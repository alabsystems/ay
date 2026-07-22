# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Categorized differential-finding INVENTORY for the AY solver, built on top of
# the pairwise comparison in `differential.py`.
#
# Runs a fixed-seed, bounded campaign per fragment and groups every finding into
# one of three HONEST categories (see differential.CAT_*):
#
#   A:sat-vs-unsat              verdict dispute, re-confirmed against z3 on the
#                               shrunk form but not adjudicated by agreement alone
#   B:wrong-model               AY says `sat` but its model FALSIFIES the formula
#                               (re-confirmed with z3 pins and/or AY's own model
#                               evaluator, depending on whether it is scalar)
#   C:partial-or-unreduced      AY says `sat` with a model we could not pin
#                               (array interp / unconstrained var / opaque value)
#                               -- EXPLICITLY NOT A BUG, counted separately.
#
# A finding is only listed in A/B once it has been re-verified against z3 (and,
# for B, against AY's own evaluator). Partial-model (C) cases are NEVER reported
# as bugs. This is the deliverable: a clean, prioritized, repro-carrying list the
# core soundness effort can act on, with the partial-model noise stripped out.

import os
from dataclasses import dataclass, field
from typing import Dict, List

from .differential import CAT_A, CAT_B, CAT_C, Finding, run_campaign
from .gen import FRAGMENTS

# Historical failures that are now hard regression pins in
# `tests/test_diff_fuzz.py`. If a future inventory finds one again, the report
# labels it as a regression instead of presenting it as a never-fixed open bug.
HISTORICAL_ARRAY_SEEDS = (341, 500, 561)
HISTORICAL_BV_MODEL_SEEDS = (5, 432, 439)

# Default per-fragment counts for an inventory campaign. `arrays` and `qf_bv`
# retain enough cases to cover their historical fixed seeds; the rest are sized
# for a thorough-but-bounded sweep. Keep this list synchronized with FRAGMENTS so
# the generated table makes the intended coverage explicit.
DEFAULT_COUNTS = {
    "qf_lia": 500,
    "qf_nia": 500,
    "qf_lra": 500,
    "qf_bv": 500,
    "qf_bv_bool": 500,
    "qf_uflia": 500,
    "arr_lia": 600,
    "arrays": 600,
    "quant_lia": 500,
    "quant_lra_isint": 500,
    "qf_fp": 500,
    "recfun": 500,
    "sequences": 500,
}

# Inventory campaigns use a tighter per-check timeout than the manual fuzzer: the
# array fragments contain a fraction of cases that neither solver dispatches in
# 2s (they SKIP either way), so a 1s bound roughly halves wall-clock while still
# exercising every decidable case and reaching all historical array seeds.
DEFAULT_TIMEOUT_MS = 1000

# Cap on the number of fully-shrunk repros captured per category per fragment.
# COUNTS stay exact; this just bounds how many detailed repros we build+shrink so
# the inventory finishes in reasonable time (distinct classes still surface, and
# duplicates would be collapsed by dedup anyway).
MAX_FINDINGS_PER_CAT = 6


@dataclass
class FragmentReport:
    fragment: str
    checked: int
    agree: int
    skip: int
    disagree: int
    model_bad: int
    model_partial: int
    findings: List[Finding] = field(default_factory=list)


@dataclass
class Inventory:
    reports: List[FragmentReport] = field(default_factory=list)
    seed_start: int = 0
    timeout_ms: int = DEFAULT_TIMEOUT_MS

    def all_findings(self) -> List[Finding]:
        out = []
        for r in self.reports:
            out.extend(r.findings)
        return out

    def by_category(self) -> Dict[str, List[Finding]]:
        out = {CAT_A: [], CAT_B: [], CAT_C: []}
        for f in self.all_findings():
            out.setdefault(f.category, []).append(f)
        return out


def _dedup_findings(findings: List[Finding]) -> List[Finding]:
    """Collapse findings that share a category + canonical SMT-LIB to ONE
    representative (the smallest seed), so the inventory lists DISTINCT classes
    rather than every seed that re-triggers the same shrunk repro."""
    by_key = {}
    for f in findings:
        key = (f.category, f.smtlib.strip())
        cur = by_key.get(key)
        if cur is None or f.seed < cur.seed:
            by_key[key] = f
    return sorted(by_key.values(), key=lambda f: (f.category, f.fragment, f.seed))


def run_inventory(fragments=None, counts=None, seed_start=0, timeout_ms=None,
                  progress=None) -> Inventory:
    """Run a categorized campaign over `fragments` (default: all) and return an
    Inventory of DISTINCT, re-confirmed findings."""
    if fragments is None:
        fragments = sorted(FRAGMENTS)
    if timeout_ms is None:
        timeout_ms = DEFAULT_TIMEOUT_MS
    counts = counts or {}
    inv = Inventory(seed_start=seed_start, timeout_ms=timeout_ms)
    for frag in fragments:
        n = counts.get(frag, DEFAULT_COUNTS.get(frag, 500))
        if progress:
            progress(f"[inventory] {frag}: running {n} cases (timeout {timeout_ms}ms)...")
        summ = run_campaign(frag, n, seed_start=seed_start, timeout_ms=timeout_ms,
                            progress=None, max_findings_per_cat=MAX_FINDINGS_PER_CAT)
        inv.reports.append(FragmentReport(
            fragment=frag, checked=summ.count, agree=summ.agree, skip=summ.skip,
            disagree=summ.disagree, model_bad=summ.model_invalid,
            model_partial=summ.model_partial,
            findings=_dedup_findings(summ.findings),
        ))
        if progress:
            progress("   " + summ.line())
    return inv


# ---------------------------------------------------------------------------
# Markdown rendering
# ---------------------------------------------------------------------------

def _matches_historical_regression(f: Finding) -> bool:
    return ((f.fragment == "arrays" and f.seed in HISTORICAL_ARRAY_SEEDS)
            or (f.fragment == "qf_bv"
                and f.seed in HISTORICAL_BV_MODEL_SEEDS))


def _z3_version() -> str:
    try:
        import z3
        return z3.get_version_string()
    except Exception:
        return "unavailable"


def render_markdown(inv: Inventory) -> str:
    cats = inv.by_category()
    lines = []
    lines.append("# AY solver -- differential fuzz inventory")
    lines.append("")
    lines.append("Generated by `python -m ayz3_fuzz --inventory` "
                 "(`ayz3_fuzz/inventory.py`). Differential cross-check: AY via the "
                 f"`ayz3` z3py-compatible binding vs real z3py {_z3_version()}.")
    lines.append("")
    lines.append(
        "This is a bounded snapshot over deterministically generated inputs: "
        f"seeds start at {inv.seed_start}, and each solver check has a "
        f"{inv.timeout_ms} ms timeout. Formulas reproduce from their "
        "`(fragment, seed)`; timeout-bound agree, skip, and partial-model "
        "counts can vary with runtime load. `unknown` and unsupported "
        "operations are skips, not agreements."
    )
    lines.append("")
    lines.append("## Categories")
    lines.append("")
    lines.append("- **A: sat-vs-unsat** -- catastrophic verdict disagreement. "
                 "Re-confirmed against z3 on the shrunk formula, including "
                 "validation of the `sat` side's model where available. A real "
                 "soundness bug. Each A "
                 "finding is also labelled by reproduction path: "
                 "**BUILDER-PATH-ONLY** (wrong only when the term is built "
                 "in-memory through the binding's C ABI; AY's own SMT-LIB parser "
                 "gets it right) vs **CORE-LEVEL** (wrong even when the "
                 "equivalent SMT-LIB is parsed -- reproduces through AY's native "
                 "CLI too).")
    lines.append("- **B: wrong-model** -- AY returns `sat` but its model "
                 "falsifies the formula. Concrete scalar models are checked by "
                 "in-memory and rendered-SMT-LIB z3 pins plus AY's own evaluator; "
                 "non-scalar models require AY to self-contradict and z3 to "
                 "confirm a valid completion. The verdict may be right but the "
                 "witness is wrong -- a soundness-adjacent bug.")
    lines.append("- **C: partial/unreduced model** -- AY returns `sat` with a "
                 "model that could not be pinned (array interpretation, "
                 "unconstrained var, or opaque/unreduced value). **NOT a bug** "
                 "-- a model-readout limitation, counted separately and never "
                 "reported as a finding.")
    lines.append("")

    # Per-fragment campaign table.
    lines.append("## Campaign coverage")
    lines.append("")
    lines.append("| fragment (seed range) | checked | agree | skip | A (disagree) | "
                 "B (bad model) | C (partial model) |")
    lines.append("|---|---:|---:|---:|---:|---:|---:|")
    for r in inv.reports:
        seed_end = inv.seed_start + r.checked - 1
        lines.append(f"| `{r.fragment}` ({inv.seed_start}..{seed_end}) | "
                     f"{r.checked} | {r.agree} | {r.skip} | "
                     f"{r.disagree} | {r.model_bad} | {r.model_partial} |")
    # Datatypes is honestly skipped (the fuzzer's generator is unimplemented).
    if "datatypes" not in [r.fragment for r in inv.reports]:
        lines.append("| `datatypes` | 0 | 0 | 0 | 0 | 0 | 0 |")
    lines.append("")
    lines.append("> `datatypes` is **skipped honestly**: ayz3 ships a "
                 "z3py-style `Datatype` builder, but the fuzzer's datatype "
                 "formula generator is not implemented yet, so the fuzzer does "
                 "not fabricate datatype coverage.")
    lines.append("")

    lines.append("## Historical regression pins")
    lines.append("")
    lines.append("The following formerly failing cases are fixed and are now "
                 "hard regression tests in `tests/test_diff_fuzz.py`:")
    lines.append("")
    lines.append("- array wrong-`unsat`: `arrays` seeds 341, 500, and 561")
    lines.append("- BV wrong-model: `qf_bv` seeds 5, 432, and 439")
    lines.append("")
    lines.append("The targeted tests independently require z3 to prove the "
                 "array formulas satisfiable and require AY's BV models to "
                 "validate through both in-memory and rendered-SMT-LIB pins.")
    lines.append("")

    # Headline counts.
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- **Category A (sat-vs-unsat soundness bugs):** "
                 f"{len(cats[CAT_A])} distinct")
    lines.append(f"- **Category B (wrong-model bugs):** {len(cats[CAT_B])} distinct")
    lines.append(f"- **Category C (partial/unreduced models, NOT bugs):** "
                 f"{sum(r.model_partial for r in inv.reports)} occurrences")
    lines.append("")

    # Findings sections.
    for cat, title in ((CAT_A, "Category A -- sat-vs-unsat disagreements"),
                       (CAT_B, "Category B -- wrong models")):
        lines.append(f"## {title}")
        lines.append("")
        items = cats[cat]
        if not items:
            lines.append("_None found in this campaign._")
            lines.append("")
            continue
        for i, f in enumerate(items, 1):
            regression = " (HISTORICAL FAILURE REGRESSED)" \
                if _matches_historical_regression(f) else ""
            lines.append(
                f"### {cat} #{i}: `{f.fragment}` seed {f.seed}{regression}"
            )
            lines.append("")
            lines.append(f"- ayz3 verdict: `{f.ay_verdict}`  |  "
                         f"z3 verdict: `{f.z3_verdict}`")
            if f.model_repr:
                lines.append(f"- model: `{f.model_repr}`")
            if f.own_eval is not None:
                lines.append(f"- AY's own `model.eval(formula)` = `{f.own_eval}`")
            lines.append(f"- re-confirmed against z3: **{f.reconfirmed}**")
            if f.note:
                lines.append(f"- confirmation: {f.note}")
            lines.append(f"- repro: `generate({f.fragment!r}, {f.seed})`")
            lines.append("")
            lines.append("```smt2")
            lines.append(f.smtlib.strip())
            lines.append("(check-sat)")
            lines.append("```")
            lines.append("")

    # Category C note (never a finding list).
    lines.append("## Category C -- partial / unreduced models (NOT bugs)")
    lines.append("")
    total_c = sum(r.model_partial for r in inv.reports)
    lines.append(f"{total_c} `sat` cases produced a model that could not be "
                 "completely pinned (e.g. an array interpretation, an "
                 "unconstrained variable, or an opaque/unreduced value). These "
                 "are model-readout limitations, **not established wrong "
                 "answers**: the verdict agrees with z3, but the model could not "
                 "be fully validated. They are counted here for completeness and "
                 "deliberately not listed as findings.")
    lines.append("")
    return "\n".join(lines)


def write_findings_md(path=None, **kwargs) -> str:
    """Run an inventory and write FINDINGS.md. Returns the path written."""
    if path is None:
        path = os.path.join(os.path.dirname(__file__), "FINDINGS.md")
    progress = kwargs.pop("progress", None)
    inv = run_inventory(progress=progress, **kwargs)
    md = render_markdown(inv)
    with open(path, "w") as fh:
        fh.write(md)
    return path, inv
