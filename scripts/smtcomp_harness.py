#!/usr/bin/env python3
# ay-script: smtcomp-restage
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""SMT-COMP 2025 restage harness (retroactive campaign).

Runs AY and the real 2025 entrant solvers on the exact 2025 benchmark
selections under competition limits, and scores with 2025 semantics
(sequential + parallel scores, error demotion, disagreement report).

Tracks: sq (SingleQuery), inc (Incremental), uc (UnsatCore),
mv (ModelValidation). Parallel track excluded (hardware; see PLAN.md).

Benchmark manifests: benchmarks/smtlib-2025/selections/<track>/<Division>.jsonl
with one JSON object per line: {relpath, logic, family, name, expected}.
relpath is relative to benchmarks/smtlib-2025/. For inc, `expected` may be a
list (or comma-joined string) of per-check-sat statuses.

Run protocol (scrambler parity): each instance is materialized as a temp copy
with every `(set-info :status ...)` line stripped so solvers never see the
answer. Only lines that exactly match the single-line form are dropped; any
paren-imbalanced oddity is copied verbatim (never corrupt an input). For the
uc track the temp additionally mirrors the 2025 scrambler's
`-gen-unsat-core true` mode: every top-level assert is renamed
`(assert (! BODY :named smtcompN))` (collision-free N from 1 after all
pre-existing normalized labels are collected; already-:named asserts are left
untouched and duplicate labels are rejected; multi-line asserts are handled by
a trivia-aware S-expression scanner), the produce option is forced true, and
`(get-unsat-core)` is appended after `(check-sat)` unless an exact top-level
zero-argument command already exists.

UnsatCore scoring (2025 semantics): a core earns reduction = #named-asserts
- |core| ONLY after validation. `validate-uc` rebuilds the reduced benchmark
(only core-named asserts kept, naming stripped, declarations intact) and runs
the division's validators (default cvc5+smtinterpol, their SQ configs): core
VALID iff #unsat > #sat among validator answers; #sat >= #unsat with #sat > 0
=> INVALIDATED (an error — demoted below every 0-error solver); all
timeout/unknown => 0 points, no error. A solver is NEVER its own validator.
Unvalidated cores (including empty `()` cores) score 0 — an empty core can
never earn full reduction. Full (all-assertion) cores are still validated:
their reduction is zero, but invalidation is a score-changing error.

Validation-row integrity (U4 review F1): every validation row records the full
sha256 of the core file it validated, and the reduced
benchmark is written to a per-(solver, instance, core-hash) path. Both the
validate-uc cache and uc scoring key on (instance, core-hash): re-running a
solver under the same tag with a different core automatically re-validates,
and a validation row whose hash no longer matches the solver's current core
is IGNORED at score time (counted + reported as stale). Legacy/unhashed rows
are never reused or scored. FRESH-TAG DISCIPLINE: for any scored run still use
a fresh --tag (or --overwrite on both run and validate-uc) so no stale rows
exist at all — the hash keying is the belt, fresh tags are the braces.

Model-validation rows likewise key on the exact model-file hash. Re-running
an MV solver under one tag overwrites its model artifact, so an instance-only
cache key could otherwise award a new model the old model's validation point
(or error). Missing/stale MV validation now blocks scoring until revalidated.

Validator health check (U4 review F2): before any validation batch, every
requested validator is run on a trivial UNSAT instance per division logic
and must answer `unsat`; otherwise the batch ABORTS loudly. A dead validator
(e.g. the macOS /usr/bin/java stub silently failing to start SMTInterpol)
must never be counted as a neutral quorum member — that would bias toward
`valid` (the remaining validator alone decides) and away from invalidation.
For SMTInterpol set JAVA_BIN to a real JRE (e.g.
.competitors/temurin21-jre/Contents/Home/bin/java — the default candidate).

For the mv track the temp mirrors the 2025 scrambler's `-gen-model-val true`
output (smtcomp/scramble_benchmarks.py): ALL complete `(set-info ...)`
commands are stripped (a balanced scan that understands |...| symbols and
"..." strings; anything odd is kept verbatim) and `(get-model)` is appended
after each `(check-sat)` (unless the file already issues one). Additionally
`(set-option :produce-models true)` is prepended (unless present) — the 2025
solver wrapper scripts enabled model production; this is the local
equivalent, same convention as uc (constructively verified accepted by the
pinned Dolmen).

Model validation (validate-mv): each recorded answer=sat run is validated
with the EXACT 2025 pipeline (smtcomp/model_validation.py check_locally at
tag smtcomp25): the pinned Dolmen (`.competitors/dolmen/dolmen`, or
$DOLMEN_BIN) is run as `dolmen --time=1h --size=40G --strict=false
--check-model=true --report-style=minimal --warn=-all <prepped-bench.smt2>`
with the solver's FULL stdout (the `sat` line + model) on stdin; the prepped
benchmark is re-materialized identically to what the solver saw. Exit-code /
stderr mapping is the 2025 parser verbatim (exit 0 = ValidationOk; exit 2 =
ModelValidatorTimeout; else stderr-suffix E:code table, incl. the
--force-smtlib2-logic=ALL retry after an exact E:forbidden-array-sort).
2025 mv scoring (smtcomp/scoring.py): a point ONLY for a Dolmen-validated
sat; ANY unsat answer or ModelUnsat (E:bad-model) is an error (the only
division-voiding outcomes); parse/partial/validator-timeout = 0 points, no
error. Errors rank a solver below every 0-error solver (demotion).

Paths: benchmarks default to <repo>/benchmarks/smtlib-2025 and results to
<repo>/evals/results/smtcomp-2025; override with $SMTCOMP_BENCH_ROOT /
$SMTCOMP_RESULTS_ROOT (worktrees carry only the selections, not the full
benchmark corpus).

Solver command lines are read from the 2025 submission JSONs
(submissions/*.json at tag smtcomp25 of github.com/SMT-COMP/smt-comp.github.io;
set SMTCOMP_SUBMISSIONS to the clone's submissions dir). argv[0] of the
submission command is replaced with the locally installed binary; remaining
args are kept (e.g. yices2 SQ on QF_BV runs `--delegate=kissat`). CAVEAT:
cvc5's and SMTInterpol's 2025 commands are wrapper scripts that live inside
their Zenodo archives, not in the JSON — locally we run the plain binary/jar
and record the deviation. A frozen copy of the extracted commands is embedded
as a fallback so the harness works without the clone.

CPU-time measurement: the child is reaped with os.wait4, so cpu_sec =
ru_utime+ru_stime of the direct child INCLUDING any descendants the child
itself reaped. LIMITATION: descendants that are still alive when we SIGKILL
the process group (or that the child never waited on) are NOT counted, and
macOS has no /usr/bin/time -v or cgroup accounting to recover them — for
scored runs prefer solvers that are a single process (all registry solvers
are; the JVM is one process). Wall time is always trustworthy.

Timeout: harness-enforced. At timeout+5s grace the whole process group gets
SIGKILL. Sequential/parallel scoring later re-applies the virtual limit to
cpu/wall respectively, so a solver that answered at 1201s is still recorded
faithfully here and zeroed at score time.

Memory: run, UnsatCore-validator, and Dolmen children all use the shared
RAM-aware job plan plus an RSS-watchdog per-child envelope. The run and
validator envelopes persist requested/admitted jobs, per-child memory,
NBCORE, headroom, and the exact process-group watchdog policy. `NBCORE` is set
for every child and AY additionally receives `--memory`. Resume caches bind
the full envelope, timeout, argv/submission command, binary hashes, source and
materialized hashes, and transform version; validation caches additionally
bind artifacts and validator binary/configuration. Scoring refuses mixed or
incomplete conditions.

Usage:
  python3 scripts/smtcomp_harness.py registry
  python3 scripts/smtcomp_harness.py run --track sq --division QF_Datatypes \
      --solvers ay,cvc5,smtinterpol --timeout 1200 --jobs 2 --tag full1200
  python3 scripts/smtcomp_harness.py run --track sq --division QF_Datatypes \
      --solvers ay,z3 --timeout 10 --tag probe --limit 5 --dry-run
  python3 scripts/smtcomp_harness.py score --track sq --division QF_Datatypes \
      --tag full1200 --timeout-virtual 1200
  python3 scripts/smtcomp_harness.py validate-uc --division QF_Datatypes \
      --tag full1200 --validators cvc5,smtinterpol --timeout 1200 --jobs 2
  python3 scripts/smtcomp_harness.py score --track uc --division QF_Datatypes \
      --tag full1200 --timeout-virtual 1200
  python3 scripts/smtcomp_harness.py run --track mv --division QF_Datatypes \
      --solvers ay --timeout 1200 --jobs 2 --tag mvfull
  python3 scripts/smtcomp_harness.py validate-mv --division QF_Datatypes \
      --tag mvfull --jobs 2
  python3 scripts/smtcomp_harness.py score --track mv --division QF_Datatypes \
      --tag mvfull --timeout-virtual 1200

Env overrides: SMTCOMP_BENCH_ROOT points the benchmark tree (read-only; e.g.
a sibling checkout that has non-incremental/ populated) somewhere else while
results stay under THIS repo's evals/. SMTCOMP_EXTRA_SOLVERS="name=/bin;..."
registers extra plain `BIN FILE` solvers (testing hook).

Results: evals/results/smtcomp-2025/<track>/<Division>/<tag>/<solver>.jsonl
(one JSON object per instance; resumable — existing (solver, instance) pairs
under the exact current run identity are skipped unless --overwrite). mv
stdout (models) and uc cores are captured to files under the same tag dir.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _oom_guard import (  # noqa: E402
    plan_solver_resources,
    rss_watchdog,
    warn_concurrent_build,
)

REPO = Path(__file__).resolve().parent.parent
# Benchmark FILES may live in another checkout (they are gitignored and big);
# SMTCOMP_BENCH_ROOT redirects reads there. Treat that tree as READ-ONLY —
# results/cores/reduced files always live under THIS repo's evals/.
BENCH_ROOT = Path(os.environ.get("SMTCOMP_BENCH_ROOT",
                                 str(REPO / "benchmarks/smtlib-2025")))
SELECTIONS = BENCH_ROOT / "selections"
RESULTS_ROOT = Path(os.environ.get("SMTCOMP_RESULTS_ROOT",
                                   str(REPO / "evals/results/smtcomp-2025")))
COMPETITORS = REPO / ".competitors"

TRACKS = {  # cli name -> 2025 submission-JSON track label
    "sq": "SingleQuery",
    "inc": "Incremental",
    "uc": "UnsatCore",
    "mv": "ModelValidation",
}

GRACE_SEC = 5  # wall grace past --timeout before the process group is killed
STDOUT_CAP = 64 * 1024 * 1024  # in-memory stdout head kept for parsing
STDERR_TAIL_CAP = 64 * 1024  # rolling stderr tail kept in memory
ANSWER_TOKENS = ("sat", "unsat", "unknown")

# Persisted provenance schemas. Bump a materialization version whenever the
# solver-visible bytes can change even if the source benchmark does not.
RESOURCE_ENVELOPE_VERSION = 1
RUN_IDENTITY_VERSION = 1
VALIDATION_IDENTITY_VERSION = 1
MATERIALIZATION_VERSION = {
    "sq": "status-strip-v1",
    "inc": "status-strip-v1",
    "uc": "status-strip+uc-structural-v2",
    "mv": "mv-structural-v2",
}
WATCHDOG_POLL_S = 0.02  # scripts/_oom_guard.py POLL_DEFAULT, recorded exactly

# Default location of the recon clone of smt-comp.github.io @ smtcomp25
# (re-derivable: git clone --filter=blob:none -b smtcomp25 <repo>).
# Override with SMTCOMP_SUBMISSIONS.
_DEFAULT_SUBMISSIONS = REPO / ".competitors/smtcomp-io/submissions"

# Frozen copy of the 2025 command lines (extracted from submissions/*.json at
# tag smtcomp25 on 2026-07-08) used when the clone is unavailable. Keys are
# "<track>" or "<track>:<LOGIC>" for logic-specific participations.
FALLBACK_2025_COMMANDS: dict[str, dict[str, list[str]]] = {
    "cvc5": {
        "sq": ["bin/starexec_run_sq"],  # wrapper script inside Zenodo archive
        "inc": ["bin/smtcomp_run_incremental"],
        "mv": ["bin/starexec_run_mv"],
        "uc": ["bin/starexec_run_uc"],
    },
    "smtinterpol": {t: ["smtinterpol"] for t in TRACKS},  # wrapper script
    "yices2": {
        "sq": ["./yices_smt2"],
        "sq:QF_BV": ["./yices_smt2", "--delegate=kissat"],
        "sq:QF_NIA": ["./yices_smt2", "--mcsat-l2o"],
        "inc": ["./yices_smt2", "--incremental"],
        "uc": ["./yices_smt2"],
        "mv": ["./yices_smt2"],
        "mv:QF_NIA": ["./yices_smt2", "--mcsat-l2o"],
    },
    "opensmt": {t: ["./opensmt"] for t in TRACKS},
    "bitwuzla": {t: ["bin/bitwuzla"] for t in TRACKS},
    "z3alpha": {"sq": ["./z3alpha.py"]},
}


# ---------------------------------------------------------------------------
# Manifests


@dataclass
class Instance:
    relpath: str
    logic: str
    family: str
    name: str
    expected: object  # "sat"|"unsat"|"unknown"|None; list/str of tokens for inc


def load_manifest(track: str, division: str) -> list[Instance]:
    # Selections may live under the short cli name (sq/) or the official
    # 2025 track label (SingleQuery/) — accept both.
    candidates = [SELECTIONS / track / f"{division}.jsonl",
                  SELECTIONS / TRACKS[track] / f"{division}.jsonl"]
    path = next((p for p in candidates if p.is_file()), None)
    if path is None:
        raise SystemExit(f"no manifest: tried {' and '.join(map(str, candidates))}")
    out: list[Instance] = []
    missing = 0
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        rec = json.loads(line)
        inst = Instance(
            relpath=rec["relpath"],
            logic=rec.get("logic", ""),
            family=rec.get("family", ""),
            name=rec.get("name", ""),
            expected=rec.get("expected"),
        )
        if not (BENCH_ROOT / inst.relpath).is_file():
            missing += 1
            continue
        out.append(inst)
    if missing:
        print(f"[manifest] {track}/{division}: {missing} listed files missing on disk",
              file=sys.stderr)
    return out


def stratified_sample(tasks: list[Instance], n: int, seed: int) -> list[Instance]:
    """Deterministic stratified sample by benchmark family."""
    import random

    if n >= len(tasks):
        return tasks
    by_family: dict[str, list[Instance]] = {}
    for t in sorted(tasks, key=lambda t: t.relpath):
        by_family.setdefault(t.family or t.relpath.split("/")[0], []).append(t)
    rng = random.Random(seed)
    picked: list[Instance] = []
    total = len(tasks)
    for _fam, members in sorted(by_family.items()):
        k = max(1, round(n * len(members) / total))
        picked.extend(rng.sample(members, min(k, len(members))))
    rng.shuffle(picked)
    return sorted(picked[:n], key=lambda t: t.relpath)


# ---------------------------------------------------------------------------
# Benchmark materialization (scrambler parity)

# Exact single-line form only. SMT-LIB practice never splits set-info across
# lines; if a paren-imbalanced or multi-line variant ever appears it will NOT
# match and the line is copied verbatim — we never corrupt an input.
_STATUS_LINE = re.compile(rb"^\s*\(\s*set-info\s+:status\s+(?:sat|unsat|unknown)\s*\)\s*$")


def strip_status(data: bytes) -> bytes:
    lines = data.splitlines(keepends=True)
    return b"".join(l for l in lines if not _STATUS_LINE.match(l.rstrip(b"\r\n")))


# --- trivia-aware S-expression scanning (uc assert naming + core validation).
# Handles comments (; to EOL), string literals ("..." with "" escapes, SMT-LIB
# 2.6: backslash is NOT an escape) and quoted symbols (|...|, no escapes).
# blocksworld asserts span multiple lines, so nothing here is line-based.

_INTERESTING = re.compile(rb'[();"|]')
_TOKEN = re.compile(rb'[^\s()";|]+')


def _skip_string(data: bytes, i: int) -> int:
    """data[i] == '\"'; index just past the closing quote ('""' escapes)."""
    n = len(data)
    i += 1
    while i <= n:
        j = data.find(b'"', i)
        if j < 0:
            return n
        if data[j + 1 : j + 2] == b'"':
            i = j + 2
            continue
        return j + 1
    return n


def _skip_quoted(data: bytes, i: int) -> int:
    j = data.find(b"|", i + 1)
    return len(data) if j < 0 else j + 1


def _skip_comment(data: bytes, i: int) -> int:
    j = data.find(b"\n", i)
    return len(data) if j < 0 else j + 1


def _scan_toplevel(data: bytes) -> list[tuple[int, int]]:
    """Byte spans of top-level parenthesized forms (commands)."""
    spans: list[tuple[int, int]] = []
    depth = 0
    start = 0
    i = 0
    while True:
        m = _INTERESTING.search(data, i)
        if m is None:
            break
        j = m.start()
        c = data[j : j + 1]
        if c == b"(":
            if depth == 0:
                start = j
            depth += 1
            i = j + 1
        elif c == b")":
            if depth > 0:
                depth -= 1
                if depth == 0:
                    spans.append((start, j + 1))
            i = j + 1  # stray ')' tolerated — never corrupt, keep scanning
        elif c == b";":
            i = _skip_comment(data, j)
        elif c == b'"':
            i = _skip_string(data, j)
        else:  # b"|"
            i = _skip_quoted(data, j)
    return spans


def _skip_trivia(data: bytes, i: int, e: int) -> int:
    while i < e:
        c = data[i : i + 1]
        if c in (b" ", b"\t", b"\r", b"\n"):
            i += 1
        elif c == b";":
            i = min(_skip_comment(data, i), e)
        else:
            break
    return i


def _term_end(data: bytes, i: int, e: int) -> int:
    """End (exclusive) of the single term starting at data[i] (i < e)."""
    c = data[i : i + 1]
    if c == b"(":
        depth = 0
        j = i
        while j < e:
            m = _INTERESTING.search(data, j, e)
            if m is None:
                return e
            k = m.start()
            ck = data[k : k + 1]
            if ck == b"(":
                depth += 1
                j = k + 1
            elif ck == b")":
                depth -= 1
                j = k + 1
                if depth == 0:
                    return j
            elif ck == b";":
                j = min(_skip_comment(data, k), e)
            elif ck == b'"':
                j = min(_skip_string(data, k), e)
            else:
                j = min(_skip_quoted(data, k), e)
        return e
    if c == b'"':
        return min(_skip_string(data, i), e)
    if c == b"|":
        return min(_skip_quoted(data, i), e)
    m = _TOKEN.match(data, i, e)
    return m.end() if m else i + 1


def _form_head(data: bytes, s: int, e: int) -> tuple[bytes, int]:
    """(head token, index just past it) of the form data[s:e]."""
    i = _skip_trivia(data, s + 1, e)
    m = _TOKEN.match(data, i, e)
    return (m.group(0), m.end()) if m else (b"", i)


def _form_terms(data: bytes, s: int, e: int) -> tuple[bytes, list[tuple[int, int]]]:
    """Return a command/term head and its direct argument spans.

    This is deliberately structural: words in comments, strings, quoted
    symbols, or nested terms are never mistaken for top-level command
    arguments.
    """
    head, i = _form_head(data, s, e)
    args: list[tuple[int, int]] = []
    limit = max(s, e - 1)  # exclude the form's closing paren
    while True:
        i = _skip_trivia(data, i, limit)
        if i >= limit:
            break
        end = _term_end(data, i, limit)
        if end <= i:
            break
        args.append((i, end))
        i = end
    return head, args


def _atomic_token(data: bytes, span: tuple[int, int]) -> bytes | None:
    """Return an unquoted atomic token, or None for compound/string terms."""
    s, e = span
    if s >= e or data[s:s + 1] in (b"(", b'"', b"|"):
        return None
    m = _TOKEN.fullmatch(data, s, e)
    return m.group(0) if m else None


def _symbol_text(data: bytes, span: tuple[int, int]) -> str | None:
    """Decode a simple or quoted SMT-LIB symbol and normalize its identity."""
    s, e = span
    raw = data[s:e]
    if raw.startswith(b"|") and raw.endswith(b"|") and len(raw) >= 2:
        return raw[1:-1].decode("utf-8", "replace")
    if _atomic_token(data, span) is None:
        return None
    return raw.decode("utf-8", "replace")


def _is_exact_command(data: bytes, s: int, e: int, head: bytes,
                      argc: int = 0) -> bool:
    actual, args = _form_terms(data, s, e)
    return actual == head and len(args) == argc


def _option_bool(data: bytes, s: int, e: int,
                 option: bytes) -> bool | None:
    """Exact `(set-option OPTION true|false)` value, else None."""
    head, args = _form_terms(data, s, e)
    if head != b"set-option" or len(args) != 2:
        return None
    if _atomic_token(data, args[0]) != option:
        return None
    value = _atomic_token(data, args[1])
    if value == b"true":
        return True
    if value == b"false":
        return False
    return None


def _annotation_name(data: bytes, s: int, e: int) -> str | None:
    """Return the exact top-level :named value of an annotation, if any."""
    head, args = _form_terms(data, s, e)
    if head != b"!" or not args:
        return None
    names: list[str] = []
    for i, arg in enumerate(args[1:], 1):
        if _atomic_token(data, arg) != b":named":
            continue
        if i + 1 >= len(args):
            continue
        name = _symbol_text(data, args[i + 1])
        if name is not None:
            names.append(name)
    if len(names) > 1:
        raise ValueError("assert annotation contains more than one :named attribute")
    return names[0] if names else None


@dataclass
class UcAssert:
    name: str  # smtcompN we assigned, or the pre-existing :named name ("" = unnamed)
    form: tuple[int, int]  # span of the whole (assert ...) form
    body: tuple[int, int] | None  # assert body span; None => emit form verbatim
    prenamed: bool = False


@dataclass
class UcScan:
    forms: list[tuple[int, int]]
    heads: list[bytes]
    asserts: dict[int, UcAssert]  # keyed by form start offset
    n_named: int
    has_option: bool
    has_guc: bool
    option_forms: set[int]


def uc_scan(data: bytes) -> UcScan:
    """One deterministic scan shared by prep (naming) and validation
    (reduced-benchmark reconstruction) — the two MUST agree on names."""
    forms = _scan_toplevel(data)
    heads: list[bytes] = []
    asserts: dict[int, UcAssert] = {}
    pending: list[tuple[int, int, int, str | None]] = []
    existing: dict[str, int] = {}
    option_forms: set[int] = set()
    for s, e in forms:
        head, hend = _form_head(data, s, e)
        heads.append(head)
        if _option_bool(data, s, e, b":produce-unsat-cores") is not None:
            option_forms.add(s)
        if head != b"assert":
            continue
        b0 = _skip_trivia(data, hend, e - 1)
        if b0 >= e - 1:  # (assert) — malformed; keep verbatim, unnameable
            asserts[s] = UcAssert("", (s, e), None)
            continue
        # Pre-named assert = body is a (! ... :named X ...) annotation. Never
        # occurs in the 2025 QF_Datatypes selections (probe-verified); kept
        # verbatim under its own name so we never double-name.
        if data[b0 : b0 + 1] == b"(":
            b1 = _term_end(data, b0, e - 1)
            name = _annotation_name(data, b0, b1)
            if name is not None:
                normalized = name
                if normalized in existing:
                    raise ValueError(
                        f"duplicate normalized :named assertion label {normalized!r}"
                    )
                existing[normalized] = s
                pending.append((s, e, b0, normalized))
                continue
        b1 = _term_end(data, b0, e - 1)
        pending.append((s, e, b0, None))

    # Allocate only after pre-collecting all existing labels, so a benchmark
    # that already owns `smtcomp1` can never receive a colliding generated name.
    counter = 1
    used = set(existing)
    for s, e, b0, prenamed in pending:
        if prenamed is not None:
            asserts[s] = UcAssert(prenamed, (s, e), None, prenamed=True)
            continue
        while f"smtcomp{counter}" in used:
            counter += 1
        name = f"smtcomp{counter}"
        counter += 1
        used.add(name)
        b1 = _term_end(data, b0, e - 1)
        asserts[s] = UcAssert(name, (s, e), (b0, b1))
    n_named = len({a.name for a in asserts.values() if a.name})
    return UcScan(forms, heads, asserts, n_named,
                  has_option=bool(option_forms),
                  has_guc=any(_is_exact_command(data, s, e,
                                                b"get-unsat-core")
                              for s, e in forms),
                  option_forms=option_forms)


def prep_uc(data: bytes) -> tuple[bytes, int]:
    """Scrambler-parity UnsatCore prep on status-stripped benchmark bytes.

    Names every top-level assert `(assert (! BODY :named smtcompN))` using the
    first collision-free N after collecting existing labels (matching the
    2025 scrambler on ordinary unlabeled inputs; already-:named asserts are
    untouched); forces the produce option true and appends get-unsat-core
    after each exact check-sat unless an exact get command is present.
    Returns (prepped_bytes, number_of_named_asserts)."""
    scan = uc_scan(data)
    out: list[bytes] = []
    if not scan.has_option:
        out.append(b"(set-option :produce-unsat-cores true)\n")
    pos = 0
    for (s, e), head in zip(scan.forms, scan.heads):
        out.append(data[pos:s])  # inter-form trivia verbatim
        a = scan.asserts.get(s)
        if s in scan.option_forms:
            # A pre-existing `false` must not override a prepended `true`.
            # Canonicalizing every exact occurrence also handles true/false
            # sequences without relying on command-substring heuristics.
            out.append(b"(set-option :produce-unsat-cores true)")
        elif a is not None and a.body is not None:
            b0, b1 = a.body
            out.append(b"(assert (! ")
            out.append(data[b0:b1])
            out.append(b" :named " + a.name.encode("utf-8") + b"))")
        else:
            out.append(data[s:e])
        if (_is_exact_command(data, s, e, b"check-sat")
                and not scan.has_guc):
            out.append(b"\n(get-unsat-core)")
        pos = e
    out.append(data[pos:])
    return b"".join(out), scan.n_named


def build_reduced(data: bytes, keep: set[str]) -> tuple[bytes, list[str], int]:
    """Reduced benchmark for core validation (2025 scrambler -core parity):
    keep ONLY the core-named asserts (naming stripped), every non-assert
    command verbatim (declarations/set-logic/check-sat), drop get-unsat-core.
    `data` must be the status-stripped ORIGINAL bytes so names line up with
    prep_uc. Returns (reduced_bytes, matched_names, n_named_asserts)."""
    scan = uc_scan(data)
    out: list[bytes] = []
    matched: list[str] = []
    matched_set: set[str] = set()
    for (s, e), head in zip(scan.forms, scan.heads):
        if _is_exact_command(data, s, e, b"get-unsat-core"):
            continue
        a = scan.asserts.get(s)
        if a is None:
            out.append(data[s:e] + b"\n")
            continue
        if a.name and a.name in keep:
            if a.name not in matched_set:
                matched.append(a.name)
                matched_set.add(a.name)
            if a.body is not None:
                b0, b1 = a.body
                out.append(b"(assert " + data[b0:b1] + b")\n")
            else:  # pre-named: verbatim (a :named annotation is semantically inert)
                out.append(data[s:e] + b"\n")
    return b"".join(out), matched, scan.n_named


def core_names(core_text: str) -> list[str]:
    """Distinct assertion names in a captured core S-expression, in order."""
    toks: list[str] = []
    i, n = 0, len(core_text)
    while i < n:
        c = core_text[i]
        if c in "() \t\r\n":
            i += 1
        elif c == "|":
            j = core_text.find("|", i + 1)
            j = n if j < 0 else j
            toks.append(core_text[i + 1 : j])
            i = j + 1
        elif c == ";":
            j = core_text.find("\n", i)
            i = n if j < 0 else j + 1
        else:
            j = i
            while j < n and core_text[j] not in "()| \t\r\n;":
                j += 1
            toks.append(core_text[i:j])
            i = j
    seen: set[str] = set()
    out: list[str] = []
    for t in toks:
        if t and t not in seen:
            seen.add(t)
            out.append(t)
    return out


def strip_set_infos(data: bytes) -> bytes:
    """Drop every complete (set-info ...) command, including multi-line
    |...|-quoted bodies (scrambler drops all set-infos in -gen-model-val
    output). Anything that does not scan as a complete form is kept verbatim
    — never corrupt an input."""
    forms = _scan_toplevel(data)
    out: list[bytes] = []
    pos = 0
    for s, e in forms:
        out.append(data[pos:s])
        head, _ = _form_head(data, s, e)
        if head != b"set-info":
            out.append(data[s:e])
        pos = e
    out.append(data[pos:])
    return b"".join(out)


def prep_mv(data: bytes) -> bytes:
    """Scrambler `-gen-model-val true` parity: strip ALL set-infos, append
    (get-model) after each (check-sat) (unless the file already issues one).
    Locally also prepend (set-option :produce-models true) — the 2025 solver
    wrappers enabled model production; this is the local equivalent (uc
    convention; verified accepted by the pinned Dolmen)."""
    stripped = strip_set_infos(data)
    forms = _scan_toplevel(stripped)
    option_forms = {
        s for s, e in forms
        if _option_bool(stripped, s, e, b":produce-models") is not None
    }
    have_gm = any(_is_exact_command(stripped, s, e, b"get-model")
                  for s, e in forms)
    out: list[bytes] = []
    if not option_forms:
        out.append(b"(set-option :produce-models true)\n")
    pos = 0
    for s, e in forms:
        out.append(stripped[pos:s])
        if s in option_forms:
            out.append(b"(set-option :produce-models true)")
        else:
            out.append(stripped[s:e])
        if (_is_exact_command(stripped, s, e, b"check-sat")
                and not have_gm):
            out.append(b"\n(get-model)")
        pos = e
    out.append(stripped[pos:])
    return b"".join(out)


def prepare_input(data: bytes, track: str) -> tuple[bytes, int | None]:
    """Return exact solver-visible bytes and the UC assertion baseline."""
    n_named: int | None = None
    if track == "mv":
        return prep_mv(data), None
    prepped = strip_status(data)
    if track == "uc":
        prepped, n_named = prep_uc(prepped)
    return prepped, n_named


def materialize(src: Path, track: str, tmpdir: str) -> tuple[str, bytes, int | None]:
    """Write the solver-visible temp .smt2.

    Returns (temp_path, original_bytes, n_named_asserts_or_None)."""
    data = src.read_bytes()
    prepped, n_named = prepare_input(data, track)
    fd, tmp = tempfile.mkstemp(suffix=".smt2", prefix="smtcomp-", dir=tmpdir)
    with os.fdopen(fd, "wb") as fh:
        fh.write(prepped)
    return tmp, data, n_named


# ---------------------------------------------------------------------------
# Solver registry


@dataclass
class Solver:
    name: str
    binary: Path | None  # resolved local executable (or jar for smtinterpol)
    kind: str  # "ay" | "z3" | "native" | "jar"
    submission: str | None = None  # submissions/<name>.json driving the args
    java: Path | None = None
    note: str = ""

    @property
    def available(self) -> bool:
        if self.binary is None or not self.binary.is_file():
            return False
        if self.kind == "jar":
            return self.java is not None
        return True


def _find(env: str, *candidates: object) -> Path | None:
    v = os.environ.get(env)
    if v:
        return Path(v)
    for c in candidates:
        if isinstance(c, Path):
            if c.is_file():
                return c
        else:  # name to look up on PATH
            w = shutil.which(str(c))
            if w:
                return Path(w)
    return None


def build_registry() -> dict[str, Solver]:
    # Prefer the vendored temurin JRE over PATH lookup: on macOS
    # /usr/bin/java is a stub that "runs" and exits answerless when no JRE
    # is installed, silently killing every SMTInterpol validation (U4 review
    # F2 — the validate-uc health check catches whatever slips through).
    java = _find("JAVA_BIN",
                 COMPETITORS / "temurin21-jre/Contents/Home/bin/java",
                 COMPETITORS / "temurin21-jre/bin/java",
                 "java")
    registry = {
        "ay": Solver("ay", _find("AY_BIN", REPO / "target/release/ay"), "ay"),
        "z3": Solver("z3", _find("Z3_BIN", COMPETITORS / "z3", "z3",
                                 Path("/opt/homebrew/bin/z3")),
                     "z3", note="reference oracle, plain `z3 FILE`"),
        "cvc5": Solver("cvc5", _find("CVC5_BIN", COMPETITORS / "cvc5", "cvc5"),
                       "native", submission="cvc5",
                       note="2025 command is a starexec wrapper script inside the "
                            "Zenodo archive; running the plain binary locally"),
        "smtinterpol": Solver(
            "smtinterpol",
            _find("SMTINTERPOL_JAR", COMPETITORS / "smtinterpol/smtinterpol.jar"),
            "jar", submission="smtinterpol", java=java,
            note="2025 command `smtinterpol` is a java wrapper script; "
                 "running `java -jar` locally"),
        "yices2": Solver("yices2",
                         _find("YICES2_BIN", COMPETITORS / "yices_smt2",
                               "yices-smt2", "yices_smt2"),
                         "native", submission="yices2"),
        "opensmt": Solver("opensmt",
                          _find("OPENSMT_BIN", COMPETITORS / "opensmt", "opensmt"),
                          "native", submission="opensmt"),
        "bitwuzla": Solver("bitwuzla",
                           _find("BITWUZLA_BIN", COMPETITORS / "bitwuzla", "bitwuzla"),
                           "native", submission="bitwuzla"),
        "z3alpha": Solver("z3alpha",
                          _find("Z3ALPHA_BIN", COMPETITORS / "z3alpha/z3alpha.py"),
                          "native", submission="z3alpha"),
    }
    # Testing hook: SMTCOMP_EXTRA_SOLVERS="name=/path/to/bin;..." registers
    # extra solvers run as plain `BIN FILE` (used by the uc smoke tests to
    # inject a mock core producer; never part of scored claims).
    for spec in filter(None, (s.strip() for s in
                              os.environ.get("SMTCOMP_EXTRA_SOLVERS", "").split(";"))):
        name, _, path = spec.partition("=")
        if name and path:
            registry[name] = Solver(name, Path(path), "plain",
                                    note="extra solver from SMTCOMP_EXTRA_SOLVERS")
    return registry


def submissions_dir() -> Path | None:
    v = os.environ.get("SMTCOMP_SUBMISSIONS")
    for cand in ([Path(v)] if v else []) + [_DEFAULT_SUBMISSIONS]:
        if cand.is_dir():
            return cand
    return None


def extract_2025_command(sub_name: str, track: str, logic: str) -> list[str] | None:
    """Exact 2025 command for (submission, track, logic).

    Prefers a live parse of submissions/<sub_name>.json (participations may
    override the top-level command per track, and carry `logics` as either a
    regex string or an explicit logic list — the most specific match wins);
    falls back to the frozen table."""
    sdir = submissions_dir()
    if sdir is not None and (sdir / f"{sub_name}.json").is_file():
        sub = json.loads((sdir / f"{sub_name}.json").read_text())
        label = TRACKS[track]
        best: tuple[int, list[str]] | None = None  # (specificity, command)
        for p in sub.get("participations", []):
            if label not in p.get("tracks", []):
                continue
            logics = p.get("logics", ".*")
            if isinstance(logics, str):
                if logic and not re.fullmatch(logics, logic):
                    continue
                spec = 0 if logics == ".*" else 1
            else:
                if logic not in logics:
                    continue
                spec = 10_000 - len(logics)  # smaller explicit list = more specific
            cmd = p.get("command") or sub.get("command")
            if cmd and (best is None or spec > best[0]):
                best = (spec, cmd)
        # No matching participation => did not enter this track/logic in 2025.
        return list(best[1]) if best else None
    table = FALLBACK_2025_COMMANDS.get(sub_name, {})
    return list(table.get(f"{track}:{logic}") or table.get(track) or []) or None


@dataclass
class Invocation:
    argv: list[str]
    stdin_path: str | None = None  # feed this file on stdin instead of argv
    smtcomp_command: list[str] | None = None  # the exact 2025 command recorded


def canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True)


def identity_key(value: object) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


def make_resource_envelope(requested_jobs: int, plan) -> dict:
    """Canonical, persisted description of planned and enforced resources."""
    memlimit_mb = int(plan.memlimit_mb or 0)
    return {
        "version": RESOURCE_ENVELOPE_VERSION,
        "requested_jobs": int(requested_jobs),
        "admitted_jobs": int(plan.jobs),
        "memlimit_mb": memlimit_mb,
        "nbcore": int(plan.nbcore),
        "headroom_mb": int(plan.headroom_mb),
        "watchdog": {
            "implementation": "scripts/_oom_guard.py:rss_watchdog",
            "scope": "process-group-rss",
            "limit_mb": memlimit_mb,
            "grace_mb": 0,
            "poll_s": WATCHDOG_POLL_S,
            "measurement_failure": "fail-closed-after-5-samples",
            "kill_signal": "SIGKILL",
            "enabled": memlimit_mb > 0,
        },
    }


_ENVELOPE_KEYS = {
    "version", "requested_jobs", "admitted_jobs", "memlimit_mb", "nbcore",
    "headroom_mb", "watchdog",
}
_WATCHDOG_KEYS = {
    "implementation", "scope", "limit_mb", "grace_mb", "poll_s",
    "measurement_failure", "kill_signal", "enabled",
}


def valid_resource_envelope(value: object) -> bool:
    if not isinstance(value, dict) or set(value) != _ENVELOPE_KEYS:
        return False
    watchdog = value.get("watchdog")
    if not isinstance(watchdog, dict) or set(watchdog) != _WATCHDOG_KEYS:
        return False
    integer_fields = (
        "version", "requested_jobs", "admitted_jobs", "memlimit_mb", "nbcore",
        "headroom_mb",
    )
    if any(type(value.get(field)) is not int for field in integer_fields):
        return False
    if type(watchdog.get("limit_mb")) is not int:
        return False
    if type(watchdog.get("grace_mb")) is not int:
        return False
    if type(watchdog.get("enabled")) is not bool:
        return False
    if type(watchdog.get("poll_s")) not in (int, float):
        return False
    try:
        return (
            int(value["version"]) == RESOURCE_ENVELOPE_VERSION
            and int(value["requested_jobs"]) > 0
            and int(value["admitted_jobs"]) > 0
            and int(value["memlimit_mb"]) >= 0
            and int(value["nbcore"]) > 0
            and int(value["headroom_mb"]) >= 0
            and watchdog["implementation"]
                == "scripts/_oom_guard.py:rss_watchdog"
            and watchdog["scope"] == "process-group-rss"
            and int(watchdog["limit_mb"]) == int(value["memlimit_mb"])
            and int(watchdog["grace_mb"]) == 0
            and float(watchdog["poll_s"]) == WATCHDOG_POLL_S
            and watchdog["measurement_failure"]
                == "fail-closed-after-5-samples"
            and watchdog["kill_signal"] == "SIGKILL"
            and bool(watchdog["enabled"]) == (int(value["memlimit_mb"]) > 0)
        )
    except (KeyError, TypeError, ValueError):
        return False


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def path_identity(path: Path | None) -> dict | None:
    if path is None:
        return None
    resolved = path.resolve()
    if not resolved.is_file():
        return {"path": str(resolved), "sha256": None, "size": None}
    stat = resolved.stat()
    return {
        "path": str(resolved),
        "sha256": file_sha256(resolved),
        "size": stat.st_size,
    }


def solver_identity(sol: Solver) -> dict:
    return {
        "name": sol.name,
        "kind": sol.kind,
        "binary": path_identity(sol.binary),
        "java": path_identity(sol.java) if sol.kind == "jar" else None,
        "submission": sol.submission,
    }


def invocation_identity(inv: Invocation, input_path: str) -> dict:
    def normalize(value: str | None) -> str | None:
        return "{INPUT}" if value == input_path else value

    return {
        "argv": [normalize(arg) for arg in inv.argv],
        "stdin": normalize(inv.stdin_path),
        "smtcomp_command": inv.smtcomp_command,
    }


def build_invocation(sol: Solver, track: str, logic: str, tmp: str,
                     resource_envelope: dict | None = None,
                     timeout_s: int = 0) -> Invocation | None:
    memlimit_mb = int(resource_envelope.get("memlimit_mb", 0)) \
        if resource_envelope else 0
    if sol.kind == "ay":
        memory = ["--memory", str(memlimit_mb)] if memlimit_mb > 0 else []
        # Without an explicit -T, AY self-caps every check-sat at the 300 s
        # DEFAULT_SAFETY_DEADLINE (check_sat.rs) — a harness budget >300 s
        # silently shrinks to 300 s effective. Leave ~5 s for output flush.
        timeout = [f"-T:{max(timeout_s - 5, 1)}"] if timeout_s > 0 else []
        if track == "inc":
            # 6d0d0823 remapped -in from --stdin to --incremental; passing
            # both made clap exit 2 (duplicate) — every post-07-13 harness
            # inc run of AY scored 0. --incremental alone reads stdin here.
            return Invocation([str(sol.binary), "--z3-mode", *memory,
                               *timeout, "--incremental"],
                              stdin_path=tmp)
        return Invocation([str(sol.binary), "--z3-mode", *memory, *timeout,
                           tmp])
    if sol.kind in ("z3", "plain"):
        return Invocation([str(sol.binary), tmp])
    cmd = extract_2025_command(sol.submission or sol.name, track, logic)
    if cmd is None:
        return None  # did not participate in this track in 2025
    extra = cmd[1:]  # argv[0] is the in-archive path; swap in the local binary
    if sol.kind == "jar":
        return Invocation([str(sol.java), "-jar", str(sol.binary), *extra, tmp],
                          smtcomp_command=cmd)
    return Invocation([str(sol.binary), *extra, tmp], smtcomp_command=cmd)


def make_run_identity(sol: Solver, inst: Instance, track: str, timeout_s: int,
                      resource_envelope: dict,
                      known_solver_identity: dict | None = None,
                      source_bytes: bytes | None = None,
                      known_input_identity: dict | None = None) -> dict:
    """Conditions whose exact equality is required for a run cache hit."""
    if not valid_resource_envelope(resource_envelope):
        raise ValueError("invalid resource envelope")
    if known_input_identity is None:
        data = (BENCH_ROOT / inst.relpath).read_bytes() \
            if source_bytes is None else source_bytes
        prepped, _ = prepare_input(data, track)
        input_identity = {
            "source_sha256": hashlib.sha256(data).hexdigest(),
            "materialized_sha256": hashlib.sha256(prepped).hexdigest(),
            "materialization_version": MATERIALIZATION_VERSION[track],
        }
    else:
        input_identity = known_input_identity
    placeholder = "{INPUT}"
    inv = build_invocation(sol, track, inst.logic, placeholder,
                           resource_envelope, timeout_s=timeout_s)
    if inv is None:
        raise ValueError(
            f"{sol.name} has no {track} invocation for logic {inst.logic}"
        )
    return {
        "version": RUN_IDENTITY_VERSION,
        "instance": inst.relpath,
        "track": track,
        "logic": inst.logic,
        "expected": inst.expected,
        "timeout_s": int(timeout_s),
        "resource_envelope": resource_envelope,
        "solver": known_solver_identity or solver_identity(sol),
        "invocation": invocation_identity(inv, placeholder),
        **input_identity,
    }


def prepared_input_identity(inst: Instance, track: str) -> dict:
    data = (BENCH_ROOT / inst.relpath).read_bytes()
    prepped, _ = prepare_input(data, track)
    return {
        "source_sha256": hashlib.sha256(data).hexdigest(),
        "materialized_sha256": hashlib.sha256(prepped).hexdigest(),
        "materialization_version": MATERIALIZATION_VERSION[track],
    }


# ---------------------------------------------------------------------------
# Process execution with rusage


@dataclass
class ExecResult:
    stdout: bytes
    stderr_tail: str
    wall_sec: float
    cpu_sec: float | None
    exit_code: int | None
    timed_out: bool
    stdout_truncated: bool = False
    spawn_error: str = ""
    memout: bool = False  # the envelope backstop killed it (a legitimate outcome)


class _NonReapingProcessView:
    """Popen-shaped watchdog target that never steals ``wait4``'s child."""

    def __init__(self, pid: int) -> None:
        self.pid = pid

    def poll(self) -> int | None:
        try:
            os.kill(self.pid, 0)
            return None
        except ProcessLookupError:
            return 0
        except PermissionError:
            return None


def _kill_process_group(pgid: int) -> None:
    try:
        os.killpg(pgid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def _drain_head(stream, buf: bytearray, cap: int, sink, total: list[int]) -> None:
    try:
        while True:
            chunk = stream.read(65536)
            if not chunk:
                break
            total[0] += len(chunk)
            if sink is not None:
                sink.write(chunk)
            if len(buf) < cap:
                buf.extend(chunk[: cap - len(buf)])
    except (OSError, ValueError):
        pass


def _drain_tail(stream, buf: bytearray, cap: int) -> None:
    try:
        while True:
            chunk = stream.read(65536)
            if not chunk:
                break
            buf.extend(chunk)
            if len(buf) > cap:
                del buf[: len(buf) - cap]
    except (OSError, ValueError):
        pass


def run_process(inv: Invocation, timeout_s: int, stdout_sink_path: Path | None = None,
                memlimit_mb: int = 0,
                resource_envelope: dict | None = None) -> ExecResult:
    """Run in a fresh process group; SIGKILL the group at timeout+grace.

    Reaps via os.wait4 for child rusage (see module docstring for the
    process-tree limitation).

    `memlimit_mb` (0 = none) attaches the scripts/_oom_guard.py rss_watchdog
    backstop. A timeout alone does not bound the RSS of concurrent children, and
    this harness can invoke competitors without a native memory limit. Apply the
    external envelope uniformly; local wrapper or kernel limits cannot be
    assumed and may not cover `ay`, Java solvers, or binaries selected from
    `.competitors/`.
    """
    if resource_envelope is not None:
        if not valid_resource_envelope(resource_envelope):
            raise ValueError("run_process received an invalid resource envelope")
        envelope_memlimit = int(resource_envelope["memlimit_mb"])
        if memlimit_mb not in (0, envelope_memlimit):
            raise ValueError("memlimit_mb disagrees with resource_envelope")
        memlimit_mb = envelope_memlimit
    child_env = os.environ.copy()
    if resource_envelope is not None:
        child_env["NBCORE"] = str(resource_envelope["nbcore"])

    out_buf, err_buf = bytearray(), bytearray()
    out_total = [0]
    stdin_fh = None
    sink = None
    proc = None
    guard = None
    drain_threads: list[threading.Thread] = []
    leader_reaped = False
    try:
        if inv.stdin_path:
            stdin_fh = open(inv.stdin_path, "rb")
        if stdout_sink_path is not None:
            stdout_sink_path.parent.mkdir(parents=True, exist_ok=True)
            sink = open(stdout_sink_path, "wb")
        t0 = time.monotonic()
        try:
            proc = subprocess.Popen(
                inv.argv,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                stdin=stdin_fh if stdin_fh else subprocess.DEVNULL,
                start_new_session=True,
                cwd=str(REPO),
                env=child_env,
            )
        except OSError as exc:
            return ExecResult(b"", "", 0.0, None, None, False, spawn_error=str(exc))
        guard = rss_watchdog(
            _NonReapingProcessView(proc.pid),
            memlimit_mb,
            label=f"smtcomp_harness.py[{inv.argv[0]}]",
            poll_s=WATCHDOG_POLL_S,
            grace_mb=0,
        )
        t_out = threading.Thread(target=_drain_head,
                                 args=(proc.stdout, out_buf, STDOUT_CAP, sink, out_total),
                                 daemon=True)
        t_err = threading.Thread(target=_drain_tail,
                                 args=(proc.stderr, err_buf, STDERR_TAIL_CAP),
                                 daemon=True)
        t_out.start()
        t_err.start()
        drain_threads = [t_out, t_err]

        deadline = t0 + timeout_s + GRACE_SEC
        killed = False
        rusage = None
        status = 0
        while True:
            try:
                pid, status, rusage = os.wait4(proc.pid, os.WNOHANG)
            except ChildProcessError:  # someone else reaped (shouldn't happen)
                pid, rusage = proc.pid, None
            if pid == proc.pid:
                break
            now = time.monotonic()
            if now >= deadline and not killed:
                killed = True
                _kill_process_group(proc.pid)  # setsid => pgid == pid
            time.sleep(min(0.05, max(deadline - now, 0.005)))
        leader_reaped = True
        wall = time.monotonic() - t0
        # The wrapper may exit while leaving solver descendants alive. Kill the
        # entire isolated group on every outcome before disarming the only RSS
        # enforcement and before waiting for pipe EOF.
        _kill_process_group(proc.pid)
        guard.stop()
        memout = guard.breached
        try:
            exit_code = os.waitstatus_to_exitcode(status)
        except ValueError:
            exit_code = None
        proc.returncode = exit_code if exit_code is not None else -1  # stop Popen re-reaping
        t_out.join(timeout=10)
        t_err.join(timeout=10)
        for s in (proc.stdout, proc.stderr):
            try:
                s.close()
            except OSError:
                pass
        cpu = (rusage.ru_utime + rusage.ru_stime) if rusage else None
        return ExecResult(
            stdout=bytes(out_buf),
            stderr_tail=err_buf.decode("utf-8", errors="replace")[-500:],
            wall_sec=wall,
            cpu_sec=cpu,
            exit_code=exit_code,
            # A memout kill is not a timeout: both SIGKILL the group, but only one
            # means "this solver needed more RAM than the envelope". Conflating them
            # would silently retitle a resource limit as slowness.
            timed_out=(killed or wall > timeout_s) and not memout,
            stdout_truncated=out_total[0] > len(out_buf),
            memout=memout,
        )
    finally:
        if proc is not None:
            _kill_process_group(proc.pid)
            if guard is not None:
                guard.stop()
            if not leader_reaped:
                try:
                    _, cleanup_status = os.waitpid(proc.pid, 0)
                    proc.returncode = os.waitstatus_to_exitcode(cleanup_status)
                except (ChildProcessError, ProcessLookupError, ValueError):
                    pass
            for stream in (proc.stdout, proc.stderr):
                if stream is not None:
                    try:
                        stream.close()
                    except OSError:
                        pass
            for thread in drain_threads:
                thread.join(timeout=10)
        for fh in (stdin_fh, sink):
            if fh is not None:
                try:
                    fh.close()
                except OSError:
                    pass


# ---------------------------------------------------------------------------
# Answer parsing


def parse_answer_sq(stdout: str) -> str:
    for line in stdout.splitlines():
        if line.strip() in ANSWER_TOKENS:
            return line.strip()
    return "none"


def parse_answers_inc(stdout: str) -> list[str]:
    return [l.strip() for l in stdout.splitlines() if l.strip() in ANSWER_TOKENS]


def parse_core(stdout: str) -> tuple[str | None, int]:
    """Extract the first balanced (...) S-expression after the `unsat` line
    that is not an `(error ...)` response (some solvers answer unsat and then
    error on get-unsat-core — that is NOT a core).

    Returns (core_text, core_size) where core_size counts atoms (tokens that
    are not parens). Faithful capture only — validation is a later step."""
    lines = stdout.splitlines()
    for i, line in enumerate(lines):
        if line.strip() == "unsat":
            rest = "\n".join(lines[i + 1:])
            pos = 0
            while True:
                start = rest.find("(", pos)
                if start < 0:
                    return None, 0
                depth = 0
                end = -1
                for j in range(start, len(rest)):
                    if rest[j] == "(":
                        depth += 1
                    elif rest[j] == ")":
                        depth -= 1
                        if depth == 0:
                            end = j + 1
                            break
                if end < 0:
                    return None, 0  # unbalanced (truncated output?) — don't guess
                inner = rest[start + 1 : end - 1].split()
                if inner and inner[0] == "error":
                    pos = end
                    continue
                core = rest[start:end]
                atoms = core.replace("(", " ").replace(")", " ").split()
                return core, len(atoms)
    return None, 0


# ---------------------------------------------------------------------------
# run subcommand


def results_dir(track: str, division: str, tag: str) -> Path:
    d = RESULTS_ROOT / track / division / tag
    d.mkdir(parents=True, exist_ok=True)
    return d


def _repo_rel(p: Path) -> str:
    """Repo-relative when possible (stable across checkouts), else absolute
    (results root moved outside the repo via SMTCOMP_RESULTS_ROOT)."""
    try:
        return str(p.relative_to(REPO))
    except ValueError:
        return str(p)


def load_done(path: Path) -> dict[str, dict]:
    done: dict[str, dict] = {}
    if path.is_file():
        for line in path.read_text().splitlines():
            if not line.strip():
                continue
            try:
                rec = json.loads(line)
            except json.JSONDecodeError:
                continue
            done[rec["instance"]] = rec
    return done


def load_rows(path: Path) -> list[dict]:
    """All JSONL rows in file order (validate-uc rows are keyed by
    (instance, core_sha256) — a plain last-wins instance map would hide
    rows for other core versions)."""
    rows: list[dict] = []
    if path.is_file():
        for line in path.read_text().splitlines():
            if not line.strip():
                continue
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError:
                continue
    return rows


def core_file_hash(rec: dict) -> str | None:
    """Full sha256 of the run record's core file, or
    None when the record has no (existing) core file. Identifies WHICH core
    a validation row talks about (U4 review F1: a changed core must never
    reuse a stale validation verdict or reduced-benchmark path)."""
    core_rel = rec.get("core_path")
    core_file = (REPO / core_rel) if core_rel else None
    if core_file is None or not core_file.is_file():
        return None
    return file_sha256(core_file)


def model_file_hash(rec: dict) -> str | None:
    """Identify the exact model artifact attached to an MV run record.

    Model files are overwritten when a tag is re-run.  Validation therefore
    has to join on the artifact hash, not merely on the instance name, or a
    verdict for an older model can be silently reused for a newer one.
    """
    model_rel = rec.get("model_path")
    if not model_rel:
        return None
    model_path = Path(model_rel)
    if not model_path.is_absolute():
        model_path = REPO / model_path
    if not model_path.is_file():
        return None
    return file_sha256(model_path)


def validation_matches_run(row: dict, rec: dict) -> bool:
    """Bind a validator verdict to the exact producer run/input identity."""
    validation = row.get("validation_identity")
    run = rec.get("run_identity")
    if not isinstance(validation, dict) or not isinstance(run, dict):
        return False
    if validation.get("producer_run_cache_key") != rec.get("run_cache_key"):
        return False
    if validation.get("source_sha256") != run.get("source_sha256"):
        return False
    if validation.get("track") == "mv":
        return (validation.get("materialized_sha256")
                == run.get("materialized_sha256"))
    return True


def validation_matches_artifact(row: dict) -> bool:
    identity = row.get("validation_identity")
    if not isinstance(identity, dict):
        return False
    if identity.get("track") == "uc":
        return identity.get("core_sha256") == row.get("core_sha256")
    if identity.get("track") == "mv":
        return identity.get("model_sha256") == row.get("model_sha256")
    return False


def reusable_run_record(rec: dict, expected_identity: dict) -> bool:
    """True only when every cache-relevant run condition is identical."""
    expected_key = identity_key(expected_identity)
    recorded_identity = rec.get("run_identity")
    if not isinstance(recorded_identity, dict):
        return False
    return (
        rec.get("run_cache_key") == expected_key
        and recorded_identity == expected_identity
        and identity_key(recorded_identity) == expected_key
    )


def require_comparable_run_envelope(
        by_solver: dict[str, dict[str, dict]]) -> dict:
    """Return the common run envelope or refuse a mixed comparison.

    A resumable tag can contain rows from several invocations.  Ranking a
    solver whose rows used different limits, or comparing solvers run under
    different limits, turns memory pressure into an apparent capability
    delta.  Scoring must fail closed instead of merely annotating that result.
    """
    per_solver: dict[str, set[str]] = {}
    decoded: dict[str, dict] = {}
    invalid: list[str] = []
    for solver, recs in by_solver.items():
        keys: set[str] = set()
        for instance, rec in recs.items():
            envelope = rec.get("resource_envelope")
            if not valid_resource_envelope(envelope):
                invalid.append(f"{solver}:{instance}")
                continue
            key = canonical_json(envelope)
            keys.add(key)
            decoded[key] = envelope
        per_solver[solver] = keys
    all_values = {value for values in per_solver.values() for value in values}
    mixed_within = {solver: values for solver, values in per_solver.items()
                    if len(values) > 1}
    if invalid or mixed_within or len(all_values) > 1:
        detail = ", ".join(
            f"{solver}={len(values)} envelope(s)"
            for solver, values in sorted(per_solver.items())
        )
        raise SystemExit(
            "cannot score results with missing, invalid, or different full "
            f"resource envelopes: {detail}; invalid={invalid[:5]}. "
            "Re-run the tag with --overwrite, or "
            "use separate tags for separate envelopes."
        )
    return decoded[next(iter(all_values))] if all_values else {}


def require_comparable_run_conditions(
        by_solver: dict[str, dict[str, dict]]) -> tuple[dict, int]:
    """Fail closed on stale/tampered identities or incomparable measurements."""
    envelope = require_comparable_run_envelope(by_solver)
    timeouts: set[int] = set()
    tracks: set[str] = set()
    instance_inputs: dict[str, set[tuple[str, str, str, str, str]]] = {}
    per_solver_binary: dict[str, set[str]] = {}
    per_solver_command: dict[tuple[str, str], set[str]] = {}
    invalid: list[str] = []
    for solver, recs in by_solver.items():
        for instance, rec in recs.items():
            identity = rec.get("run_identity")
            if (not isinstance(identity, dict)
                    or identity.get("version") != RUN_IDENTITY_VERSION
                    or identity.get("instance") != instance
                    or not isinstance(identity.get("solver"), dict)
                    or identity["solver"].get("name") != solver
                    or rec.get("run_cache_key") != identity_key(identity)
                    or identity.get("resource_envelope") != envelope):
                invalid.append(f"{solver}:{instance}")
                continue
            try:
                timeouts.add(int(identity["timeout_s"]))
                tracks.add(str(identity["track"]))
                instance_inputs.setdefault(instance, set()).add((
                    str(identity["source_sha256"]),
                    str(identity["materialized_sha256"]),
                    str(identity["materialization_version"]),
                    str(identity["logic"]),
                    canonical_json(identity["expected"]),
                ))
                per_solver_binary.setdefault(solver, set()).add(
                    canonical_json(identity["solver"])
                )
                per_solver_command.setdefault(
                    (solver, str(identity["logic"])), set()
                ).add(canonical_json(identity["invocation"]))
            except (KeyError, TypeError, ValueError):
                invalid.append(f"{solver}:{instance}")
    mixed_inputs = [inst for inst, values in instance_inputs.items()
                    if len(values) > 1]
    mixed_binaries = [solver for solver, values in per_solver_binary.items()
                      if len(values) > 1]
    mixed_commands = [f"{solver}:{logic}"
                      for (solver, logic), values in per_solver_command.items()
                      if len(values) > 1]
    corpus_sets = {tuple(sorted(recs)) for recs in by_solver.values()}
    if (invalid or len(timeouts) != 1 or len(tracks) != 1
            or mixed_inputs or mixed_binaries
            or mixed_commands or len(corpus_sets) > 1):
        raise SystemExit(
            "cannot score incomparable run conditions: "
            f"invalid identities={invalid[:5]}, timeouts={sorted(timeouts)}, "
            f"tracks={sorted(tracks)}, "
            f"mixed inputs={mixed_inputs[:5]}, mixed binaries={mixed_binaries}, "
            f"mixed commands={mixed_commands[:5]}, "
            f"corpus variants={len(corpus_sets)}. Re-run with --overwrite."
        )
    return envelope, next(iter(timeouts))


def require_comparable_validation_envelope(
        by_solver: dict[str, dict[str, dict]], track: str) -> dict:
    """Return the common validator envelope or refuse a mixed scoreboard."""
    per_solver: dict[str, set[str]] = {}
    decoded: dict[str, dict] = {}
    invalid: list[str] = []
    for solver, rows in by_solver.items():
        values: set[str] = set()
        for instance, row in rows.items():
            envelope = row.get("validation_resource_envelope")
            if not valid_resource_envelope(envelope):
                invalid.append(f"{solver}:{instance}")
                continue
            key = canonical_json(envelope)
            values.add(key)
            decoded[key] = envelope
        per_solver[solver] = values
    all_values = {value for values in per_solver.values() for value in values}
    mixed_within = {solver: values for solver, values in per_solver.items()
                    if len(values) > 1}
    if invalid or mixed_within or len(all_values) > 1:
        detail = ", ".join(
            f"{solver}={len(values)} envelope(s)"
            for solver, values in sorted(per_solver.items())
        )
        raise SystemExit(
            f"cannot score {track} validation with missing, invalid, or "
            f"different full resource envelopes: {detail}; "
            f"invalid={invalid[:5]}. Re-run validation "
            "with --overwrite under one envelope."
        )
    return decoded[next(iter(all_values))] if all_values else {}


def require_comparable_validation_conditions(
        by_solver: dict[str, dict[str, dict]], track: str) -> dict:
    envelope = require_comparable_validation_envelope(by_solver, track)
    invalid: list[str] = []
    timeouts: set[int] = set()
    source_by_instance: dict[str, set[str]] = {}
    mv_configs: set[str] = set()
    uc_pools_by_logic: dict[str, set[str]] = {}
    for solver, rows in by_solver.items():
        for instance, row in rows.items():
            identity = row.get("validation_identity")
            if (not isinstance(identity, dict)
                    or identity.get("version") != VALIDATION_IDENTITY_VERSION
                    or identity.get("instance") != instance
                    or identity.get("producer") != solver
                    or identity.get("track") != track
                    or row.get("validation_cache_key") != identity_key(identity)
                    or identity.get("resource_envelope") != envelope):
                invalid.append(f"{solver}:{instance}")
                continue
            try:
                timeouts.add(int(identity["timeout_s"]))
                source_by_instance.setdefault(instance, set()).add(
                    str(identity["source_sha256"])
                )
                if track == "mv":
                    mv_configs.add(canonical_json(identity["validator_config"]))
                elif track == "uc":
                    uc_pools_by_logic.setdefault(
                        str(identity["logic"]), set()
                    ).add(canonical_json(identity["validator_pool"]))
            except (KeyError, TypeError, ValueError):
                invalid.append(f"{solver}:{instance}")
    mixed_source = [inst for inst, values in source_by_instance.items()
                    if len(values) > 1]
    mixed_uc_pools = [logic for logic, values in uc_pools_by_logic.items()
                      if len(values) > 1]
    if (invalid or len(timeouts) > 1 or mixed_source or mixed_uc_pools
            or (track == "mv" and len(mv_configs) > 1)):
        raise SystemExit(
            f"cannot score incomparable {track} validation conditions: "
            f"invalid identities={invalid[:5]}, timeouts={sorted(timeouts)}, "
            f"mixed source inputs={mixed_source[:5]}, "
            f"validator configs={len(mv_configs)}, "
            f"mixed UC validator pools={mixed_uc_pools}. "
            "Re-run validation with "
            "--overwrite."
        )
    return envelope


def run_one(sol: Solver, inst: Instance, track: str, timeout_s: int,
            tag_dir: Path, tmpdir: str, resource_envelope: dict,
            known_solver_identity: dict | None = None) -> dict:
    src = BENCH_ROOT / inst.relpath
    tmp, original, n_named = materialize(src, track, tmpdir)
    try:
        run_identity = make_run_identity(
            sol, inst, track, timeout_s, resource_envelope,
            known_solver_identity=known_solver_identity,
            source_bytes=original,
        )
        inv = build_invocation(sol, track, inst.logic, tmp, resource_envelope,
                               timeout_s=timeout_s)
        assert inv is not None  # filtered before scheduling
        sink_path = None
        if track == "mv":
            sink_path = tag_dir / "models" / sol.name / (inst.relpath + ".out")
        res = run_process(inv, timeout_s, stdout_sink_path=sink_path,
                          resource_envelope=resource_envelope)
        stdout = res.stdout.decode("utf-8", errors="replace")
        rec: dict = {
            "instance": inst.relpath,
            "solver": sol.name,
            "logic": inst.logic,
            "expected": inst.expected,
            "wall_sec": round(res.wall_sec, 3),
            "cpu_sec": round(res.cpu_sec, 3) if res.cpu_sec is not None else None,
            "exit_code": res.exit_code,
            "timed_out": res.timed_out,
            "timeout_s": timeout_s,
            "resource_envelope": resource_envelope,
            # Kept as a flat convenience field; cache/scoring use the complete
            # canonical resource envelope above.
            "memlimit_mb": resource_envelope["memlimit_mb"],
            "run_identity": run_identity,
            "run_cache_key": identity_key(run_identity),
            "memout": res.memout,
            "stderr_tail": res.stderr_tail if (res.spawn_error or res.exit_code not in (0,)) else "",
        }
        if res.spawn_error:
            rec["stderr_tail"] = res.spawn_error
        if res.stdout_truncated:
            rec["stdout_truncated"] = True
        if track == "inc":
            answers = parse_answers_inc(stdout)
            rec["answer"] = ",".join(answers)
            rec["n_answers"] = len(answers)
        elif track == "mv":
            rec["answer"] = parse_answer_sq(stdout)
            rec["model_path"] = _repo_rel(sink_path) if sink_path else None
            rec["model_bytes"] = sink_path.stat().st_size if sink_path and sink_path.exists() else 0
        elif track == "uc":
            rec["answer"] = parse_answer_sq(stdout)
            rec["n_asserts"] = n_named  # named asserts in the prepped temp = reduction baseline
            core, size = (None, 0)
            if rec["answer"] == "unsat":
                core, size = parse_core(stdout)
            rec["core_size"] = size
            if core is not None:
                cpath = tag_dir / "cores" / sol.name / (inst.relpath + ".core")
                cpath.parent.mkdir(parents=True, exist_ok=True)
                cpath.write_text(core)
                rec["core_path"] = _repo_rel(cpath)
        else:  # sq
            rec["answer"] = parse_answer_sq(stdout)
        return rec
    finally:
        try:
            os.unlink(tmp)
        except OSError:
            pass


def cmd_run(args: argparse.Namespace) -> None:
    track = args.track
    tasks = load_manifest(track, args.division)
    if args.only:
        rx = re.compile(args.only)
        tasks = [t for t in tasks if rx.search(t.relpath)]
    if args.sample:
        tasks = stratified_sample(tasks, args.sample, args.seed)
    if args.limit:
        tasks = tasks[: args.limit]
    if not tasks:
        raise SystemExit("no tasks selected")

    registry = build_registry()
    requested = [s.strip() for s in args.solvers.split(",") if s.strip()]
    solvers: list[Solver] = []
    for name in requested:
        if name not in registry:
            raise SystemExit(f"unknown solver {name!r}; known: {sorted(registry)}")
        sol = registry[name]
        if not sol.available:
            print(f"[registry] WARNING: {name} unavailable "
                  f"(binary={sol.binary}) — skipping", file=sys.stderr)
            continue
        if build_invocation(sol, track, tasks[0].logic, "PROBE.smt2") is None:
            print(f"[registry] WARNING: {name} has no 2025 {TRACKS[track]} "
                  f"participation covering logic {tasks[0].logic!r} — skipping",
                  file=sys.stderr)
            continue
        if sol.note:
            print(f"[registry] {name}: {sol.binary} ({sol.note})")
        else:
            print(f"[registry] {name}: {sol.binary}")
        solvers.append(sol)
    if not solvers:
        raise SystemExit("no available solvers to run")

    tag_dir = results_dir(track, args.division, args.tag)
    tmpdir = tempfile.mkdtemp(prefix=f"smtcomp-{track}-{args.tag}-")
    requested_jobs = args.jobs
    plan = plan_solver_resources(requested_jobs, label="smtcomp_harness.py")
    jobs = plan.jobs
    resource_envelope = make_resource_envelope(requested_jobs, plan)

    if args.dry_run:
        inst = tasks[0]
        tmp, _, n_named = materialize(BENCH_ROOT / inst.relpath, track, tmpdir)
        print(f"\n[dry-run] instance: {inst.relpath} (logic={inst.logic}, "
              f"expected={inst.expected})")
        prep_label = ("mv-prepped: set-infos stripped, produce-models, get-model"
                      if track == "mv" else
                      "status-stripped"
                      + (f", uc-prepped: {n_named} asserts named smtcompN"
                         if track == "uc" else ""))
        print(f"[dry-run] temp file ({prep_label}): {tmp}")
        for sol in solvers:
            inv = build_invocation(sol, track, inst.logic, tmp,
                                   resource_envelope, timeout_s=timeout_s)
            assert inv is not None
            feed = f"  (stdin <- {inv.stdin_path})" if inv.stdin_path else ""
            print(f"[dry-run] {sol.name}: argv = {inv.argv}{feed}")
            if inv.smtcomp_command:
                print(f"[dry-run]   2025 submission command: {inv.smtcomp_command}")
        print(f"[dry-run] resource envelope: {canonical_json(resource_envelope)}")
        print("[dry-run] temp file kept for inspection; no solver launched")
        return

    # RAM-aware admission control (scripts/_oom_guard.py): --jobs N spawns N
    # concurrent (solver, instance) pairs, and --timeout alone does not bound
    # their memory. Cap concurrency and enforce a per-child RSS envelope.
    warn_concurrent_build()
    if jobs < requested_jobs:
        print(f"[run] OOM GUARD: --jobs {requested_jobs} -> {jobs} "
              f"(RAM budget; see scripts/_oom_guard.py)")

    print(f"[run] {track}/{args.division} tag={args.tag}: {len(tasks)} instances, "
          f"solvers={[s.name for s in solvers]}, timeout={args.timeout}s "
          f"(+{GRACE_SEC}s grace), jobs={jobs}/{requested_jobs} admitted/requested, "
          f"memlimit={plan.memlimit_mb or 'none'}MB/child, "
          f"NBCORE={plan.nbcore}, headroom={plan.headroom_mb}MB")
    solver_identities = {sol.name: solver_identity(sol) for sol in solvers}
    # Source/materialization hashes are solver-independent. Compute them once
    # rather than reparsing every benchmark once per competitor during resume.
    input_identities = {
        task.relpath: prepared_input_identity(task, track) for task in tasks
    }
    try:
        for sol in solvers:
            out_path = tag_dir / f"{sol.name}.jsonl"
            if args.overwrite and out_path.exists():
                out_path.unlink()
            done = load_done(out_path)
            expected_identities = {
                task.relpath: make_run_identity(
                    sol, task, track, args.timeout, resource_envelope,
                    known_solver_identity=solver_identities[sol.name],
                    known_input_identity=input_identities[task.relpath],
                )
                for task in tasks
            }
            cached = {
                instance for instance, rec in done.items()
                if instance in expected_identities
                and reusable_run_record(rec, expected_identities[instance])
            }
            stale_envelope = sum(
                1 for task in tasks
                if task.relpath in done and task.relpath not in cached
            )
            todo = [t for t in tasks if t.relpath not in cached]
            if not todo:
                print(f"[run] {sol.name}: all {len(tasks)} already done")
                continue
            print(f"[run] {sol.name}: {len(todo)} to run ({len(cached)} cached"
                  + (f", {stale_envelope} stale under another run identity"
                     if stale_envelope else "")
                  + ")")
            lock = threading.Lock()
            completed = 0
            t0 = time.monotonic()
            with out_path.open("a") as fh, ThreadPoolExecutor(max_workers=jobs) as pool:
                futs = {pool.submit(run_one, sol, t, track, args.timeout, tag_dir,
                                    tmpdir, resource_envelope,
                                    solver_identities[sol.name]): t
                        for t in todo}
                for fut in as_completed(futs):
                    rec = fut.result()
                    with lock:
                        fh.write(json.dumps(rec) + "\n")
                        fh.flush()
                        completed += 1
                        if completed % 25 == 0 or completed == len(todo):
                            rate = completed / max(time.monotonic() - t0, 1e-9)
                            eta = (len(todo) - completed) / max(rate, 1e-9)
                            print(f"[run] {sol.name}: {completed}/{len(todo)} "
                                  f"({rate:.2f}/s, eta {eta/60:.1f}m)", flush=True)
            recs = load_done(out_path)
            n_def = sum(1 for r in recs.values()
                        if (r.get("answer") or "").split(",")[0] in ("sat", "unsat"))
            n_to = sum(1 for r in recs.values() if r.get("timed_out"))
            print(f"[run] {sol.name}: {len(recs)} recorded, {n_def} definite, {n_to} timed out")
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)
    print(f"[run] results in {tag_dir}")


# ---------------------------------------------------------------------------
# validate-uc subcommand — 2025 unsat-core validation
#
# 2025 rule (smtcomp-io scoring.py/results.py):
# the reduced benchmark (only core-named asserts kept) is given to the
# division's validating solvers (SQ configurations). The core is VALID iff
# strictly more validators answer unsat than sat; #sat >= #unsat with #sat > 0
# INVALIDATES the core (error, e=1); all timeout/unknown = no points, no
# error. A solver never validates its own cores (AY must never count as its
# own validator). Correctness first: anything unvalidated scores 0.


def validation_path(tag_dir: Path, solver: str) -> Path:
    return tag_dir / "validation" / f"{solver}.jsonl"


def validator_config(vsol: Solver, logic: str, resource_envelope: dict,
                     known_identity: dict | None = None) -> dict:
    placeholder = "{INPUT}"
    inv = build_invocation(vsol, "sq", logic, placeholder,
                           resource_envelope)
    return {
        "solver": known_identity or solver_identity(vsol),
        "invocation": (invocation_identity(inv, placeholder)
                       if inv is not None else None),
    }


def make_uc_validation_identity(
        rec: dict, solver_name: str, validators: list[Solver], timeout_s: int,
        resource_envelope: dict,
        validator_identities: dict[str, dict] | None = None) -> dict:
    """Exact core, benchmark, validator, command, and envelope cache identity."""
    inst = rec["instance"]
    src_data = (BENCH_ROOT / inst).read_bytes()
    stripped = strip_status(src_data)
    core_rel = rec.get("core_path")
    core_file = (REPO / core_rel) if core_rel else None
    core_bytes = core_file.read_bytes() \
        if core_file is not None and core_file.is_file() else None
    names = core_names(core_bytes.decode("utf-8", errors="replace")) \
        if core_bytes is not None else []
    reduced, _, _ = build_reduced(stripped, set(names))
    vlist = [v for v in validators if v.name != solver_name]
    identities = validator_identities or {}
    pool = [
        validator_config(v, rec.get("logic", ""), resource_envelope,
                         identities.get(v.name))
        for v in validators
    ]
    return {
        "version": VALIDATION_IDENTITY_VERSION,
        "instance": inst,
        "producer": solver_name,
        "track": "uc",
        "logic": rec.get("logic", ""),
        "timeout_s": int(timeout_s),
        "resource_envelope": resource_envelope,
        "producer_run_cache_key": rec.get("run_cache_key"),
        "source_sha256": hashlib.sha256(src_data).hexdigest(),
        "status_stripped_sha256": hashlib.sha256(stripped).hexdigest(),
        "materialized_sha256": hashlib.sha256(reduced).hexdigest(),
        "materialization_version": MATERIALIZATION_VERSION["uc"],
        "core_sha256": (hashlib.sha256(core_bytes).hexdigest()
                        if core_bytes is not None else None),
        "validator_pool": pool,
        "validators": [
            validator_config(v, rec.get("logic", ""), resource_envelope,
                             identities.get(v.name))
            for v in vlist
        ],
    }


def _run_validator(vsol: Solver, logic: str, reduced: Path, timeout_s: int,
                   resource_envelope: dict) -> dict:
    memlimit_mb = int(resource_envelope["memlimit_mb"])
    inv = build_invocation(vsol, "sq", logic, str(reduced),
                           resource_envelope)
    if inv is None:  # no 2025 SQ participation for this logic
        return {"answer": "not-applicable", "wall_sec": 0.0, "cpu_sec": None,
                "memlimit_mb": memlimit_mb, "memout": False}
    res = run_process(inv, timeout_s, resource_envelope=resource_envelope)
    ans = parse_answer_sq(res.stdout.decode("utf-8", errors="replace"))
    out = {"answer": ans, "wall_sec": round(res.wall_sec, 3),
           "cpu_sec": round(res.cpu_sec, 3) if res.cpu_sec is not None else None,
           "memlimit_mb": memlimit_mb, "memout": res.memout}
    if res.timed_out:
        out["timed_out"] = True
    if res.spawn_error:
        out["spawn_error"] = res.spawn_error
    return out


def health_check_validators(validators: list[Solver], logics: set[str],
                            timeout_s: int, resource_envelope: dict) -> None:
    """Fail-closed validator startup check (U4 review F2): every requested
    validator must answer `unsat` on a trivial unsat instance for every
    logic in the workload, through the exact invocation used for real
    validation. ANY failure aborts the whole batch loudly — a dead validator
    recorded as neutral `none` rows would silently halve the quorum and bias
    validation toward `valid` (the surviving validator alone decides) and
    away from invalidation. Known offender: the macOS /usr/bin/java stub
    "runs" SMTInterpol for 0.06 s with no answer; set JAVA_BIN to a real JRE
    (e.g. .competitors/temurin21-jre/Contents/Home/bin/java)."""
    with tempfile.TemporaryDirectory(prefix="smtcomp-vhc-") as td:
        for logic in sorted(logics):
            trivial = Path(td) / f"trivial_unsat_{logic}.smt2"
            trivial.write_bytes(b"(set-logic " + logic.encode("utf-8")
                                + b")\n(assert false)\n(check-sat)\n")
            for v in validators:
                r = _run_validator(v, logic, trivial, timeout_s,
                                   resource_envelope)
                if r["answer"] == "unsat":
                    continue
                inv = build_invocation(v, "sq", logic, str(trivial),
                                       resource_envelope)
                raise SystemExit(
                    f"[validate-uc] VALIDATOR HEALTH CHECK FAILED — aborting "
                    f"before spending any validation time.\n"
                    f"  validator: {v.name} (binary={v.binary}"
                    + (f", java={v.java}" if v.kind == "jar" else "") + ")\n"
                    f"  logic:     {logic}\n"
                    f"  expected:  unsat on a trivial (assert false)\n"
                    f"  got:       {r}\n"
                    f"  command:   {inv.argv if inv else 'NOT APPLICABLE (no 2025 SQ participation for this logic)'}\n"
                    f"  A validator that cannot answer must NOT be counted as "
                    f"a neutral quorum member (it would bias toward 'valid'). "
                    f"Fix the binary (for smtinterpol: JAVA_BIN=<real JRE>/bin/java) "
                    f"or drop it from --validators explicitly.")
    print(f"[validate-uc] health check OK: "
          f"{', '.join(v.name for v in validators)} on {sorted(logics)}")


def validate_uc_one(rec: dict, solver_name: str, validators: list[Solver],
                    tag_dir: Path, timeout_s: int, resource_envelope: dict,
                    validator_identities: dict[str, dict] | None = None) -> dict:
    inst = rec["instance"]
    vlist = [v for v in validators if v.name != solver_name]
    validation_identity = make_uc_validation_identity(
        rec, solver_name, validators, timeout_s, resource_envelope,
        validator_identities,
    )
    row: dict = {"instance": inst, "solver": solver_name,
                 "logic": rec.get("logic", ""), "reduction": 0,
                 "validators_used": [v.name for v in vlist],
                 "validation_timeout_s": timeout_s,
                 "validation_resource_envelope": resource_envelope,
                 "validator_memlimit_mb": resource_envelope["memlimit_mb"],
                 "validation_identity": validation_identity,
                 "validation_cache_key": identity_key(validation_identity)}
    core_rel = rec.get("core_path")
    core_file = (REPO / core_rel) if core_rel else None
    if core_file is None or not core_file.is_file():
        row["status"] = "no_core"  # answered unsat but produced no core: 0 points
        return row
    core_bytes = core_file.read_bytes()
    # U4 review F1: the row is about THIS core, not "the instance" — record
    # the core hash so cache lookups and scoring can detect a changed core.
    chash = hashlib.sha256(core_bytes).hexdigest()
    row["core_sha256"] = chash
    if validation_identity.get("core_sha256") != chash:
        row["status"] = "artifact_changed"
        row["note"] = "core file changed while validation was being prepared"
        return row
    names = core_names(core_bytes.decode("utf-8", errors="replace"))
    src = BENCH_ROOT / inst
    src_bytes = src.read_bytes()
    data = strip_status(src_bytes)
    reduced_bytes, matched, n_named = build_reduced(data, set(names))
    if (validation_identity.get("source_sha256")
            != hashlib.sha256(src_bytes).hexdigest()
            or validation_identity.get("status_stripped_sha256")
            != hashlib.sha256(data).hexdigest()
            or validation_identity.get("materialized_sha256")
            != hashlib.sha256(reduced_bytes).hexdigest()):
        row["status"] = "artifact_changed"
        row["note"] = "benchmark changed while validation was being prepared"
        return row
    row["n_asserts"] = n_named
    row["core_names"] = len(names)
    unknown = sorted(set(names) - set(matched))
    if unknown:
        # A core referencing names that do not exist in the benchmark is a
        # malformed answer — the 2025 validation build would fail on it.
        row["status"] = "invalid_names"
        row["unknown_names"] = unknown[:5] + (
            [f"... {len(unknown) - 5} more"] if len(unknown) > 5 else [])
        return row
    if not names and n_named > 0:
        # An empty core claims unsat-with-no-assertions on a benchmark that
        # has assertions: the reduced benchmark is trivially sat, so the
        # validators can only invalidate it. Decide without spending them.
        row["status"] = "invalidated"
        row["note"] = "empty core on a benchmark with assertions"
        return row
    if not vlist:
        row["status"] = "no_validator"  # e.g. z3 core with z3-only validators
        return row
    # Per-(solver, instance, core-hash) path: concurrent validations of
    # DIFFERENT cores for one instance must never overwrite each other's
    # reduced benchmark mid-run (U4 review F1 — this aliasing produced a
    # false "validator wrong-sat" alarm during the review).
    red_path = tag_dir / "reduced" / solver_name / (inst + f".{chash}.reduced.smt2")
    red_path.parent.mkdir(parents=True, exist_ok=True)
    red_path.write_bytes(reduced_bytes)
    row["reduced_path"] = _repo_rel(red_path)
    vres: dict[str, dict] = {}
    n_unsat = n_sat = 0
    for v in vlist:  # sequential: at most `jobs` solver processes machine-wide
        r = _run_validator(v, rec.get("logic", ""), red_path, timeout_s,
                           resource_envelope)
        vres[v.name] = r
        if r["answer"] == "unsat":
            n_unsat += 1
        elif r["answer"] == "sat":
            n_sat += 1
    row["validator_results"] = vres
    if n_unsat > n_sat:
        row["status"] = "valid"
        row["reduction"] = max(n_named - len(names), 0)
    elif n_sat > 0:
        row["status"] = "invalidated"
    else:
        row["status"] = "unvalidated"  # all timeout/unknown: 0 points, no error
    return row


def cmd_validate_uc(args: argparse.Namespace) -> None:
    tag_dir = results_dir("uc", args.division, args.tag)
    registry = build_registry()
    validators: list[Solver] = []
    seen_validators: set[str] = set()
    for name in (s.strip() for s in args.validators.split(",")):
        if not name:
            continue
        if name in seen_validators:
            raise SystemExit(f"duplicate validator {name!r} would bias the quorum")
        seen_validators.add(name)
        if name not in registry:
            raise SystemExit(f"unknown validator {name!r}; known: {sorted(registry)}")
        if not registry[name].available:
            raise SystemExit(f"validator {name!r} unavailable "
                             f"(binary={registry[name].binary})")
        validators.append(registry[name])
    if not validators:
        raise SystemExit("no validators given")

    files = sorted(tag_dir.glob("*.jsonl"))
    if args.solvers:
        keep = {s.strip() for s in args.solvers.split(",")}
        files = [f for f in files if f.stem in keep]
    if not files:
        raise SystemExit(f"no result files under {tag_dir}")

    # Validators are solver processes too.  They previously bypassed the
    # run subcommand's admission plan and watchdog entirely, so --jobs N
    # could launch N unbounded cvc5/SMTInterpol children.
    warn_concurrent_build()
    requested_jobs = args.jobs
    plan = plan_solver_resources(requested_jobs,
                                 label="smtcomp_harness.py validate-uc")
    jobs = plan.jobs
    resource_envelope = make_resource_envelope(requested_jobs, plan)
    if jobs < requested_jobs:
        print(f"[validate-uc] OOM GUARD: --jobs {requested_jobs} -> {jobs} "
              f"(RAM budget; see scripts/_oom_guard.py)")
    validator_identities = {v.name: solver_identity(v) for v in validators}

    # Fail-closed startup check (U4 review F2): never start a batch with a
    # dead validator. Health-check every (validator, logic) pair that the
    # workload can touch, through the real invocation path.
    all_logics: set[str] = set()
    for f in files:
        for r in load_done(f).values():
            if r.get("answer") == "unsat" and r.get("logic"):
                all_logics.add(r["logic"])
    if all_logics:
        health_check_validators(validators, all_logics,
                                min(args.timeout, 120), resource_envelope)

    for f in files:
        solver_name = f.stem
        vnames = [v.name for v in validators if v.name != solver_name]
        vpath = validation_path(tag_dir, solver_name)
        if args.overwrite and vpath.exists():
            vpath.unlink()
        # Cache identity includes the artifact, benchmark transform, exact
        # validator binaries/commands, timeout, and full resource envelope.
        done_keys: set[str] = set()
        done_insts: set[str] = set()
        for row in load_rows(vpath):
            recorded_identity = row.get("validation_identity")
            key = row.get("validation_cache_key")
            if (isinstance(recorded_identity, dict)
                    and key == identity_key(recorded_identity)
                    and validation_matches_artifact(row)):
                done_keys.add(key)
            done_insts.add(row["instance"])
        recs = [r for r in load_done(f).values() if r.get("answer") == "unsat"]
        expected_keys = {
            r["instance"]: identity_key(make_uc_validation_identity(
                r, solver_name, validators, args.timeout, resource_envelope,
                validator_identities,
            ))
            for r in recs
        }
        todo = [r for r in recs if expected_keys[r["instance"]] not in done_keys]
        stale = sum(1 for r in todo if r["instance"] in done_insts)
        if args.limit:
            todo = todo[: args.limit]
        print(f"[validate-uc] {solver_name}: {len(recs)} unsat answers, "
              f"{len(todo)} to validate ({len(done_keys)} cached"
              + (f", {stale} stale rows superseded — artifact/config changed" if stale
                 else "")
              + f"); validators={vnames or 'NONE (self excluded)'}, "
              f"timeout={args.timeout}s, jobs={jobs}/{requested_jobs}, "
              f"memlimit={plan.memlimit_mb}MB/child, NBCORE={plan.nbcore}, "
              f"headroom={plan.headroom_mb}MB")
        if not todo:
            continue
        vpath.parent.mkdir(parents=True, exist_ok=True)
        lock = threading.Lock()
        completed = 0
        t0 = time.monotonic()
        with vpath.open("a") as fh, ThreadPoolExecutor(max_workers=jobs) as pool:
            futs = [pool.submit(validate_uc_one, r, solver_name, validators,
                                tag_dir, args.timeout, resource_envelope,
                                validator_identities)
                    for r in todo]
            for fut in as_completed(futs):
                row = fut.result()
                with lock:
                    fh.write(json.dumps(row) + "\n")
                    fh.flush()
                    completed += 1
                    if completed % 10 == 0 or completed == len(todo):
                        rate = completed / max(time.monotonic() - t0, 1e-9)
                        print(f"[validate-uc] {solver_name}: {completed}/{len(todo)} "
                              f"({rate:.2f}/s)", flush=True)
        rows = load_done(vpath)
        by_status: dict[str, int] = {}
        for r in rows.values():
            by_status[r.get("status", "?")] = by_status.get(r.get("status", "?"), 0) + 1
        total_red = sum(int(r.get("reduction") or 0) for r in rows.values()
                        if r.get("status") == "valid")
        print(f"[validate-uc] {solver_name}: {dict(sorted(by_status.items()))}, "
              f"validated reduction (uncapped) = {total_red}")
    print(f"[validate-uc] done; score with: score --track uc "
          f"--division {args.division} --tag {args.tag}")


# ---------------------------------------------------------------------------
# validate-mv subcommand — EXACT 2025 Dolmen pipeline
# (smtcomp/model_validation.py check_locally + check_result_locally @ smtcomp25)

# defs.Answer names used by the 2025 pipeline, recorded verbatim in our jsonl.
V_OK = "Sat"  # ValidationOk => the run's answer stays Sat (the only point-scorer)
V_MODEL_UNSAT = "ModelUnsat"  # E:bad-model — the only division-voiding validation error
V_TIMEOUT = "ModelValidatorTimeout"
V_MEMOUT = "ModelValidatorMemoryOut"
V_EXCEPTION = "ModelValidatorException"
V_STRICT_TYPING = "ModelValidatorBenchmarkStrictTyping"
V_PARSING = "ModelParsingError"
V_PARTIAL_FUN = "ModelPartialFunctionMissing"
V_NOT_VALIDATED = "ModelNotValidated"  # sat answer, no validation record
V_UNKNOWN = "UnknownValidatorError"  # 2025 raised ValueError here; we record + flag

_DOLMEN_STDERR_MAP = [  # 2025 check_locally, verbatim order
    (b"E:bad-model\n", V_MODEL_UNSAT),
    (b"E:timeout\n", V_TIMEOUT),
    (b"E:uncaught-exn\n", V_EXCEPTION),
    (b"E:forbidden-array-sort\n", V_STRICT_TYPING),
    (b"E:non-linear-expr\n", V_STRICT_TYPING),
    (b"E:id-def-conflict\n", V_PARSING),
    (b"E:parsing-error\n", V_PARSING),
    (b"E:lexing-error\n", V_PARSING),
    (b"E:unbound-id\n", V_PARSING),
    (b"E:undefined-constant\n", V_PARSING),
    (b"E:partial-dstr\n", V_PARTIAL_FUN),
]


def find_dolmen() -> Path | None:
    return _find("DOLMEN_BIN", COMPETITORS / "dolmen/dolmen", "dolmen")


def dolmen_status(returncode: int, stderr: bytes) -> str:
    if returncode == 0:
        return V_OK
    if returncode == 2:  # LimitReached (--time/--size)
        return V_TIMEOUT
    for suffix, status in _DOLMEN_STDERR_MAP:
        if stderr.endswith(suffix):
            return status
    return V_UNKNOWN


def dolmen_argv(dolmen: Path, bench: str, time_budget: str,
                size_budget: str, force_logic_all: bool) -> list[str]:
    argv = [str(dolmen), f"--time={time_budget}", f"--size={size_budget}",
            "--strict=false", "--check-model=true", "--report-style=minimal",
            "--warn=-all"]
    if force_logic_all:
        argv.append("--force-smtlib2-logic=ALL")
    argv.append(bench)
    return argv


def make_mv_validation_identity(
        dolmen: Path, rec: dict, time_budget: str, size_budget: str,
        wall_cap: int, resource_envelope: dict,
        known_dolmen_identity: dict | None = None) -> dict:
    src = BENCH_ROOT / rec["instance"]
    src_data = src.read_bytes() if src.is_file() else None
    prepped = prepare_input(src_data, "mv")[0] \
        if src_data is not None else None
    model_rel = rec.get("model_path")
    model_path = Path(model_rel) if model_rel else None
    if model_path is not None and not model_path.is_absolute():
        model_path = REPO / model_path
    model_sha = file_sha256(model_path) \
        if model_path is not None and model_path.is_file() else None
    placeholder = "{INPUT}"
    return {
        "version": VALIDATION_IDENTITY_VERSION,
        "instance": rec["instance"],
        "producer": rec.get("solver"),
        "track": "mv",
        "timeout_s": int(wall_cap),
        "resource_envelope": resource_envelope,
        "producer_run_cache_key": rec.get("run_cache_key"),
        "source_sha256": (hashlib.sha256(src_data).hexdigest()
                          if src_data is not None else None),
        "materialized_sha256": (hashlib.sha256(prepped).hexdigest()
                                if prepped is not None else None),
        "materialization_version": MATERIALIZATION_VERSION["mv"],
        "model_sha256": model_sha,
        "validator_config": {
            "binary": known_dolmen_identity or path_identity(dolmen),
            "time_budget": time_budget,
            "size_budget": size_budget,
            "normal_argv": dolmen_argv(
                dolmen, placeholder, time_budget, size_budget, False
            ),
            "retry_argv": dolmen_argv(
                dolmen, placeholder, time_budget, size_budget, True
            ),
            "stdin": "{MODEL}",
        },
    }


def run_dolmen(dolmen: Path, bench: str, model_path: Path, time_budget: str,
               size_budget: str, wall_cap: int, force_logic_all: bool,
               resource_envelope: dict) -> dict:
    memlimit_mb = int(resource_envelope["memlimit_mb"])
    argv = dolmen_argv(dolmen, bench, time_budget, size_budget,
                       force_logic_all)
    res = run_process(Invocation(argv, stdin_path=str(model_path)), wall_cap,
                      resource_envelope=resource_envelope)
    stderr = res.stderr_tail
    code = res.exit_code
    if res.memout:
        status = V_MEMOUT
    elif res.timed_out:
        status = V_TIMEOUT
    elif res.spawn_error:
        status = V_UNKNOWN
        stderr = res.spawn_error
    else:
        status = dolmen_status(code if code is not None else -1,
                               stderr.encode("utf-8"))
    return {
        "status": status,
        "dolmen_exit": code,
        "dolmen_stderr": stderr,
        "dolmen_wall_sec": round(res.wall_sec, 3),
        "dolmen_memout": res.memout,
        "dolmen_timed_out": res.timed_out,
        "validator_memlimit_mb": memlimit_mb,
    }


def validate_mv_one(dolmen: Path, rec: dict, tmpdir: str, time_budget: str,
                    size_budget: str, wall_cap: int, resource_envelope: dict,
                    known_dolmen_identity: dict | None = None) -> dict:
    validation_identity = make_mv_validation_identity(
        dolmen, rec, time_budget, size_budget, wall_cap, resource_envelope,
        known_dolmen_identity,
    )
    out = {"instance": rec["instance"], "solver": rec["solver"],
           "answer": rec.get("answer"),
           "dolmen_binary": str(dolmen),
           "dolmen_time_budget": time_budget,
           "dolmen_size_budget": size_budget,
           "validation_wall_cap_s": wall_cap,
           "validation_resource_envelope": resource_envelope,
           "validator_memlimit_mb": resource_envelope["memlimit_mb"],
           "validation_identity": validation_identity,
           "validation_cache_key": identity_key(validation_identity)}
    model_path = None
    if rec.get("model_path"):
        mp = Path(rec["model_path"])
        model_path = mp if mp.is_absolute() else REPO / mp
    if model_path is None or not model_path.is_file():
        out.update(status="MissingModelFile", dolmen_exit=None,
                   dolmen_stderr="", dolmen_wall_sec=0.0)
        return out
    out["model_sha256"] = file_sha256(model_path)
    if validation_identity.get("model_sha256") != out["model_sha256"]:
        out.update(status="ArtifactChanged", dolmen_exit=None,
                   dolmen_stderr="model changed during validation setup",
                   dolmen_wall_sec=0.0)
        return out
    src = BENCH_ROOT / rec["instance"]
    if not src.is_file():
        out.update(status="MissingBenchmark", dolmen_exit=None,
                   dolmen_stderr="", dolmen_wall_sec=0.0)
        return out
    tmp, _, _ = materialize(src, "mv", tmpdir)
    try:
        if (validation_identity.get("source_sha256") != file_sha256(src)
                or validation_identity.get("materialized_sha256")
                != file_sha256(Path(tmp))):
            out.update(status="ArtifactChanged", dolmen_exit=None,
                       dolmen_stderr="benchmark changed during validation setup",
                       dolmen_wall_sec=0.0)
            return out
        res = run_dolmen(dolmen, tmp, model_path, time_budget, size_budget,
                         wall_cap, force_logic_all=False,
                         resource_envelope=resource_envelope)
        # 2025 retry rule (check_result_locally): an error whose stderr is
        # exactly "E:forbidden-array-sort\n" is re-checked with
        # --force-smtlib2-logic=ALL; the retried result stands.
        if res["dolmen_stderr"] == "E:forbidden-array-sort\n":
            res = run_dolmen(dolmen, tmp, model_path, time_budget, size_budget,
                             wall_cap, force_logic_all=True,
                             resource_envelope=resource_envelope)
            res["retried_force_logic"] = True
        out.update(res)
        return out
    finally:
        try:
            os.unlink(tmp)
        except OSError:
            pass


def load_validation(tag_dir: Path, solver: str) -> dict[str, dict]:
    return load_done(tag_dir / "validation" / f"{solver}.jsonl")


def load_current_mv_validation(tag_dir: Path, solver: str,
                               recs: dict[str, dict]) -> tuple[dict[str, dict], int]:
    """Validation rows matching the exact current model artifact.

    Legacy rows without a model hash and rows for overwritten models are
    intentionally not accepted.  A bad-model verdict is score-critical, so
    matching by instance alone would let a later model inherit either a point
    or an error from unrelated bytes.
    """
    rows = load_rows(tag_dir / "validation" / f"{solver}.jsonl")
    by_key: dict[tuple[str, str | None], dict] = {}
    instances_with_rows: set[str] = set()
    for row in rows:
        instance = row["instance"]
        instances_with_rows.add(instance)
        if "model_sha256" in row:
            by_key[(instance, row.get("model_sha256"))] = row

    current: dict[str, dict] = {}
    stale = 0
    for instance, rec in recs.items():
        if rec.get("answer") != "sat":
            continue
        row = by_key.get((instance, model_file_hash(rec)))
        if (row is not None and validation_matches_run(row, rec)
                and validation_matches_artifact(row)):
            current[instance] = row
        elif instance in instances_with_rows:
            stale += 1
    return current, stale


def cmd_validate_mv(args: argparse.Namespace) -> None:
    dolmen = find_dolmen()
    if dolmen is None or not dolmen.is_file():
        raise SystemExit("pinned Dolmen not found — set DOLMEN_BIN or install "
                         ".competitors/dolmen/dolmen (see PROVENANCE.txt)")
    tag_dir = results_dir("mv", args.division, args.tag)
    files = sorted(f for f in tag_dir.glob("*.jsonl"))
    if args.solvers:
        keep = {s.strip() for s in args.solvers.split(",")}
        files = [f for f in files if f.stem in keep]
    if not files:
        raise SystemExit(f"no mv result files under {tag_dir}")

    # Dolmen processes used to bypass both RAM-aware admission and the RSS
    # watchdog.  Its generous 40G internal size budget is per process and
    # cannot safely be multiplied by an unchecked --jobs value.
    warn_concurrent_build()
    requested_jobs = args.jobs
    plan = plan_solver_resources(requested_jobs,
                                 label="smtcomp_harness.py validate-mv")
    jobs = plan.jobs
    resource_envelope = make_resource_envelope(requested_jobs, plan)
    if jobs < requested_jobs:
        print(f"[validate-mv] OOM GUARD: --jobs {requested_jobs} -> {jobs} "
              f"(RAM budget; see scripts/_oom_guard.py)")
    dolmen_identity = path_identity(dolmen)
    print(f"[validate-mv] dolmen: {dolmen} (--time={args.dolmen_time} "
          f"--size={args.dolmen_size}, wall cap {args.wall_cap}s, "
          f"jobs={jobs}/{requested_jobs}, memlimit={plan.memlimit_mb}MB/child, "
          f"NBCORE={plan.nbcore}, headroom={plan.headroom_mb}MB)")
    tmpdir = tempfile.mkdtemp(prefix=f"smtcomp-mvval-{args.tag}-")
    try:
        for f in files:
            solver = f.stem
            recs = load_done(f)
            sat_rows = [r for r in recs.values() if r.get("answer") == "sat"]
            vpath = tag_dir / "validation" / f"{solver}.jsonl"
            if args.overwrite and vpath.exists():
                vpath.unlink()
            done_keys: set[str] = set()
            done_insts: set[str] = set()
            for row in load_rows(vpath):
                done_insts.add(row["instance"])
                recorded_identity = row.get("validation_identity")
                key = row.get("validation_cache_key")
                if (isinstance(recorded_identity, dict)
                        and key == identity_key(recorded_identity)
                        and validation_matches_artifact(row)):
                    done_keys.add(key)
            expected_keys = {
                r["instance"]: identity_key(make_mv_validation_identity(
                    dolmen, r, args.dolmen_time, args.dolmen_size,
                    args.wall_cap, resource_envelope, dolmen_identity,
                ))
                for r in sat_rows
            }
            todo = [r for r in sat_rows
                    if expected_keys[r["instance"]] not in done_keys]
            stale = sum(1 for r in todo if r["instance"] in done_insts)
            print(f"[validate-mv] {solver}: {len(recs)} runs, {len(sat_rows)} sat, "
                  f"{len(todo)} to validate ({len(done_keys)} cached"
                  + (f", {stale} stale artifact/config rows superseded"
                     if stale else "")
                  + ")")
            if not todo:
                continue
            vpath.parent.mkdir(parents=True, exist_ok=True)
            lock = threading.Lock()
            completed = 0
            t0 = time.monotonic()
            with vpath.open("a") as fh, ThreadPoolExecutor(max_workers=jobs) as pool:
                futs = [pool.submit(validate_mv_one, dolmen, r, tmpdir,
                                    args.dolmen_time, args.dolmen_size,
                                    args.wall_cap, resource_envelope,
                                    dolmen_identity)
                        for r in todo]
                for fut in as_completed(futs):
                    vrec = fut.result()
                    with lock:
                        fh.write(json.dumps(vrec) + "\n")
                        fh.flush()
                        completed += 1
                        if completed % 50 == 0 or completed == len(todo):
                            rate = completed / max(time.monotonic() - t0, 1e-9)
                            eta = (len(todo) - completed) / max(rate, 1e-9)
                            print(f"[validate-mv] {solver}: {completed}/{len(todo)} "
                                  f"({rate:.2f}/s, eta {eta/60:.1f}m)", flush=True)
            vrecs = load_validation(tag_dir, solver)
            tally: dict[str, int] = {}
            for v in vrecs.values():
                tally[v["status"]] = tally.get(v["status"], 0) + 1
            print(f"[validate-mv] {solver}: " +
                  ", ".join(f"{k}={v}" for k, v in sorted(tally.items())))
            if tally.get(V_UNKNOWN):
                print(f"[validate-mv] WARNING: {solver} has {tally[V_UNKNOWN]} "
                      f"UnknownValidatorError result(s) — the 2025 pipeline would "
                      f"have crashed on these; inspect dolmen_stderr", file=sys.stderr)
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)
    print(f"[validate-mv] validation records in {tag_dir / 'validation'}")


# ---------------------------------------------------------------------------
# score subcommand — 2025 semantics


def _expected_tokens(expected: object) -> list[str]:
    if expected is None:
        return []
    if isinstance(expected, list):
        return [str(t) for t in expected]
    return [t for t in re.split(r"[,;\s]+", str(expected)) if t]


def judge_mv(rec: dict, vstatus: str | None) -> tuple[int, int]:
    """2025 mv (e, n) — smtcomp/scoring.py ModelValidation case.

    error = ANY unsat answer (every 2025 MV benchmark is known sat) or a
    Dolmen E:bad-model (ModelUnsat); point ONLY for a Dolmen-validated sat.
    Everything else (parse error, partial function, validator timeout,
    unknown, no answer) = 0 points, no error."""
    ans = rec.get("answer")
    if ans == "unsat":
        return 1, 0
    if ans == "sat":
        if vstatus == V_OK:
            return 0, 1
        if vstatus == V_MODEL_UNSAT:
            return 1, 0
        return 0, 0
    return 0, 0


def judge(track: str, rec: dict) -> tuple[int, int]:
    """Per-benchmark (e, n) before the virtual time limit is applied.

    e=1 iff a definite answer contradicts a definite expected status.
    sq: n=1 for an uncontradicted definite answer. (uc does NOT route through
    here: it has its own reduction scoring in _score_uc; mv uses judge_mv.)
    inc: any wrong token in the answered prefix => e=1, n=0; else n = number
    of definite tokens not contradicted by the expected sequence."""
    if track == "inc":
        answers = [t for t in (rec.get("answer") or "").split(",") if t]
        exp = _expected_tokens(rec.get("expected"))
        n = 0
        for i, tok in enumerate(answers):
            if tok not in ("sat", "unsat"):
                continue
            if i < len(exp) and exp[i] in ("sat", "unsat") and tok != exp[i]:
                return 1, 0
            n += 1
        return 0, n
    ans = rec.get("answer")
    exp = rec.get("expected")
    if ans in ("sat", "unsat"):
        if exp in ("sat", "unsat") and ans != exp:
            return 1, 0
        return 0, 1
    return 0, 0


def _score_uc(args: argparse.Namespace, tag_dir: Path,
              by_solver: dict[str, dict[str, dict]], vlimit: int,
              run_resource_envelope: dict, run_timeout_s: int) -> None:
    """UnsatCore reduction scoring, 2025 semantics with error demotion.

    reduction = #named-asserts - |core| is credited ONLY for cores the
    validators declared valid (see cmd_validate_uc). Unvalidated, empty,
    missing cores and legacy skipped-full rows score 0. Every invalidated core is an
    error: e >= 1 ranks the solver below every 0-error solver regardless of
    reduction (one invalidated core forfeits the win — hence the harness-side
    fail-closed discipline). Wrong answers (sat on expected-unsat) are errors
    too. Sequential reduction applies the virtual limit to cpu time, parallel
    to wall time; errors stand regardless of time.

    Validation rows are joined by (instance, core-hash) and exact producer-run
    identity — a row for different bytes or conditions is STALE and scores
    nothing (U4 review F1). Pre-fix rows without an identity are rejected."""
    # (instance, core_sha256) -> row.
    val_by_key: dict[str, dict[tuple[str, str | None], dict]] = {}
    val_insts: dict[str, set[str]] = {}
    for s in by_solver:
        val_by_key[s] = {}
        val_insts[s] = set()
        for row in load_rows(validation_path(tag_dir, s)):
            inst = row["instance"]
            val_insts[s].add(inst)
            if "core_sha256" in row or row.get("status") == "no_core":
                val_by_key[s][(inst, row.get("core_sha256"))] = row
    # Effective (current-core-matched) validation row per instance — also
    # feeds the gap list below.
    val_effective: dict[str, dict[str, dict]] = {s: {} for s in by_solver}
    board: dict[str, dict] = {}
    for sname, recs in by_solver.items():
        b = {"instances": len(recs), "errors": 0, "wrong_answers": 0,
             "answered_unsat": 0, "validated": 0, "invalidated": 0,
             "unvalidated": 0, "no_core": 0, "skipped_full_core": 0,
             "stale_validation": 0,
             "seq_reduction": 0, "par_reduction": 0,
             "seq_time": 0.0, "par_time": 0.0,
             "timeouts": sum(1 for r in recs.values() if r.get("timed_out")),
             "unknowns": sum(1 for r in recs.values()
                             if (r.get("answer") or "") not in ("sat", "unsat"))}
        for inst, rec in recs.items():
            ans = rec.get("answer")
            exp = rec.get("expected")
            if ans in ("sat", "unsat") and exp in ("sat", "unsat") and ans != exp:
                b["errors"] += 1
                b["wrong_answers"] += 1
                continue
            if ans != "unsat":
                continue
            b["answered_unsat"] += 1
            v = val_by_key[sname].get((inst, core_file_hash(rec)))
            if (v is not None
                    and (not validation_matches_run(v, rec)
                         or not validation_matches_artifact(v))):
                v = None
            if v is None:
                if inst in val_insts[sname]:
                    # Rows exist but none matches the CURRENT core: stale.
                    b["stale_validation"] += 1
                b["unvalidated"] += 1  # 0 points
                continue
            val_effective[sname][inst] = v
            st = v.get("status")
            if st == "valid":
                red = int(v.get("reduction") or 0)
                # Fail-closed guard (cannot fire if validate-uc is honest):
                # an empty core must never earn reduction.
                if v.get("core_names", 0) == 0 and v.get("n_asserts", 0) > 0:
                    red = 0
                b["validated"] += 1
                cpu = rec.get("cpu_sec")
                cpu = cpu if cpu is not None else rec.get("wall_sec", 0.0)
                wall = rec.get("wall_sec", 0.0)
                if cpu <= vlimit:
                    b["seq_reduction"] += red
                    b["seq_time"] += cpu
                if wall <= vlimit:
                    b["par_reduction"] += red
                    b["par_time"] += wall
            elif st in ("invalidated", "invalid_names"):
                b["invalidated"] += 1
                b["errors"] += 1  # error demotion; stands regardless of time
            elif st == "no_core":
                b["no_core"] += 1
            elif st == "skipped_full_core":
                b["skipped_full_core"] += 1  # reduction 0 by construction
            else:  # unvalidated / no_validator
                b["unvalidated"] += 1
        b["seq_time"] = round(b["seq_time"], 3)
        b["par_time"] = round(b["par_time"], 3)
        board[sname] = b

    validation_resource_envelope = require_comparable_validation_conditions(
        val_effective, "uc"
    )

    seq_rank = sorted(board, key=lambda s: (board[s]["errors"],
                                            -board[s]["seq_reduction"],
                                            board[s]["seq_time"]))
    par_rank = sorted(board, key=lambda s: (board[s]["errors"],
                                            -board[s]["par_reduction"],
                                            board[s]["par_time"]))

    # Addressable frontier: instances the best non-AY solver got validated
    # reduction on while ay did not (or less), largest reduction first.
    # Uses only current-core and producer-run-matched validation rows.
    gap_solver = next((s for s in seq_rank if s != "ay"), None)
    gap_list = []
    if gap_solver and "ay" in board:
        ay_v = val_effective.get("ay", {})
        for inst, v in val_effective.get(gap_solver, {}).items():
            if v.get("status") != "valid":
                continue
            theirs = int(v.get("reduction") or 0)
            av = ay_v.get(inst)
            ours = int(av.get("reduction") or 0) if av and av.get("status") == "valid" else 0
            if theirs > ours:
                gap_list.append({"instance": inst, "solver": gap_solver,
                                 "reduction": theirs, "ay_reduction": ours})
        gap_list.sort(key=lambda g: -g["reduction"])

    scoreboard = {
        "competition": "SMT-COMP 2025 (retroactive restage)",
        "track": "uc", "division": args.division, "tag": args.tag,
        "timeout_virtual": vlimit,
        "run_timeout_s": run_timeout_s,
        "run_resource_envelope": run_resource_envelope,
        "validation_resource_envelope": validation_resource_envelope,
        "run_memlimit_mb": run_resource_envelope.get("memlimit_mb", 0),
        "validator_memlimit_mb": validation_resource_envelope.get(
            "memlimit_mb", 0
        ),
        "solvers": board,
        "ranking_sequential": seq_rank,
        "ranking_parallel": par_rank,
        "gap_solver": gap_solver,
        "gap_list": gap_list,
        "notes": "uc reduction scoring: reduction = named asserts - |core|, "
                 "credited ONLY for validator-confirmed cores (#unsat > #sat); "
                 "invalidated core or wrong answer => error demotion below all "
                 "0-error solvers; empty/unvalidated/missing cores score 0; "
                 "seq caps cpu, par caps wall; errors stand regardless of time",
    }
    out = tag_dir / "scoreboard.json"
    out.write_text(json.dumps(scoreboard, indent=2))

    print(f"\n## SMT-COMP 2025 restage — UnsatCore / {args.division} [{args.tag}] "
          f"(virtual limit {vlimit}s)\n")
    print("| # | solver | errors | seq reduction | par reduction | answered unsat "
          "| validated | invalidated | unvalidated | no core | full-core skipped | run |")
    print("|---|--------|--------|---------------|---------------|----------------"
          "|-----------|-------------|-------------|---------|-------------------|-----|")
    for i, s in enumerate(seq_rank, 1):
        b = board[s]
        print(f"| {i} | {s} | {b['errors']} | {b['seq_reduction']} "
              f"| {b['par_reduction']} | {b['answered_unsat']} | {b['validated']} "
              f"| {b['invalidated']} | {b['unvalidated']} | {b['no_core']} "
              f"| {b['skipped_full_core']} | {b['instances']} |")
    print(f"\nsequential ranking: {' > '.join(seq_rank)}")
    print(f"parallel ranking:   {' > '.join(par_rank)}")
    for s in seq_rank:
        if board[s]["errors"]:
            print(f"!! {s}: {board[s]['errors']} error(s) "
                  f"({board[s]['wrong_answers']} wrong answer(s), "
                  f"{board[s]['invalidated']} invalidated core(s)) — demoted "
                  f"below every 0-error solver")
        if board[s]["stale_validation"]:
            print(f"!! {s}: {board[s]['stale_validation']} STALE validation "
                  f"row(s) ignored (core changed since validation — re-run "
                  f"validate-uc; scored as unvalidated, 0 points)")
    unval = {s: board[s]["unvalidated"] for s in seq_rank if board[s]["unvalidated"]}
    if unval:
        print(f"note: unvalidated cores score 0 — run validate-uc first "
              f"({unval})")
    if gap_solver:
        print(f"\nGAP LIST vs {gap_solver} (validated reduction ay lacks): "
              f"{len(gap_list)} instance(s)")
        for g in gap_list[:20]:
            print(f"   {g['reduction']:>10}  (ay {g['ay_reduction']:>10})  {g['instance']}")
        if len(gap_list) > 20:
            print(f"   ... {len(gap_list) - 20} more in scoreboard.json")
    print(f"\nscoreboard: {out}")


def cmd_score(args: argparse.Namespace) -> None:
    track = args.track
    vlimit = args.timeout_virtual
    tag_dir = results_dir(track, args.division, args.tag)
    files = sorted(tag_dir.glob("*.jsonl"))
    if args.solvers:
        keep = {s.strip() for s in args.solvers.split(",")}
        files = [f for f in files if f.stem in keep]
    if not files:
        raise SystemExit(f"no result files under {tag_dir}")

    by_solver: dict[str, dict[str, dict]] = {f.stem: load_done(f) for f in files}
    run_resource_envelope, run_timeout_s = require_comparable_run_conditions(
        by_solver
    )
    if track == "uc":
        _score_uc(args, tag_dir, by_solver, vlimit, run_resource_envelope,
                  run_timeout_s)
        return

    # mv: scoring REQUIRES the validate-mv pass — a point exists only for a
    # Dolmen-validated sat, and an unvalidated model could conceal the
    # score-critical ModelUnsat verdict.  Fail closed on missing or stale rows.
    validations: dict[str, dict[str, dict]] = {}
    val_tally: dict[str, dict[str, int]] = {}
    validation_resource_envelope: dict = {}
    if track == "mv":
        unvalidated: dict[str, int] = {}
        stale_validation: dict[str, int] = {}
        for sname, recs in by_solver.items():
            validations[sname], stale = load_current_mv_validation(
                tag_dir, sname, recs
            )
            if stale:
                stale_validation[sname] = stale
            val_tally[sname] = {}
            miss = sum(1 for inst, rec in recs.items()
                       if rec.get("answer") == "sat"
                       and inst not in validations[sname])
            if miss:
                unvalidated[sname] = miss
        if unvalidated:
            detail = ", ".join(f"{s}: {n}" for s, n in sorted(unvalidated.items()))
            stale_detail = ("; stale model-validation rows: "
                            + ", ".join(f"{s}: {n}" for s, n in
                                        sorted(stale_validation.items()))) \
                if stale_validation else ""
            raise SystemExit(
                f"mv scoring needs dolmen validation for every sat answer; "
                f"unvalidated sat rows: {detail}{stale_detail}. "
                f"Run `validate-mv --division "
                f"{args.division} --tag {args.tag}` first "
                f"under the current model artifacts and envelope.")
        validation_resource_envelope = require_comparable_validation_conditions(
            validations, "mv"
        )

    board: dict[str, dict] = {}
    seq_solved: dict[str, dict[str, dict]] = {}  # solver -> instance -> rec (seq-counted)
    for sname, recs in by_solver.items():
        errors = seq_n = par_n = 0
        seq_time = par_time = 0.0
        raw_n = 0
        seq_solved[sname] = {}
        for inst, rec in recs.items():
            if track == "mv":
                v = validations.get(sname, {}).get(inst)
                vstatus = (v["status"] if v else
                           V_NOT_VALIDATED if rec.get("answer") == "sat" else None)
                if vstatus is not None:
                    val_tally[sname][vstatus] = val_tally[sname].get(vstatus, 0) + 1
                e, n = judge_mv(rec, vstatus)
            else:
                e, n = judge(track, rec)
            errors += e
            raw_n += n
            cpu = rec.get("cpu_sec")
            cpu = cpu if cpu is not None else rec.get("wall_sec", 0.0)
            wall = rec.get("wall_sec", 0.0)
            # SEQUENTIAL: the solve is zeroed if CPU exceeds the virtual
            # limit; the error stands regardless (a wrong answer is a wrong
            # answer whenever it arrives).
            if n and cpu <= vlimit:
                seq_n += n
                seq_time += cpu
                seq_solved[sname][inst] = rec
            # PARALLEL: wall-clock against the same virtual limit.
            if n and wall <= vlimit:
                par_n += n
                par_time += wall
        board[sname] = {
            "instances": len(recs),
            "errors": errors,
            "seq_solved": seq_n,
            "seq_time": round(seq_time, 3),
            "_seq_time_raw": seq_time,
            "par_solved": par_n,
            "par_time": round(par_time, 3),
            "_par_time_raw": par_time,
            "raw_solved_uncapped": raw_n,
            "timeouts": sum(1 for r in recs.values() if r.get("timed_out")),
            "unknowns": sum(1 for r in recs.values()
                            if (r.get("answer") or "").split(",")[0] not in ("sat", "unsat")),
        }
        if track == "mv":
            board[sname]["validation"] = dict(sorted(val_tally[sname].items()))
            board[sname]["unsat_answers"] = sum(
                1 for r in recs.values() if r.get("answer") == "unsat")

    seq_rank = sorted(board, key=lambda s: (board[s]["errors"], -board[s]["seq_solved"],
                                            board[s]["_seq_time_raw"]))
    par_rank = sorted(board, key=lambda s: (board[s]["errors"], -board[s]["par_solved"],
                                            board[s]["_par_time_raw"]))
    for b in board.values():  # raw sort keys don't belong in scoreboard.json
        del b["_seq_time_raw"], b["_par_time_raw"]

    # Cross-solver disagreement on expected=unknown instances: any sat-vs-unsat
    # pair between two solvers is a soundness flag.
    disagreements = []
    all_inst = sorted({i for recs in by_solver.values() for i in recs})
    for inst in all_inst:
        if track == "inc":
            per = {s: (r[inst].get("answer") or "").split(",")
                   for s, r in by_solver.items() if inst in r}
            exp = _expected_tokens(next(iter(
                by_solver[s][inst].get("expected") for s in per if inst in by_solver[s])))
            maxlen = max((len(t) for t in per.values()), default=0)
            conflict = {}
            for i in range(maxlen):
                if i < len(exp) and exp[i] in ("sat", "unsat"):
                    continue  # only unknown-status positions
                at_i = {s: t[i] for s, t in per.items()
                        if i < len(t) and t[i] in ("sat", "unsat")}
                if len(set(at_i.values())) > 1:
                    conflict[f"check-sat #{i + 1}"] = at_i
            if conflict:
                disagreements.append({"instance": inst, "answers": conflict})
        else:
            exp = next((by_solver[s][inst].get("expected")
                        for s in by_solver if inst in by_solver[s]), None)
            if exp in ("sat", "unsat"):
                continue
            answers = {s: r[inst]["answer"] for s, r in by_solver.items()
                       if inst in r and r[inst].get("answer") in ("sat", "unsat")}
            if len(set(answers.values())) > 1:
                disagreements.append({"instance": inst, "answers": answers})

    # GAP LIST: what the best non-AY solver solved (sequentially) that ay did
    # not — the addressable frontier, easiest first (that solver's wall time).
    gap_list = []
    gap_solver = next((s for s in seq_rank if s != "ay"), None)
    if gap_solver:
        ay_solved = set(seq_solved.get("ay", {}))
        for inst, rec in seq_solved[gap_solver].items():
            if inst not in ay_solved:
                gap_list.append({"instance": inst, "solver": gap_solver,
                                 "answer": rec.get("answer"),
                                 "wall_sec": rec.get("wall_sec"),
                                 "cpu_sec": rec.get("cpu_sec")})
        gap_list.sort(key=lambda g: g["wall_sec"] or 0.0)

    scoreboard = {
        "competition": "SMT-COMP 2025 (retroactive restage)",
        "track": track, "division": args.division, "tag": args.tag,
        "timeout_virtual": vlimit,
        "run_timeout_s": run_timeout_s,
        "run_resource_envelope": run_resource_envelope,
        "validation_resource_envelope": (
            validation_resource_envelope if track == "mv" else None
        ),
        "run_memlimit_mb": run_resource_envelope.get("memlimit_mb", 0),
        "validator_memlimit_mb": (
            validation_resource_envelope.get("memlimit_mb", 0)
            if track == "mv" else None
        ),
        "solvers": board,
        "ranking_sequential": seq_rank,
        "ranking_parallel": par_rank,
        "disagreements_on_unknown": disagreements,
        "gap_solver": gap_solver,
        "gap_list": gap_list,
        "notes": "seq zeroes solves with cpu>vlimit (errors stand); "
                 + ("mv: point = dolmen-validated sat only; error = unsat "
                    "answer or ModelUnsat (2025 scoring.py); parse/partial/"
                    "validator-timeout = 0 points, no error"
                    if track == "mv" else
                    "sq/inc answer-level scoring "
                    "(uc has its own reduction scoring path)"),
    }
    out = tag_dir / "scoreboard.json"
    out.write_text(json.dumps(scoreboard, indent=2))

    # Markdown table
    print(f"\n## SMT-COMP 2025 restage — {TRACKS[track]} / {args.division} [{args.tag}] "
          f"(virtual limit {vlimit}s)\n")
    print("| # | solver | errors | seq solved | seq time (s) | par solved | par time (s) | unknown/none | timeouts | run |")
    print("|---|--------|--------|------------|--------------|------------|--------------|--------------|----------|-----|")
    for i, s in enumerate(seq_rank, 1):
        b = board[s]
        print(f"| {i} | {s} | {b['errors']} | {b['seq_solved']} | {b['seq_time']} "
              f"| {b['par_solved']} | {b['par_time']} | {b['unknowns']} "
              f"| {b['timeouts']} | {b['instances']} |")
    if track == "mv":
        print("\nvalidation breakdown (per solver):")
        for s in seq_rank:
            b = board[s]
            parts = ", ".join(f"{k}={v}" for k, v in b.get("validation", {}).items())
            print(f"   {s}: {parts or '(no sat answers)'}"
                  + (f"; unsat answers={b['unsat_answers']}" if b.get("unsat_answers") else ""))
    print(f"\nsequential ranking: {' > '.join(seq_rank)}")
    print(f"parallel ranking:   {' > '.join(par_rank)}")
    if disagreements:
        print(f"\n!! {len(disagreements)} sat-vs-unsat disagreement(s) on "
              f"expected=unknown instances:")
        for d in disagreements[:20]:
            print(f"   {d['instance']}: {d['answers']}")
        if len(disagreements) > 20:
            print(f"   ... {len(disagreements) - 20} more in scoreboard.json")
    if gap_solver:
        print(f"\nGAP LIST vs {gap_solver} (solved by {gap_solver}, missed by ay): "
              f"{len(gap_list)} instance(s)")
        for g in gap_list[:20]:
            print(f"   {g['wall_sec']:>9.3f}s  {g['answer']:>6}  {g['instance']}")
        if len(gap_list) > 20:
            print(f"   ... {len(gap_list) - 20} more in scoreboard.json")
    print(f"\nscoreboard: {out}")


# ---------------------------------------------------------------------------
# registry subcommand


def cmd_registry(args: argparse.Namespace) -> None:
    sdir = submissions_dir()
    print(f"submissions dir: {sdir or 'MISSING (using frozen 2025 command table)'}")
    dolmen = find_dolmen()
    print(f"dolmen (mv):     "
          f"{dolmen if dolmen and dolmen.is_file() else 'MISSING (set DOLMEN_BIN)'}")
    print(f"bench root:      {BENCH_ROOT}"
          + ("" if BENCH_ROOT.is_dir() else "  [MISSING — set SMTCOMP_BENCH_ROOT]"))
    registry = build_registry()
    for name, sol in registry.items():
        status = "ok" if sol.available else "MISSING"
        print(f"  {name:12s} [{status:7s}] {sol.binary}"
              + (f" (java={sol.java})" if sol.kind == "jar" else ""))
        if sol.note:
            print(f"  {'':12s} note: {sol.note}")
        if sol.submission:
            for tr in TRACKS:
                cmd = extract_2025_command(sol.submission, tr, "QF_UF")
                if cmd:
                    print(f"  {'':12s} 2025 {tr}: {cmd}")


# ---------------------------------------------------------------------------


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    rp = sub.add_parser("run", help="run solvers on a division selection")
    rp.add_argument("--track", required=True, choices=sorted(TRACKS))
    rp.add_argument("--division", required=True)
    rp.add_argument("--solvers", default="ay,z3")
    rp.add_argument("--timeout", type=int, default=1200)
    rp.add_argument("--jobs", type=int, default=2)
    rp.add_argument("--tag", required=True, help="run label, e.g. probe120, full1200")
    rp.add_argument("--limit", type=int, default=0, help="only first N instances")
    rp.add_argument("--only", default="", help="regex filter on instance relpath")
    rp.add_argument("--sample", type=int, default=0, help="stratified sample of N")
    rp.add_argument("--seed", type=int, default=2025)
    rp.add_argument("--overwrite", action="store_true",
                    help="discard existing results for the selected solvers")
    rp.add_argument("--dry-run", action="store_true",
                    help="print argv + temp file for the first instance and exit")
    rp.set_defaults(func=cmd_run)

    vp = sub.add_parser("validate-uc",
                        help="validate captured unsat cores (2025 rules)")
    vp.add_argument("--division", required=True)
    vp.add_argument("--tag", required=True)
    vp.add_argument("--solvers", default="",
                    help="restrict to these core-producing solvers")
    vp.add_argument("--validators", default="cvc5,smtinterpol",
                    help="comma list of validating solvers (SQ configs); a "
                         "solver is never its own validator")
    vp.add_argument("--timeout", type=int, default=1200,
                    help="per-validator timeout on the reduced benchmark")
    vp.add_argument("--jobs", type=int, default=2)
    vp.add_argument("--limit", type=int, default=0,
                    help="validate at most N cores per solver this invocation")
    vp.add_argument("--overwrite", action="store_true",
                    help="discard existing validation rows for selected solvers")
    vp.set_defaults(func=cmd_validate_uc)

    mvp = sub.add_parser("validate-mv",
                         help="dolmen-validate recorded mv models (exact 2025 pipeline)")
    mvp.add_argument("--division", required=True)
    mvp.add_argument("--tag", required=True)
    mvp.add_argument("--solvers", default="", help="restrict to these solvers")
    mvp.add_argument("--jobs", type=int, default=2)
    mvp.add_argument("--dolmen-time", default="1h",
                     help="dolmen --time budget (2025: 1h)")
    mvp.add_argument("--dolmen-size", default="40G",
                     help="dolmen --size budget (2025: 40G)")
    mvp.add_argument("--wall-cap", type=int, default=3700,
                     help="harness kill for a dolmen run (s); maps to "
                          "ModelValidatorTimeout")
    mvp.add_argument("--overwrite", action="store_true",
                     help="discard existing validation records for the selected solvers")
    mvp.set_defaults(func=cmd_validate_mv)

    sp = sub.add_parser("score", help="2025-semantics scoreboard for a tag")
    sp.add_argument("--track", required=True, choices=sorted(TRACKS))
    sp.add_argument("--division", required=True)
    sp.add_argument("--tag", required=True)
    sp.add_argument("--solvers", default="", help="restrict to these solvers")
    sp.add_argument("--timeout-virtual", type=int, default=1200)
    sp.set_defaults(func=cmd_score)

    gp = sub.add_parser("registry", help="show solver availability + 2025 commands")
    gp.set_defaults(func=cmd_registry)

    args = ap.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
