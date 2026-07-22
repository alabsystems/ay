#!/usr/bin/env python3
# ay-script: rewrite-oracle-build
"""Regenerate the fast-core rewrite golden oracle from AY's harness results.

Harvests every definitive, non-placeholder (instance, verdict) AY produced
across evals/results/chccomp-harness/20*/, resolves each to a concrete .smt2,
and writes evals/results/rewrite-oracle/golden_verdicts.jsonl. Cross-run
disagreements are excluded (should be zero given AY's zero-wrong discipline).
"""
import json, glob, os

BENCH = "benchmarks/chc"
OUT = "evals/results/rewrite-oracle/golden_verdicts.jsonl"


def build_index():
    idx = {}
    for dp, _, fs in os.walk(BENCH):
        if "worktree" in dp:
            continue
        for f in fs:
            if f.endswith(".smt2"):
                idx.setdefault(f, os.path.join(dp, f))
    return idx


def main():
    idx = build_index()

    def resolve(year, inst):
        rel = inst.lstrip("./")
        if rel.endswith(".yml"):
            rel = rel[:-4] + ".smt2"
        p = os.path.join(BENCH, f"chc-comp{year[-2:]}-benchmarks", rel)
        if os.path.exists(p):
            return p
        return idx.get(os.path.basename(rel))

    golden, conflict = {}, 0
    for f in glob.glob("evals/results/chccomp-harness/20*/**/ay.jsonl", recursive=True):
        year = "2025" if "/2025/" in f else "2026"
        for line in open(f):
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
            except Exception:
                continue
            if r.get("status") in ("sat", "unsat") and not r.get("placeholder_verdict", False):
                sm = resolve(year, r["instance"])
                if not sm:
                    continue
                if sm in golden and golden[sm] != r["status"]:
                    golden[sm] = "CONFLICT"
                    conflict += 1
                elif sm not in golden:
                    golden[sm] = r["status"]
    golden = {k: v for k, v in golden.items() if v != "CONFLICT"}
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as w:
        for sm, v in sorted(golden.items()):
            w.write(json.dumps({"smt2": sm, "verdict": v}) + "\n")
    sat = sum(1 for v in golden.values() if v == "sat")
    print(f"{len(golden)} instances (sat {sat}, unsat {len(golden)-sat}), {conflict} conflicts excluded -> {OUT}")


if __name__ == "__main__":
    main()
