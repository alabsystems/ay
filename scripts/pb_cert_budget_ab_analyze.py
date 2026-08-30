#!/usr/bin/env python3
"""Score a `pb_cert_budget_ab_run.sh` sweep.

Coverage is a RATIO and the denominator is not the proof arm: in proof mode AY
is fail-closed and downgrades an uncertifiable `s OPTIMUM FOUND` to
`s SATISFIABLE`, so scoring the proof arm against itself divides the certified
count by itself. The denominator is the NOPROOF arm's optima at the same budget.

Exits 2 when an arm is missing or empty. A harness that measured nothing must
not print a clean summary of nothing.
"""

import json
import sys
from pathlib import Path

ARMS = ["base-noproof", "base-proof", "head-proof", "head-noproof"]


def read_arm(outdir: Path, label: str, arm: str) -> dict:
    path = outdir / f"{label}-{arm}.tsv"
    if not path.exists() or path.stat().st_size == 0:
        print(f"ERROR: arm file '{path}' is missing or empty", file=sys.stderr)
        sys.exit(2)
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        f = line.split("\t")
        rows[f[0]] = {
            "status": f[3],
            "objective": f[4],
            "wall_ms": int(f[5]),
            "proof_bytes": int(f[6]),
            "proof_lines": int(f[7]),
            "route": f[9],
            "verdict": f[11],
            "score": f[13],
        }
    return rows


def main() -> None:
    outdir = Path(sys.argv[1])
    label = sys.argv[2]
    arms = {a: read_arm(outdir, label, a) for a in ARMS}

    common = set(arms[ARMS[0]])
    for a in ARMS[1:]:
        common &= set(arms[a])
    if not common:
        print("ERROR: the arms share no instance; nothing was measured", file=sys.stderr)
        sys.exit(2)

    base_opt = {i for i in common if arms["base-noproof"][i]["status"] == "OPTIMUM FOUND"}
    head_opt = {i for i in common if arms["head-noproof"][i]["status"] == "OPTIMUM FOUND"}
    base_cert = {i for i in common if arms["base-proof"][i]["score"] == "VERIFIED"}
    head_cert = {i for i in common if arms["head-proof"][i]["score"] == "VERIFIED"}

    def alarms(arm):
        return sorted(i for i in common if arms[arm][i]["score"] in ("REJECT", "WRONG-CONCLUSION"))

    report = {
        "label": label,
        "instances_in_every_arm": len(common),
        "denominator_base_noproof_optima": len(base_opt),
        "denominator_head_noproof_optima": len(head_opt),
        "denominator_moved": sorted(base_opt ^ head_opt),
        "base_certified": len(base_cert),
        "head_certified": len(head_cert),
        "base_coverage_of_solved": f"{len(base_cert & base_opt)}/{len(base_opt)}",
        "head_coverage_of_solved": f"{len(head_cert & base_opt)}/{len(base_opt)}",
        "head_only_certified": sorted(head_cert - base_cert),
        "base_only_certified": sorted(base_cert - head_cert),
        "soundness_alarms_base": alarms("base-proof"),
        "soundness_alarms_head": alarms("head-proof"),
    }

    # Incumbent quality: capping the native phase must not cost `o` lines on the
    # instances neither arm certifies. Lower objective is better (min form).
    worse, better = [], []
    for i in sorted(common):
        b, h = arms["base-proof"][i], arms["head-proof"][i]
        if b["objective"] in ("-", "") or h["objective"] in ("-", ""):
            if b["objective"] not in ("-", "") and h["objective"] in ("-", ""):
                worse.append((i, b["objective"], "none"))
            elif h["objective"] not in ("-", "") and b["objective"] in ("-", ""):
                better.append((i, "none", h["objective"]))
            continue
        bo, ho = int(b["objective"]), int(h["objective"])
        if ho > bo:
            worse.append((i, bo, ho))
        elif ho < bo:
            better.append((i, bo, ho))
    report["proof_arm_incumbent_worse_in_head"] = worse
    report["proof_arm_incumbent_better_in_head"] = better

    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
