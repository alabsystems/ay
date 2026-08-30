#!/usr/bin/env python3
"""Score a `pb_cert_cli_ab_run.sh` sweep: coverage per arm, and the head-to-head.

The coverage DENOMINATOR is stated, per binary, exactly as the census states it:
instances the SAME binary's no-proof arm answered `s OPTIMUM FOUND` at the same
budget. A ratio whose denominator came from a different binary, or from the proof
arm itself (which is fail-closed and downgrades), is not a coverage figure.

Exit 2 if any arm file is missing or empty: a harness that measured NOTHING must
never report "0 fail".

Usage: pb_cert_cli_ab_analyze.py <data-dir> <budget_ms> [out.json]
"""
import json
import os
import sys
from collections import OrderedDict

COLS = ["path", "arm", "budget", "status", "obj", "wall_ms", "bytes", "lines",
        "sha256", "route", "checker_exit", "verdict", "want", "score"]


def load(path):
    rows = {}
    with open(path) as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line:
                continue
            f = line.split("\t")
            if len(f) != len(COLS):
                raise SystemExit(f"malformed row in {path}: {len(f)} fields")
            rows[f[0]] = dict(zip(COLS, f))
    return rows


def main():
    if len(sys.argv) < 3:
        raise SystemExit(__doc__)
    data, budget = sys.argv[1], sys.argv[2]
    out_path = sys.argv[3] if len(sys.argv) > 3 else None

    arms = {}
    for name in sorted(os.listdir(data)):
        if not name.endswith(f"-{budget}.tsv"):
            continue
        arm = name[: -len(f"-{budget}.tsv")]
        arms[arm] = load(os.path.join(data, name))
    if not arms:
        print(f"ERROR: no arm files in {data} for budget {budget}", file=sys.stderr)
        raise SystemExit(2)
    for arm, rows in arms.items():
        if not rows:
            print(f"ERROR: arm {arm} measured nothing", file=sys.stderr)
            raise SystemExit(2)

    report = OrderedDict()
    report["arms_rows_on_disk"] = {a: len(r) for a, r in arms.items()}

    # EVERY NUMBER BELOW IS ON THE COMMON SET. A sweep can be interrupted, and
    # an arm that has more rows than another would otherwise be compared against
    # a different denominator. Restricting to the instances every arm measured
    # is what makes a partial sweep still an honest A/B rather than a mixture.
    common = set.intersection(*(set(r) for r in arms.values()))
    for arm in arms:
        arms[arm] = {p: r for p, r in arms[arm].items() if p in common}
    report["measured_in_every_arm"] = len(common)
    if not common:
        print("ERROR: no instance was measured in every arm", file=sys.stderr)
        raise SystemExit(2)

    # ---- coverage, per binary key, denominator = that binary's own noproof arm
    cov = OrderedDict()
    for arm in sorted(arms):
        if not arm.endswith("-proof"):
            continue
        key = arm[: -len("-proof")]
        den_arm = f"{key}-noproof"
        proof = arms[arm]
        den = arms.get(den_arm)
        solved = None
        if den is not None:
            solved = {p for p, r in den.items() if r["status"] == "OPTIMUM FOUND"}
        verified = {p for p, r in proof.items() if r["score"] == "VERIFIED"}
        rejects = {p for p, r in proof.items() if r["score"] == "REJECT"}
        wrong = {p for p, r in proof.items() if r["score"] == "WRONG-CONCLUSION"}
        sat = {p for p, r in proof.items() if r["status"] == "SATISFIABLE"}
        unk = {p for p, r in proof.items() if r["status"] == "UNKNOWN"}
        entry = OrderedDict(
            measured=len(proof),
            verified=len(verified),
            rejects=len(rejects),
            wrong_conclusion=len(wrong),
            proof_mode_satisfiable=len(sat),
            proof_mode_unknown=len(unk),
        )
        if solved is not None:
            entry["denominator_noproof_optimum"] = len(solved)
            inside = verified & solved
            entry["verified_inside_denominator"] = len(inside)
            entry["coverage"] = f"{len(inside)}/{len(solved)}"
            entry["coverage_pct"] = round(100.0 * len(inside) / len(solved), 1) if solved else None
            entry["verified_outside_denominator"] = sorted(verified - solved)
        cov[arm] = entry
    report["coverage"] = cov

    # ---- head to head between every pair of proof arms
    h2h = OrderedDict()
    proof_arms = [a for a in sorted(arms) if a.endswith("-proof")]
    for i, a in enumerate(proof_arms):
        for b in proof_arms[i + 1:]:
            ra, rb = arms[a], arms[b]
            both = sorted(set(ra) & set(rb))
            va = {p for p in both if ra[p]["score"] == "VERIFIED"}
            vb = {p for p in both if rb[p]["score"] == "VERIFIED"}
            disagree = [p for p in both
                        if ra[p]["status"] == rb[p]["status"] == "OPTIMUM FOUND"
                        and ra[p]["obj"] != rb[p]["obj"]]
            h2h[f"{a}|{b}"] = OrderedDict(
                measured_in_both=len(both),
                verified_a_only=sorted(va - vb),
                verified_b_only=sorted(vb - va),
                verified_both=len(va & vb),
                optimum_disagreements=disagree,
            )
    report["head_to_head"] = h2h

    # ---- every VERIFIED row, verbatim verdict, so the table is auditable
    rowsout = []
    for arm in proof_arms:
        for p, r in sorted(arms[arm].items()):
            if r["score"] in ("VERIFIED", "REJECT", "WRONG-CONCLUSION"):
                rowsout.append(OrderedDict(arm=arm, instance=os.path.basename(p),
                                           status=r["status"], obj=r["obj"],
                                           bytes=int(r["bytes"]), wall_ms=int(r["wall_ms"]),
                                           checker_exit=r["checker_exit"],
                                           verdict=r["verdict"], score=r["score"]))
    report["scored_rows"] = rowsout

    text = json.dumps(report, indent=2)
    if out_path:
        with open(out_path, "w") as fh:
            fh.write(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
