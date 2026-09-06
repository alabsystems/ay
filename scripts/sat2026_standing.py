#!/usr/bin/env python3
"""The ONE per-instance standing for the SAT-COMP 2026 campaign.

WHY THIS EXISTS. The campaign's evidence is spread across a 1500 s sweep, an
on-menu VeriPB re-screen with three confirmation phases, a fair-budget pass in
banked batches, and an UNSAT banking file — and every number this campaign has
had to retract came from joining those by hand. This script does the join ONCE,
per instance, with the counting rules stated in code:

  * A SAT verdict counts when the sweep validated the model (models are
    self-certifying; the sweep cross-checks against ground truth and this
    script re-checks that no counted verdict contradicts truth).
  * An UNSAT verdict counts ONLY with an accepted on-menu VeriPB certificate —
    from the HEAD re-screen, a confirmation phase, an uncapped settlement, or
    the banking file. dsr-trim acceptance is OFF-MENU and never counts here.
  * A converted-but-uncertified UNSAT is PENDING, never blended into the
    standing.
  * A verdict contradicting ground truth ABORTS the script. Zero wrong answers
    is a harder requirement than any score.

Budgets are reported side by side and never mixed into one number silently:
the 1500 s standing and the official-limits (5000 s / 32 GB) standing are
different claims about different budgets.

Usage:
    python3 scripts/sat2026_standing.py [--bench-dir ~/ay-bench] [--tsv out.tsv]
"""

import argparse
import glob
import json
import os
import sys

TRUTH = os.path.join(os.path.dirname(__file__), "..",
                     "benchmarks", "sat", "satcomp2026-main-truth.json")


def load_truth():
    with open(TRUTH) as f:
        t = json.load(f)
    return {h: e for h, e in t["instances_by_hash"].items()}


def read_tsv(path, key=0):
    rows = {}
    if not os.path.exists(path):
        return rows
    with open(path) as f:
        for line in f:
            if line.startswith("#"):
                continue
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 2 or parts[0] == "cnf":
                continue
            rows[parts[key].replace(".cnf", "")] = parts
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bench-dir", default=os.path.expanduser("~/ay-bench"))
    ap.add_argument("--tsv", help="write the per-instance table here")
    args = ap.parse_args()
    b = args.bench_dir

    truth = load_truth()

    # ---- verdict sources -------------------------------------------------
    # 1500 s head sweep: the settled base standing.
    head = json.load(open(os.path.join(b, "proofmode-head-1500s.json")))
    base = {r["cnf"].replace(".cnf", ""): r for r in head["results"]}

    # Fair-budget conversions at the official limits (memout slice + batches).
    fair = {}
    for p in [os.path.join(b, "fairbudget-memouts-5000s.json")] + \
             sorted(glob.glob(os.path.join(b, "fairbudget", "batch*.json"))):
        if not os.path.exists(p):
            continue
        d = json.load(open(p))
        for r in d["results"]:
            h = r["cnf"].replace(".cnf", "")
            if r["verdict"] in ("sat", "unsat"):
                fair[h] = (r["verdict"], r["time"], os.path.basename(p))

    # ---- on-menu VeriPB acceptance sources ------------------------------
    # Verified rows from the capped HEAD re-screen and phase-3 confirmation.
    onmenu = set()
    for name, col in [("veripb-onmenu-screen-HEAD.tsv", 2),
                      ("veripb-onmenu-confirm-phase3.tsv", 2)]:
        for h, parts in read_tsv(os.path.join(b, name)).items():
            if len(parts) > col and parts[col] == "verified":
                onmenu.add(h)
    # Uncapped settlements (provenance in the file itself).
    sp = os.path.join(b, "veripb-uncapped-settlements.json")
    if os.path.exists(sp):
        s = json.load(open(sp))
        onmenu.update(h for h in s if not h.startswith("_"))
    # The banking file: official-limit re-solves checked uncapped.
    banked = set()
    # One banking file per (solver, checker) identity pair: round 1 ran the
    # pre-fix solver against the 95563a89 pin; round 2 re-solves late
    # conversions with the family-3-fixed binary. Same schema, same rules.
    for bank_name in ("bank-unsat-veripb.tsv", "bank-unsat-veripb2.tsv"):
        for h, parts in read_tsv(os.path.join(b, bank_name)).items():
            if len(parts) >= 7 and parts[4] == "0" and "VERIFIED" in parts[6]:
                banked.add(h)
    onmenu |= banked

    # ---- the join, with the counting rules ------------------------------
    counted_1500, counted_official = set(), set()
    pending_unsat, wrong = [], []
    rows = []
    for h, e in truth.items():
        tr = e.get("truth")
        base_r = base.get(h)
        base_v = base_r["verdict"] if base_r else None
        fair_v = fair.get(h)

        def check_truth(v, src):
            if tr in ("sat", "unsat") and v in ("sat", "unsat") and v != tr:
                wrong.append((h, v, tr, src))

        status, budget = "unsolved", ""
        if base_v in ("sat", "unsat"):
            check_truth(base_v, "1500s")
            if base_v == "sat" or h in onmenu:
                status, budget = f"counted-{base_v}", "1500s"
                counted_1500.add(h)
                counted_official.add(h)
            else:
                status, budget = "pending-unsat-cert", "1500s"
                pending_unsat.append((h, "1500s"))
        elif fair_v:
            v, t, src = fair_v
            check_truth(v, src)
            if v == "sat" or h in onmenu:
                status, budget = f"counted-{v}", "official-5000s"
                counted_official.add(h)
            else:
                status, budget = "pending-unsat-cert", "official-5000s"
                pending_unsat.append((h, src))
        rows.append((h, e.get("name", ""), tr, status, budget))

    if wrong:
        for h, v, tr, src in wrong:
            print(f"WRONG ANSWER: {h} claimed {v}, truth {tr} (source {src})",
                  file=sys.stderr)
        sys.exit(2)

    n1500 = len(counted_1500)
    noff = len(counted_official)
    print("SAT-COMP 2026 standing (counting rules in the docstring; "
          "zero tolerance for truth contradictions — enforced, none found)")
    print(f"  1500 s standing            : {n1500}/400")
    print(f"  official-limits standing   : {noff}/400   (5000 s / 32 GB where re-measured)")
    print(f"  pending UNSAT certificates : {len(pending_unsat)}  "
          f"(converted, awaiting on-menu VeriPB acceptance — NEVER blended)")
    print(f"  winner's bar               : 276")
    for h, src in pending_unsat:
        print(f"    pending: {h[:16]}  ({src})")

    if args.tsv:
        with open(args.tsv, "w") as f:
            f.write("instance\tname\ttruth\tstatus\tbudget\n")
            for r in rows:
                f.write("\t".join(str(x) for x in r) + "\n")
        print(f"per-instance table -> {args.tsv}")


if __name__ == "__main__":
    main()
