#!/usr/bin/env python3
# ay-script: satcomp2026-score
"""Score a local sweep against the official SAT-COMP 2026 Main Track results.

The 2026 competition published per-instance runtimes for all 31 solvers, so a
local run on the same 400 instances can be checked for *correctness* against
ground truth and compared, family by family, with the official field.

What this does NOT do: promote a local time to an official score. This box is
not HoreKa, and the local timeout is not 5000 s. Every table here is labelled
with the local timeout it was produced at, and the official columns are only
ever shown alongside, never merged.

Usage:
  sat2026_score.py sweep_results.json [--truth benchmarks/sat/satcomp2026-main-truth.json]
                                      [--solver ay] [--top 12]
"""
import argparse, collections, json, os, re, sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_TRUTH = os.path.join(REPO, "benchmarks", "sat", "satcomp2026-main-truth.json")


def family(name):
    """Leading alphabetic token of the instance name, the coarse family key."""
    m = re.match(r"[A-Za-z_]+", name)
    return m.group(0).strip("_") if m else name[:8]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sweep", help="sweep.py results JSON")
    ap.add_argument("--truth", default=DEFAULT_TRUTH)
    ap.add_argument("--solver", action="append", default=[],
                    help="restrict to these sweep solver names (default: all)")
    ap.add_argument("--top", type=int, default=12, help="official solvers to list")
    ap.add_argument("--families", type=int, default=15)
    args = ap.parse_args()

    sweep = json.load(open(args.sweep))
    truth = json.load(open(args.truth))
    by_hash = truth["instances_by_hash"]
    timeout = sweep["timeout_s"]

    solvers = args.solver or sorted({r["solver"] for r in sweep["results"]})
    print(f"official set: {truth['track']} ({truth['instances']} instances, "
          f"{truth['timeout_s']} s official timeout)")
    print(f"local sweep : {args.sweep}  timeout {timeout} s  "
          f"workers {sweep.get('workers')}  (local box, NOT official hardware)\n")

    wrong_total = 0
    for name in solvers:
        rs = [r for r in sweep["results"] if r["solver"] == name]
        solved = wrong = unmapped = 0
        sat = unsat = 0
        par2 = 0.0
        wrongs = []
        for r in rs:
            h = os.path.basename(r["cnf"])[:-4]
            meta = by_hash.get(h)
            if meta is None:
                unmapped += 1
            v = r["verdict"]
            if v in ("sat", "unsat"):
                solved += 1
                sat += v == "sat"
                unsat += v == "unsat"
                par2 += r["time"]
                if meta and meta["truth"] in ("sat", "unsat") and meta["truth"] != v:
                    wrong += 1
                    wrongs.append((meta["name"], v, meta["truth"]))
            else:
                par2 += 2 * timeout
        wrong_total += wrong
        print(f"{name:12s} solved {solved:3d}/{len(rs)} (sat {sat} unsat {unsat})  "
              f"PAR-2@{timeout:g}s sum {par2:>10.1f}  mean {par2/max(1,len(rs)):>8.1f}"
              + (f"  UNMAPPED {unmapped}" if unmapped else ""))
        if wrong:
            print(f"  *** {wrong} WRONG ANSWERS vs official ground truth "
                  f"(competition-disqualifying) ***")
            for n, got, want in wrongs[:10]:
                print(f"      {n}: reported {got}, official {want}")

    print("\n--- official field (5000 s, HoreKa; for reference only) ---")
    for row in truth["field"][:args.top]:
        print(f"  {row['par2_mean']:>8.2f} mean PAR-2  {row['solved']:3d} solved  "
              f"{row['solver']}")

    # Family view: where does the local solver stand against the winner?
    if solvers:
        primary = solvers[0]
        rs = {os.path.basename(r["cnf"])[:-4]: r
              for r in sweep["results"] if r["solver"] == primary}
        fams = collections.defaultdict(lambda: [0, 0, 0, 0])  # n, local, winner, vbs
        for h, meta in by_hash.items():
            f = family(meta["name"])
            fams[f][0] += 1
            r = rs.get(h)
            if r and r["verdict"] in ("sat", "unsat"):
                fams[f][1] += 1
            fams[f][2] += bool(meta["winner_solved"])
            fams[f][3] += bool(meta["n_solved"])
        print(f"\n--- families: {primary}@{timeout:g}s vs official winner@5000s vs VBS ---")
        ranked = sorted(fams.items(), key=lambda kv: (-(kv[1][2] - kv[1][1]), -kv[1][0]))
        print(f"  {'family':28s} {'n':>3} {'local':>6} {'winner':>7} {'vbs':>4}")
        for f, (n, loc, win, vbs) in ranked[:args.families]:
            print(f"  {f:28s} {n:3d} {loc:6d} {win:7d} {vbs:4d}")

    if wrong_total:
        print(f"\nFAIL: {wrong_total} wrong answer(s) — a single one is a "
              f"competition disqualification.")
        return 1
    print("\nno wrong answers against official ground truth")
    return 0


if __name__ == "__main__":
    sys.exit(main())
