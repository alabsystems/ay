#!/usr/bin/env python3
"""Re-derive every number in the `13.5x per-node throughput` block from its own data.

the development design notes:26` records

    Gurobi finishes at the ROOT (<=1 node)  :  23 of 37  (62%)  -- ay needs 9,929 nodes
    ay finishes at the ROOT (<=1 node)      :   9        (24%)  -- gurobi needs 33,534
    both actually branch                    :  12
    node ratio ay/gurobi  geomean 4.85x  median 3.35x
    node throughput : ay 53 nodes/s vs gurobi 717 nodes/s -> gurobi 13.5x faster per node

and commits NO computation for it. The data survives (the development design notes,
154 rows from `milp_w0.py par --tier gurobi --secs 20 --threads 1,8`). This script
is that computation, written after the fact, so the block can be checked rather
than quoted.

WHAT IT FINDS. Five of the six lines reproduce exactly. `median 3.35x` reproduces
only under an upper-median convention (`sorted[n//2]`); `statistics.median` gives
2.79x. And `53 vs 717 nodes/s` reproduces under NO subset x estimator combination
this script sweeps -- the natural aggregations of the same 37 rows put ay between
0.66x and 1.33x of Gurobi, not 1/13.5x.

Run: python3 scripts/audit_p0_node_throughput.py [path/to/p0-par-corpus.json]
"""
import json, math, os, statistics as st, sys

PROVED = {"OPTIMAL", "INFEASIBLE"}


def load(path):
    rows = json.load(open(path))["rows"]
    out = []
    for r in rows:
        a = r.get("ay_1t") or {}
        g = (r.get("gurobi") or {}).get("1") or {}
        g8 = (r.get("gurobi") or {}).get("8") or {}
        if a.get("nodes") is None or g.get("nodes") is None:
            continue
        out.append((r["name"], a, g, g8))
    return out


def geo(v):
    return math.exp(sum(map(math.log, v)) / len(v)) if v else float("nan")


def harm(v):
    return len(v) / sum(1.0 / x for x in v) if v else float("nan")


def main(path):
    allr = load(path)
    both = [x for x in allr
            if x[1].get("status") in PROVED and x[2].get("status") in PROVED]
    gr_root = [x for x in both if x[2]["nodes"] <= 1]
    ay_root = [x for x in both if x[1]["nodes"] <= 1]
    bb = [x for x in both if x[1]["nodes"] > 1 and x[2]["nodes"] > 1]

    print("== THE STRUCTURAL LINES (all reproduce) ==")
    print("  both prove and both report nodes : %d   [recorded 37]" % len(both))
    print("  gurobi <=1 node                  : %d   ay nodes there %d   [recorded 23 / 9,929]"
          % (len(gr_root), sum(x[1]["nodes"] for x in gr_root)))
    print("  ay <=1 node                      : %d   gurobi nodes there %d  [recorded 9 / 33,534]"
          % (len(ay_root), sum(x[2]["nodes"] for x in ay_root)))
    print("  both branch                      : %d   [recorded 12]" % len(bb))
    rat = [x[1]["nodes"] / x[2]["nodes"] for x in bb]
    srt = sorted(rat)
    print("  node ratio geomean %.2fx [recorded 4.85x] | median %.2fx [recorded 3.35x, "
          "which is sorted[n//2] = %.2fx]" % (geo(rat), st.median(rat), srt[len(srt) // 2]))

    print("\n== THE DOUBLE COUNT IN THE 62%% HEADLINE ==")
    ov = sorted(set(x[0] for x in gr_root) & set(x[0] for x in ay_root))
    print("  instances where BOTH finish at the root: %d  %s" % (len(ov), ov))
    print("  gurobi-at-root AND ay-branches : %d of %d = %.0f%%  (not 62%%)"
          % (len(gr_root) - len(ov), len(both), 100 * (len(gr_root) - len(ov)) / len(both)))
    print("  ay-at-root AND gurobi-branches : %d of %d = %.0f%%  (not 24%%)"
          % (len(ay_root) - len(ov), len(both), 100 * (len(ay_root) - len(ov)) / len(both)))

    print("\n== THE THROUGHPUT LINE: SWEEP FOR 'ay 53 n/s vs gurobi 717 n/s' ==")
    subsets = {
        "both proved (37)": both,
        "both branch (12)": bb,
        "gurobi root (23)": gr_root,
        "gurobi branches": [x for x in both if x[2]["nodes"] > 1],
        "ALL rows (151)": allr,
    }
    ests = {
        "total n/total t": lambda n, t: sum(n) / sum(t),
        "mean of rates": lambda n, t: sum(a / b for a, b in zip(n, t)) / len(n),
        "median of rates": lambda n, t: st.median([a / b for a, b in zip(n, t)]),
        "geomean of rates": lambda n, t: geo([a / b for a, b in zip(n, t)]),
        "harmonic of rates": lambda n, t: harm([a / b for a, b in zip(n, t)]),
    }
    best = None
    for sn, s in subsets.items():
        for gi, glab in ((2, "grb-1T"), (3, "grb-8T")):
            for floor in (1, 2):
                sel = [x for x in s
                       if x[1]["nodes"] >= floor and (x[gi].get("nodes") or 0) >= floor
                       and (x[1].get("t") or 0) > 0 and (x[gi].get("t") or 0) > 0]
                if len(sel) < 3:
                    continue
                an = [x[1]["nodes"] for x in sel]; at = [x[1]["t"] for x in sel]
                gn = [x[gi]["nodes"] for x in sel]; gt = [x[gi]["t"] for x in sel]
                for en, f in ests.items():
                    A, G = f(an, at), f(gn, gt)
                    r = G / A
                    print("  %-18s %-7s floor=%d %-18s n=%3d  ay %10.1f  gurobi %10.1f  -> %6.2fx"
                          % (sn, glab, floor, en, len(sel), A, G, r))
                    if best is None or r > best[0]:
                        best = (r, sn, glab, floor, en)
    print("\n  LARGEST ay-unfavourable ratio anywhere in the sweep: %.2fx  (%s, %s, floor=%d, %s)"
          % best)

    print("\n== WHAT THE ONLY ~13x ESTIMATOR IS ACTUALLY MEASURING ==")
    print("  harmonic mean of per-instance rates = n / SUM(t_i/n_i): the denominator IS")
    print("  the sum of per-node costs, so each instance is weighted by its own per-node cost.")
    for who, i in (("ay", 1), ("gurobi", 2)):
        tot = sum(x[i]["t"] / x[i]["nodes"] for x in bb)
        top = max(bb, key=lambda x: x[i]["t"] / x[i]["nodes"])
        share = 100 * (top[i]["t"] / top[i]["nodes"]) / tot
        print("  %-7s harmonic %7.1f n/s   TOP CONTRIBUTOR %s = %.1f%% of the statistic "
              "(%d nodes)" % (who, len(bb) / tot, top[0], share, top[i]["nodes"]))

    print("\n== THE HONEST PAIRED MEASURE: per-node cost where both actually branch ==")
    bb2 = sorted(bb, key=lambda x: x[1]["nodes"])
    print("  %-20s %9s %11s %11s %8s" % ("instance", "ay nodes", "ay us/node", "grb us/node", "ratio"))
    for n, a, g, _ in bb2:
        print("  %-20s %9d %11.1f %11.1f %8.2f"
              % (n, a["nodes"], a["t"] / a["nodes"] * 1e6, g["t"] / g["nodes"] * 1e6,
                 (a["t"] / a["nodes"]) / (g["t"] / g["nodes"])))
    v = [(a["t"] / a["nodes"]) / (g["t"] / g["nodes"]) for _, a, g, _ in bb2]
    print("  geomean %.2fx  median %.2fx  over %d" % (geo(v), st.median(v), len(v)))
    for lo, hi, lab in ((0, 1000, "ay nodes < 1,000"), (1000, 10 ** 12, "ay nodes >= 1,000")):
        s = [x for x in bb2 if lo <= x[1]["nodes"] < hi]
        vv = [(a["t"] / a["nodes"]) / (g["t"] / g["nodes"]) for _, a, g, _ in s]
        print("    %-18s n=%d  geomean %.2fx" % (lab, len(s), geo(vv)))
    print("  The ratio falls monotonically with tree size because ay's FIXED per-solve cost")
    print("  (parse, presolve, root LP, root cuts, exact rim) is being divided by node count.")

    print("\n== FIXED vs MARGINAL: least squares t = fixed + marginal * nodes ==")
    def fit(pts):
        n = len(pts); sx = sum(p[0] for p in pts); sy = sum(p[1] for p in pts)
        sxx = sum(p[0] ** 2 for p in pts); sxy = sum(p[0] * p[1] for p in pts)
        b = (n * sxy - sx * sy) / (n * sxx - sx * sx)
        return (sy - b * sx) / n, b
    for lab, s in (("all 37 both-proved", both), ("12 both-branch", bb)):
        aa, ab = fit([(x[1]["nodes"], x[1]["t"]) for x in s])
        ga, gb = fit([(x[2]["nodes"], x[2]["t"]) for x in s])
        print("  %-20s ay %.3fs + %7.2f us/node | gurobi %.3fs + %7.2f us/node "
              "| fixed %.1fx, marginal %.2fx" % (lab, aa, ab * 1e6, ga, gb * 1e6, aa / ga, ab / gb))
    print("  CAVEAT: the fit is leverage-dominated by mas76/pk1 (the two largest trees).")
    print("  Read it as: the large gap is in the FIXED term, not the marginal one.")


if __name__ == "__main__":
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "reports", "p0-par-corpus.json"))
