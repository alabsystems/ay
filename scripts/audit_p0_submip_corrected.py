#!/usr/bin/env python3
# ay-script: audit-p0-submip-corrected
"""Re-derive the P0 ay-vs-Gurobi node figures with a GUROBI-COMPARABLE node count.

THE ASYMMETRY. the development design notes
compares `ay_milp::nodes_explored()` against Gurobi's `Model.NodeCount`. Those are
not the same quantity: ay's counter is process-global and cumulative across
RENS/RINS sub-MIP trees, Gurobi's excludes the sub-MIPs its heuristics run. The
bias runs in BOTH directions off a single per-instance number

    r = root_nodes / total_nodes   in (0, 1]

because the recorded statistics are built from the same two counts:

    tree-quality ratio  = ay_nodes / grb_nodes        -> multiplied by r  (FALLS)
    ay per-node cost    = ay_wall  / ay_nodes         -> divided by r     (RISES)

So the correction makes ay's trees look BETTER and ay's per-node cost look WORSE,
by the same factor, on the same instance. Neither direction may be applied alone.

WHY ay's WALL IS NOT ALSO SPLIT. Gurobi's `Runtime` includes the time its
heuristics spend inside their sub-MIPs while `NodeCount` excludes those nodes; its
per-node cost is therefore "all of the time, over main-tree nodes only". The
comparable ay quantity is the same shape — total wall over root nodes — so the
correction is exactly "divide by r", with no time reattributed.

INPUTS
  the development design notes     the committed P0 run (ay 1T + Gurobi 1T/8T)
  --share <json>                 output of scripts/milp_submip_share.py, which
                                 measures r per instance. Use the arm built from
                                 the SAME commit that produced the P0 run
                                 (f6b5028f6); today's engine is a different
                                 engine and its r describes today, not July.

Run: python3 scripts/audit_p0_submip_corrected.py --share the development design notes
"""
from __future__ import annotations

import argparse
import json
import math
import os
import statistics as st

PROVED = {"OPTIMAL", "INFEASIBLE"}


def geo(v):
    return math.exp(sum(map(math.log, v)) / len(v)) if v else float("nan")


def load_p0(path):
    rows = json.load(open(path))["rows"]
    out = []
    for r in rows:
        a = r.get("ay_1t") or {}
        g = (r.get("gurobi") or {}).get("1") or {}
        if a.get("nodes") is None or g.get("nodes") is None:
            continue
        out.append((r["name"], a, g))
    return out


def load_share(path, arm):
    """Per-instance r = root/total, one value per rep, plus a summary.

    Reps are kept and reported; the point estimate is the MEDIAN of the reps,
    which is the load-robust choice on a box shared with other agents.
    """
    d = json.load(open(path))
    runs = d["runs"]
    out = {}
    for name, byarm in runs.items():
        recs = byarm.get(arm) or []
        rs, tot, sub = [], [], []
        for rec in recs:
            t = rec.get("total_nodes")
            if t is None or t == 0:
                continue
            rs.append(rec["root_nodes"] / t)
            tot.append(t)
            sub.append(rec["submip_nodes"])
        if rs:
            out[name] = {"reps": rs, "r": st.median(rs), "totals": tot, "submips": sub,
                         "statuses": [rec.get("status") for rec in recs]}
    return out, d


def fmt_stats(label, v):
    if not v:
        return f"  {label:34s} n=0"
    return (f"  {label:34s} n={len(v):3d}  geomean {geo(v):7.3f}x  "
            f"median {st.median(v):7.3f}x  min {min(v):6.3f}x  max {max(v):8.2f}x")


def main():
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    ap = argparse.ArgumentParser()
    ap.add_argument("--p0", default=os.path.join(here, "reports", "p0-par-corpus.json"))
    ap.add_argument("--share", required=True)
    ap.add_argument("--arm", default="july")
    ap.add_argument("--json-out", default=None)
    args = ap.parse_args()

    allr = load_p0(args.p0)
    share, sharedoc = load_share(args.share, args.arm)
    print(f"P0 rows with both node counts: {len(allr)}")
    print(f"share arm '{args.arm}' = {sharedoc['arms'][args.arm]}")
    print(f"instances with a measured r:   {len(share)}")

    # ---------------------------------------------------------------- 1. the split
    print("\n== 1. SUB-MIP SHARE OF `nodes_explored()`, arm=%s ==" % args.arm)
    withtree = {k: v for k, v in share.items() if max(v["totals"]) > 0}
    rs = [v["r"] for v in withtree.values()]
    print(f"  instances with a non-empty tree: {len(withtree)}")
    print(f"  root share r: geomean {geo(rs):.4f}  median {st.median(rs):.4f}  "
          f"min {min(rs):.4f}  max {max(rs):.4f}")
    for thr in (1.0, 0.99, 0.95, 0.90, 0.75, 0.50):
        n = sum(1 for r in rs if r >= thr)
        print(f"    r >= {thr:.2f} : {n:3d} / {len(rs)}  ({100 * n / len(rs):5.1f}%)")
    worst = sorted(withtree.items(), key=lambda kv: kv[1]["r"])[:12]
    print("  the twelve largest sub-MIP shares (1 - r):")
    for name, v in worst:
        print(f"    {name:26s} r={v['r']:.4f}  submip share {1 - v['r']:.4f}  "
              f"reps r={['%.4f' % x for x in v['reps']]}  totals={v['totals']}")
    # Rep-to-rep stability of r itself: the correction is only as good as this.
    spread = [max(v["reps"]) - min(v["reps"]) for v in withtree.values() if len(v["reps"]) > 1]
    if spread:
        print(f"  rep spread of r (max-min), n={len(spread)}: "
              f"median {st.median(spread):.5f}  p90 {sorted(spread)[int(0.9 * len(spread))]:.5f}  "
              f"max {max(spread):.5f}")
    # SPLIT BY TERMINATION. A run that hit the wall budget has a load-dependent node
    # count, so its r is a property of this box's load as well as of the search; a run
    # that PROVED ran the whole search and its r is a property of the search alone.
    # The re-derived comparisons use only the proved population.
    for lab, keep in (("PROVED (terminated)", lambda s: s in PROVED),
                      ("hit the budget", lambda s: s not in PROVED)):
        sel = [v["r"] for v in withtree.values()
               if v["statuses"] and keep(v["statuses"][0])]
        if sel:
            print(f"  {lab:22s} n={len(sel):3d}  r geomean {geo(sel):.4f}  "
                  f"median {st.median(sel):.4f}  "
                  f"share with r < 0.99: {sum(1 for x in sel if x < 0.99)}")

    # ---------------------------------------------------------------- 2. re-derive
    both = [x for x in allr if x[1].get("status") in PROVED and x[2].get("status") in PROVED]
    print("\n== 2. THE RECORDED SUBSET (both prove, both report nodes) ==")
    print(f"  n = {len(both)}  [recorded 37]")
    missing = [x[0] for x in both if x[0] not in share]
    if missing:
        print(f"  WITHOUT a measured r (excluded from the corrected figures): {missing}")

    def corrected_nodes(name, a):
        r = share.get(name, {}).get("r")
        return None if r is None else a["nodes"] * r

    bb_old = [x for x in both if x[1]["nodes"] > 1 and x[2]["nodes"] > 1]
    rat_old = [x[1]["nodes"] / x[2]["nodes"] for x in bb_old]
    print("\n== 3. TREE QUALITY where both branch ==")
    print(fmt_stats("AS RECORDED (cumulative nodes)", rat_old))
    # Corrected. Membership is recomputed, because a corrected count can drop to
    # <= 1 node and leave the "both branch" set — reported, never hidden.
    bb_new, dropped = [], []
    for x in both:
        cn = corrected_nodes(x[0], x[1])
        if cn is None:
            continue
        if cn > 1 and x[2]["nodes"] > 1:
            bb_new.append((x[0], cn, x[2]["nodes"]))
        elif x[1]["nodes"] > 1 and x[2]["nodes"] > 1:
            dropped.append((x[0], cn))
    rat_new = [cn / gn for _, cn, gn in bb_new]
    print(fmt_stats("CORRECTED (root nodes only)", rat_new))
    if dropped:
        print(f"  left the 'both branch' set under correction: {dropped}")
    # Same membership, so the movement is not a sample change.
    paired = [(x[0], x[1]["nodes"] / x[2]["nodes"],
               corrected_nodes(x[0], x[1]) / x[2]["nodes"])
              for x in bb_old if corrected_nodes(x[0], x[1]) is not None]
    if paired:
        print(fmt_stats("CORRECTED, membership frozen", [p[2] for p in paired]))
        movers = sorted(paired, key=lambda p: p[2] / p[1])[:8]
        print("  instances the correction moves most:")
        for name, o, n in movers:
            print(f"    {name:26s} {o:9.2f}x -> {n:9.2f}x   (x{n / o:.4f})")

    print("\n== 4. PER-NODE COST where both branch ==")
    pn_old = [(x[1]["t"] / x[1]["nodes"]) / (x[2]["t"] / x[2]["nodes"]) for x in bb_old]
    print(fmt_stats("AS RECORDED (cumulative nodes)", pn_old))
    pn_new = [(x[1]["t"] / corrected_nodes(x[0], x[1])) / (x[2]["t"] / x[2]["nodes"])
              for x in bb_old if corrected_nodes(x[0], x[1]) is not None]
    print(fmt_stats("CORRECTED (root nodes only)", pn_new))
    for lo, hi, lab in ((0, 1000, "ay nodes < 1,000"), (1000, 10 ** 12, "ay nodes >= 1,000")):
        s = [x for x in bb_old if lo <= x[1]["nodes"] < hi]
        o = [(x[1]["t"] / x[1]["nodes"]) / (x[2]["t"] / x[2]["nodes"]) for x in s]
        c = [(x[1]["t"] / corrected_nodes(x[0], x[1])) / (x[2]["t"] / x[2]["nodes"])
             for x in s if corrected_nodes(x[0], x[1]) is not None]
        print(f"    {lab:20s} recorded geomean {geo(o):6.3f}x (n={len(o)})   "
              f"corrected {geo(c):6.3f}x (n={len(c)})")

    print("\n== 5. DIRECTION OF MOVEMENT ==")
    if rat_old and paired:
        print(f"  tree quality  geomean {geo(rat_old):.3f}x -> {geo([p[2] for p in paired]):.3f}x  "
              f"({'FALLS — ay looks BETTER' if geo([p[2] for p in paired]) < geo(rat_old) else 'rises'})")
    if pn_old and pn_new:
        print(f"  per-node cost geomean {geo(pn_old):.3f}x -> {geo(pn_new):.3f}x  "
              f"({'RISES — ay looks WORSE' if geo(pn_new) > geo(pn_old) else 'falls'})")

    if args.json_out:
        with open(args.json_out, "w") as fh:
            json.dump({
                "p0": args.p0, "share": args.share, "arm": args.arm,
                "n_both": len(both), "n_both_branch": len(bb_old),
                "r_geomean": geo(rs), "r_median": st.median(rs),
                "tree_quality_recorded_geomean": geo(rat_old) if rat_old else None,
                "tree_quality_corrected_geomean": geo([p[2] for p in paired]) if paired else None,
                "tree_quality_recorded_median": st.median(rat_old) if rat_old else None,
                "tree_quality_corrected_median": st.median([p[2] for p in paired]) if paired else None,
                "per_node_recorded_geomean": geo(pn_old) if pn_old else None,
                "per_node_corrected_geomean": geo(pn_new) if pn_new else None,
                "per_node_recorded_median": st.median(pn_old) if pn_old else None,
                "per_node_corrected_median": st.median(pn_new) if pn_new else None,
                "per_instance_r": {k: v["r"] for k, v in share.items()},
            }, fh, indent=1)
        print(f"\nwrote {args.json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
