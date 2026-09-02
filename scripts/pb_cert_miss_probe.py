#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""THE ESCALATION PROBE. Classify every residual PB-certificate miss into one
cause, with per-instance evidence, so that family hunts stop being guesswork.

R1's probe could not be reused for R2 because it carried no BINARY column: a
miss is a property of (instance, binary, budget), not of an instance, and the
two binaries have different certificate routes (the four OPT-LIN FLOOR emitters
live in `crates/ay-pb` and nowhere in the `ay` CLI). Every row here names its
binary.

THE FOUR CAUSES
---------------
(0) NOT-SOLVED       the NO-PROOF arm of THIS binary never decided the
                     instance, so there is no optimum to certify. A search
                     problem wearing a certificate costume; it is EXCLUDED from
                     the certificate denominator, never counted as a miss.
(1) DELIVERY         the derivation exists but was not produced in budget.
                     TESTED, not asserted: the escalated arm (10x budget) is
                     re-run and the PINNED checker is asked again. A verdict
                     flipping to VERIFIED is a conversion and proves delivery.
(2) EXPRESSION       AY computes a bound it cannot write in the proof system.
                     To claim this you must first show the bound is not
                     LP-expressible, so the probe establishes LP* EXACTLY (see
                     below) rather than trusting AY's own dual solve.
(3) SEARCH-PROOF-GAP optimality is proven by a search whose reasoning is never
                     logged. Forced when ceil(LP*) < optimum: an LP-dual floor
                     certificate proves `obj >= ceil(b'y - 1'w)` from a
                     dual-feasible (y, w), and weak duality caps `b'y - 1'w` at
                     LP* for EVERY such pair, so no LP-dual floor over the
                     original rows can reach the optimum. The gap from
                     ceil(LP*) up to the optimum was closed by branching or
                     cuts, and AY logs neither.
                     This is a statement about AY's ROUTE INVENTORY, not about
                     the proof system: VeriPB's cutting-planes calculus can
                     express these bounds. Nothing here is "uncertifiable".

WHY LP* IS COMPUTED EXACTLY AND WITHOUT AY
------------------------------------------
The float LP optimum is a guess. Both sides of the classification are decided
by RATIONAL certificates recomputed with `fractions.Fraction`:

  U  a primal point snapped to a small denominator and verified row by row.
     Feasible => LP* <= U. If ceil(U) < optimum then ceil(LP*) < optimum and
     the LP-dual route is CAPPED BELOW THE OPTIMUM. Proven, not estimated.
  L  y := max(0, -HiGHS marginals) snapped, with w := max(0, A'y - c). For ANY
     y >= 0 this pair is dual feasible, so L := b'y - 1'w <= LP*. If
     ceil(L) >= optimum the LP-dual route CAN reach the optimum.

HiGHS is used only to guess where to look; if it returned nonsense both bounds
would still be valid on their own terms. The bound machinery is imported from
`pb_lp_relaxation_ceiling.py` so there is one implementation, not two.

FAIL CLOSED. When the two bounds do not decide the instance, the row is
`LP-INDETERMINATE` and the cause is `UNRESOLVED`. An undecided probe says so.

USAGE
  pb_cert_miss_probe.py lp    UNION.list OPTIMA.tsv OUT.json [JOBS]
  pb_cert_miss_probe.py class BASE_DIR ESC_DIR LP.json OUT.json OUT.tsv [GOV_DIR]

  `lp`    exact two-sided LP* bound per instance (OPTIMA.tsv: path<TAB>optimum)
  `class` join the base census, the escalated census and the LP* table into the
          per-instance cause table and the cause histogram.
"""

import json
import math
import os
import sys
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pb_lp_relaxation_ceiling import (  # noqa: E402
    Unsupported,
    exact_lower,
    exact_upper,
    exact_upper_margin,
    parse_opb,
    solve_float,
)

DECIDED = ("OPTIMUM FOUND", "UNSATISFIABLE")


# ---------------------------------------------------------------- exact LP*

def lp_star_exact(job):
    """Exact two-sided bound on LP*, or a reason the probe declined."""
    path, optimum = job
    out = {"path": path}
    try:
        objective, rows, num_vars, nnz = parse_opb(path)
        out.update(vars=num_vars, rows=len(rows), nnz=nnz)
        result = solve_float(objective, rows, num_vars)
        out["lp_float"] = float(result.fun)
        low = exact_lower(objective, rows, result, num_vars)
        high = exact_upper(objective, rows, num_vars, result)
        if high is None:
            # The optimal vertex did not snap. Re-solve with a feasibility
            # margin so a rounded point still satisfies the ORIGINAL rows. The
            # target is `optimum - 1`, the only value that settles the question:
            # a feasible point at or under it proves ceil(LP*) < optimum.
            target = None if optimum is None else optimum - 1
            high = exact_upper_margin(objective, rows, num_vars, result, target)
            out["upper_from_margin"] = high is not None
        out["lp_lower_exact"] = str(low) if low is not None else None
        out["lp_upper_exact"] = str(high) if high is not None else None
        if low is not None and high is not None and low == high:
            out["lp_star_exact"] = str(low)
            out["ceil_lp_star"] = math.ceil(low)
    except Unsupported as exc:
        out["declined"] = f"unsupported:{exc}"
    except Exception as exc:  # noqa: BLE001 — every decline is reported, never hidden
        out["declined"] = f"{type(exc).__name__}:{exc}"
    return out


def cmd_lp(list_path, optima_tsv, out_json, jobs):
    paths = [l.strip() for l in open(list_path) if l.strip()]
    optima = {}
    for line in open(optima_tsv):
        parts = line.rstrip("\n").split("\t")
        if len(parts) >= 2 and parts[1] not in ("", "-"):
            optima[parts[0]] = int(parts[1])
    results = {}
    with ProcessPoolExecutor(max_workers=jobs) as pool:
        jobs_in = [(p, optima.get(p)) for p in paths]
        for row in pool.map(lp_star_exact, jobs_in):
            path = row["path"]
            opt = optima.get(path)
            row["optimum"] = opt
            row["lp_verdict"] = lp_verdict(row, opt)
            results[path] = row
            sys.stderr.write(f"{row['lp_verdict']:22s} {os.path.basename(path)}\n")
            sys.stderr.flush()
    json.dump(results, open(out_json, "w"), indent=1, sort_keys=True)
    return 0


def lp_verdict(row, optimum):
    """Decide REACHABLE / UNREACHABLE from the RATIONAL bounds alone."""
    if "declined" in row:
        return "LP-DECLINED"
    if optimum is None:
        return "LP-NO-OPTIMUM"
    low = row.get("lp_lower_exact")
    high = row.get("lp_upper_exact")
    # FAIL-CLOSED SELF-CHECK. The LP relaxes the integer program, so
    # LP* <= optimum ALWAYS, and a lower bound above the optimum is impossible.
    # It means the bound machinery is broken on this instance, not that the
    # floor is reachable — say so instead of blessing an LP-dual route.
    # This check is what caught the `exact_lower` all-variables `w` defect.
    if low is not None and Fraction(low) > optimum:
        return "LP-BOUND-INCONSISTENT"
    if high is not None and low is not None and Fraction(low) > Fraction(high):
        return "LP-BOUND-INCONSISTENT"
    if high is not None and math.ceil(Fraction(high)) < optimum:
        return "LP-UNREACHABLE"
    if low is not None and math.ceil(Fraction(low)) >= optimum:
        return "LP-REACHABLE"
    return "LP-INDETERMINATE"


# ------------------------------------------------------------- classification

def lp_gap(lprow):
    """optimum - ceil(LP*), using the EXACT upper bound (the certified side).

    This is how far past the LP relaxation the search had to travel, i.e. how
    much unlogged reasoning a certificate would have to reproduce. It is only
    defined when the upper bound exists, because only the upper bound proves
    ceil(LP*) is that low.
    """
    high = lprow.get("lp_upper_exact")
    optimum = lprow.get("optimum")
    if high is None or optimum is None:
        return "-"
    return optimum - math.ceil(Fraction(high))


def read_arm(path):
    rows = {}
    if not os.path.exists(path):
        return rows
    for line in open(path):
        parts = line.rstrip("\n").split("\t")
        if len(parts) >= 14:
            rows[parts[0]] = parts  # LAST row per path wins (R1's dedup rule)
    return rows


def cmd_class(base_dir, esc_dir, lp_json, out_json, out_tsv, gov_dir=None):
    lp = json.load(open(lp_json))
    arms = {}
    for b in ("cli", "aypb"):
        arms[(b, "base", "noproof")] = read_arm(f"{base_dir}/{b}-noproof-60000.tsv")
        arms[(b, "base", "proof")] = read_arm(f"{base_dir}/{b}-proof-60000.tsv")
        arms[(b, "esc", "noproof")] = read_arm(f"{esc_dir}/{b}-noproof-600000.tsv")
        arms[(b, "esc", "proof")] = read_arm(f"{esc_dir}/{b}-proof-600000.tsv")
        arms[(b, "gov", "proof")] = (
            read_arm(f"{gov_dir}/{b}-proof-600000.tsv") if gov_dir else {})

    table, hist = [], {}
    for path in sorted(lp):
        for b in ("cli", "aypb"):
            bn = arms[(b, "base", "noproof")].get(path)
            bp = arms[(b, "base", "proof")].get(path)
            en = arms[(b, "esc", "noproof")].get(path)
            ep = arms[(b, "esc", "proof")].get(path)
            gp = arms[(b, "gov", "proof")].get(path)
            if bn is None or bp is None:
                continue
            base_decided = bn[3] in DECIDED
            base_score = bp[13]
            if base_decided and base_score == "VERIFIED":
                continue  # covered at 60 s for this binary: not a residual miss
            row = classify(path, b, bn, bp, en, ep, lp[path], gp)
            table.append(row)
            hist[row["cause"]] = hist.get(row["cause"], 0) + 1

    with open(out_tsv, "w") as out:
        cols = ("instance", "binary", "budget_ms", "status_noproof", "status_proof",
                "incumbent", "optimum", "lp_star_exact", "ceil_lp_star", "lp_gap",
                "lp_verdict", "cause", "evidence")
        out.write("\t".join(cols) + "\n")
        for row in table:
            out.write("\t".join(str(row.get(c, "-")) for c in cols) + "\n")
    ranked = rank(table)
    json.dump({"histogram": hist, "ranked": ranked, "rows": table},
              open(out_json, "w"), indent=1)
    for cause, n in sorted(hist.items(), key=lambda kv: -kv[1]):
        print(f"{n:5d}  {cause}")
    print(f"{len(table):5d}  TOTAL residual (instance, binary) misses")
    print()
    print("RANKED CONVERSION TARGETS (pairs convertible / one unit of work)")
    for entry in ranked:
        print(f"{entry['pairs']:5d} pairs {entry['instances']:3d} inst  "
              f"{entry['lever']:34s} {entry['note']}")
    return 0


def rank(table):
    """What converts the most (instance, binary) pairs per unit of work.

    The unit of work is ONE LEVER: a route that has to be built once and then
    fires on everything in its bucket. Buckets are keyed by the cause and, for
    the search-proof gap, by how far the search had to travel past ceil(LP*) —
    a gap of 1 is one logged cut, a gap of 25 is a logged tree.
    """
    buckets = {}
    for row in table:
        cause = row["cause"]
        gap = row.get("lp_gap")
        if cause == "3-SEARCH-PROOF-GAP" and isinstance(gap, int):
            key = ("3-SEARCH-PROOF-GAP", "gap=1 (one logged cut closes it)"
                   if gap == 1 else f"gap {'2-5' if gap <= 5 else '>5'} "
                   "(logged branch-and-bound)")
        else:
            key = (cause, "")
        entry = buckets.setdefault(key, {"pairs": 0, "insts": set()})
        entry["pairs"] += 1
        entry["insts"].add(row["instance"])
    out = []
    for (cause, note), entry in buckets.items():
        out.append({"lever": cause, "note": note, "pairs": entry["pairs"],
                    "instances": len(entry["insts"])})
    out.sort(key=lambda e: -e["pairs"])
    return out


def classify(path, binary, bn, bp, en, ep, lprow, gp=None):
    """One (instance, binary) residual miss -> exactly one cause."""
    row = {
        "instance": os.path.basename(path),
        "path": path,
        "binary": binary,
        "budget_ms": 600000 if ep else 60000,
        "status_noproof": bn[3],
        "status_proof": bp[3],
        "incumbent": bp[4],
        "optimum": lprow.get("optimum"),
        "lp_star_exact": lprow.get("lp_star_exact", "-"),
        "lp_lower_exact": lprow.get("lp_lower_exact"),
        "lp_upper_exact": lprow.get("lp_upper_exact"),
        "lp_float": lprow.get("lp_float"),
        "ceil_lp_star": lprow.get("ceil_lp_star", "-"),
        "lp_verdict": lprow.get("lp_verdict", "LP-NOT-RUN"),
        "lp_gap": lp_gap(lprow),
        "esc_status_noproof": en[3] if en else "-",
        "esc_status_proof": ep[3] if ep else "-",
        "esc_score": ep[13] if ep else "-",
        "esc_obj": ep[4] if ep else "-",
        "esc_wall_ms": ep[5] if ep else "-",
        "esc_checker_verdict": ep[11] if ep else "-",
        "gov_status_proof": gp[3] if gp else "-",
        "gov_score": gp[13] if gp else "-",
        "gov_checker_verdict": gp[11] if gp else "-",
    }

    # (0) NOT-SOLVED — this binary's search never decided it, at EITHER budget.
    if bn[3] not in DECIDED:
        if not en or en[3] not in DECIDED:
            row["cause"] = "0-NOT-SOLVED"
            row["evidence"] = (f"noproof@60s={bn[3]}; noproof@600s="
                               f"{en[3] if en else 'not-run'}; nothing to certify")
            return row
        row["cause"] = "0-NOT-SOLVED-AT-60s"
        row["evidence"] = (f"noproof@60s={bn[3]} but noproof@600s={en[3]}"
                           f" o={en[4]}: outside the 60 s denominator")
        return row

    # SOUNDNESS first: a proof the checker rejected is never a coverage miss.
    for tag, r in (("60s", bp), ("600s", ep)):
        if r and r[13] in ("REJECT", "WRONG-CONCLUSION"):
            row["cause"] = "ALARM-" + r[13]
            row["evidence"] = f"{tag} arm scored {r[13]}: {r[11]}"
            return row

    # (1) DELIVERY — TESTED. The 10x budget produced a PIN-accepted certificate.
    if ep and ep[13] == "VERIFIED":
        row["cause"] = "1-DELIVERY-CONVERTED"
        row["evidence"] = (f"proof@600s VERIFIED by THE PIN ({ep[11]}), "
                           f"{ep[6]} bytes, wall {ep[5]} ms; 60 s arm was {bp[3]}")
        return row

    # (4) RESOURCE — the run printed no `s` line at all because AY's OWN memory
    # governor (physical RAM / 16 = 3.0 GiB here) terminated it. Nothing about
    # the certificate was measured, so this is neither a delivery failure nor a
    # search-proof gap; calling it either would be inventing a result.
    #
    # The raised-governor arm splits that into three DIFFERENT answers, and the
    # difference matters for what to build next:
    #   VERIFIED           the memory ceiling WAS the whole blocker
    #   still no `s` line  the ceiling moved and the wall is still there
    #   an `s` line, no cert   memory was never the blocker; the run now
    #                          completes and the real cause is downstream, so
    #                          fall through to the LP-based classification
    #   arm not run        UNMEASURED. Say so; do not guess from the others.
    killed = [tag for tag, r in (("60s", bp), ("600s", ep))
              if r and r[3].startswith("<no-s-line")]
    if killed:
        where = "/".join(killed)
        if gp is None:
            row["cause"] = "4-RESOURCE-UNMEASURED"
            row["evidence"] = (
                f"proof arm printed no `s` line at {where}: AY's memory governor "
                f"(physical RAM/16 = 3.0 GiB) terminated it, and no raised-governor "
                f"arm was run on this pair. The certificate was NEVER MEASURED")
            return row
        if gp[13] == "VERIFIED":
            row["cause"] = "4-RESOURCE-CONVERTED-BY-GOVERNOR"
            row["evidence"] = (
                f"killed at {where} with no `s` line (3.0 GiB governor); re-run "
                f"with GOVERN_AY_MB raised: VERIFIED by THE PIN ({gp[11]}), "
                f"{gp[6]} bytes, wall {gp[5]} ms")
            return row
        if gp[3].startswith("<no-s-line"):
            row["cause"] = "4-RESOURCE-WALL-PERSISTS"
            row["evidence"] = (
                f"killed at {where} AND again with GOVERN_AY_MB raised: the "
                f"memory ceiling moved and the wall did not. Still unmeasured")
            return row
        row["resource_note"] = (
            f"killed at {where} under the default 3.0 GiB governor; only "
            f"measurable with GOVERN_AY_MB raised, where it reached "
            f"{gp[3]} (score {gp[13]}) — so memory was not the blocker")
    verdict = row["lp_verdict"]
    opt = row["optimum"]

    # (3) SEARCH-PROOF GAP — weak duality caps every LP-dual floor below the
    # optimum, so the missing step is search reasoning that is never logged.
    if verdict == "LP-UNREACHABLE":
        row["cause"] = "3-SEARCH-PROOF-GAP"
        row["evidence"] = (row.get("resource_note", "") + "; " if row.get("resource_note") else "") + (
            f"exact rational primal point certifies LP* <= {row['lp_upper_exact']}, "
            f"so ceil(LP*) <= {math.ceil(Fraction(row['lp_upper_exact']))} < optimum "
            f"{opt}; weak duality caps every LP-dual floor at LP*, so the "
            f"remaining gap is closed by unlogged branching/cut reasoning")
        return row

    # The bound EXISTS in LP-dual form and 10x budget still did not emit it.
    if verdict == "LP-REACHABLE":
        reached = ep and ep[4] not in ("-", "") and opt is not None and \
            str(ep[4]) == str(opt)
        row["cause"] = "1-DELIVERY-ROUTE-GAP"
        row["evidence"] = (row.get("resource_note", "") + "; " if row.get("resource_note") else "") + (
            f"exact dual pair certifies LP* >= {row['lp_lower_exact']} so "
            f"ceil(LP*) >= optimum {opt}: the floor is LP-EXPRESSIBLE. "
            f"proof@600s={ep[3] if ep else 'not-run'} score="
            f"{ep[13] if ep else '-'}"
            f"{' (incumbent reached, floor not emitted)' if reached else ''}"
            f" => not expression; a missing/starved EMISSION route")
        return row

    row["cause"] = "UNRESOLVED-" + verdict
    row["evidence"] = (
        f"exact LP* bracket [{row['lp_lower_exact']}, {row['lp_upper_exact']}] "
        f"does not decide against optimum {opt}; proof@600s="
        f"{ep[13] if ep else 'not-run'}")
    return row


def main(argv):
    if len(argv) >= 5 and argv[1] == "lp":
        return cmd_lp(argv[2], argv[3], argv[4], int(argv[5]) if len(argv) > 5 else 4)
    if len(argv) >= 7 and argv[1] == "class":
        return cmd_class(argv[2], argv[3], argv[4], argv[5], argv[6],
                         argv[7] if len(argv) > 7 else None)
    sys.stderr.write(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
