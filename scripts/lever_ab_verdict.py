#!/usr/bin/env python3
# ay-script: lever-ab-verdict
"""Score ONE paired lever A/B sweep and print a FLIP / NO-FLIP verdict.

Why this is not `verify_proof_manifest.py score`
------------------------------------------------
That scorer's `load_verdicts()` keys certificates by CNF BASENAME and collapses
several rows for one CNF by ranking verified > rejected > unverified.  On a
two-arm sweep both arms produce a row for the same CNF, so it would hand the
WINNING arm's accepted certificate to the LOSING arm as well and silently
manufacture a clean result.  `ay-lever-core` therefore stamps an `arm` field
into every manifest row (it survives into the verdict because
`verify_one` does `verdict = dict(row)`), and this scorer joins on (arm, cnf).

The pairing rule this campaign runs on
--------------------------------------
Both arms live in ONE sweep, submitted back-to-back on the same CNF, because
between-run drift on the full 400 has been measured at +/-8 solves -- wider
than any effect these levers could produce.  A base number from yesterday and
an arm number from today is not a measurement.

The flip bar
------------
  net solved > 0  AND  zero losses.
Gains and losses are counted asymmetrically, on purpose:

  * a GAIN must survive the honest-score rule -- an UNSAT counts only once an
    external checker has ACCEPTED its certificate.  A newly-"solved" UNSAT with
    no accepted certificate is not a win; it is an unverified claim.
  * a LOSS is counted the moment the arm fails to produce the answer base
    produced, certificate or not.  Losing a solve is a loss regardless.

SAT and UNSAT are always reported separately: a lever that trades two UNSAT for
two SAT nets zero and must not read as neutral.
"""
import argparse
import glob
import json
import os
import re
import sys

SOLVED = ("sat", "unsat")
VERIFIED = "verified"
REJECTED = "rejected"

STAT_RE = re.compile(r"^c\s+([a-z_0-9]+):\s*(-?\d+)\s*$")

# Counters the per-lever regression checks read out of the retained stderr.
VIVIFY_STATS = ("preprocess_ms", "viv_irr_calls_pp", "viv_pp_rounds",
                "viv_pp_ticks", "viv_pp_converged", "viv_pp_stop_bdgt",
                "viv_pp_stop_rnds", "viv_pp_stop_dead")
EQUITICKS_STATS = ("conflicts", "decisions", "focused_decs", "stable_decs",
                   "mode_switches", "restarts")
BVE_STATS = ("bve_eliminated", "bve_cls_removed", "bve_resolvents",
             "factor_count", "preprocess_ms")

# A both-arms-solved pair is a TIME REGRESSION when it is both relatively and
# absolutely worse. Either alone is noise on a loaded machine.
REGRESSION_RATIO = 1.5
REGRESSION_ABS_S = 5.0
# A pair whose two arms agree to within this is treated as INERT -- evidence
# the instance never reached the flag. A high inert rate means the eligible
# population was over-approximated, which is a reportable fact, not a failure.
INERT_ABS_S = 0.5
INERT_RATIO = 1.05


def load_verdict_rows(manifest):
    """(arm, cnf-basename) -> most recent verdict row. NEVER collapse arms."""
    vdir = os.path.join(manifest, "verdicts")
    out = {}
    for p in sorted(glob.glob(os.path.join(vdir, "*.json"))):
        try:
            row = json.load(open(p))
        except (OSError, ValueError):
            continue
        arm = row.get("arm")
        cnf = os.path.basename(row.get("cnf", ""))
        if not arm or not cnf:
            continue
        key = (arm, cnf)
        cur = out.get(key)
        if cur is None or (row.get("epoch") or 0) >= (cur.get("epoch") or 0):
            out[key] = row
    return out


def load_pending(manifest):
    """(arm, cnf) still awaiting a checker -- an ABSENT measurement, not a pass."""
    pend = {}
    for sub in ("pending", "claimed"):
        for p in sorted(glob.glob(os.path.join(manifest, sub, "*.json"))):
            try:
                row = json.load(open(p))
            except (OSError, ValueError):
                continue
            arm, cnf = row.get("arm"), os.path.basename(row.get("cnf", ""))
            if arm and cnf:
                pend[(arm, cnf)] = sub
    return pend


def load_stats(stats_dir, arms):
    """(arm, cnf) -> {counter: int} from the retained stderr copies."""
    out = {}
    if not stats_dir or not os.path.isdir(stats_dir):
        return out
    for p in sorted(glob.glob(os.path.join(stats_dir, "*.stats"))):
        name = os.path.basename(p)[:-len(".stats")]
        # token = <cnf-base>.<arm>.<pid>.<seq>
        parts = name.split(".")
        if len(parts) < 4:
            continue
        arm = None
        for a in arms:
            if f".{a}." in name:
                arm = a
                break
        if arm is None:
            continue
        cnf = name.split(f".{arm}.")[0] + ".cnf"
        vals = {}
        try:
            with open(p, errors="replace") as fh:
                for line in fh:
                    m = STAT_RE.match(line.rstrip("\n"))
                    if m:
                        vals[m.group(1)] = int(m.group(2))
        except OSError:
            continue
        prev = out.get((arm, cnf))
        # Several runs can exist (phantom-memout retries); the richest wins.
        if prev is None or len(vals) > len(prev):
            out[(arm, cnf)] = vals
    return out


def solve_seconds(row, vrow):
    ms = (vrow or {}).get("ay_wall_ms")
    if ms is None:
        ms = row.get("solver_wall_ms")
    if ms is not None and ms >= 0:
        return ms / 1000.0
    return row.get("time")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sweep", required=True)
    ap.add_argument("--lever", required=True,
                    choices=("vivify-converge", "mode-equiticks-large",
                             "bve-giant-raw", "large-rephase-walk"))
    ap.add_argument("--base-solver", default="ay-base")
    ap.add_argument("--arm-solver", required=True)
    ap.add_argument("--base-arm", default="base")
    ap.add_argument("--arm", required=True)
    ap.add_argument("--manifest",
                    default=os.path.expanduser("~/ay-bench/proof-manifest-lever"))
    ap.add_argument("--stats-dir",
                    default=os.path.expanduser("~/ay-bench/lever-ab/stats"))
    ap.add_argument("--truth", default="benchmarks/sat/satcomp2026-main-truth.json")
    ap.add_argument("--populations",
                    default=os.path.expanduser("~/ay-bench/lever-ab/lever-populations.json"))
    ap.add_argument("--out")
    args = ap.parse_args()

    sweep = json.load(open(args.sweep))
    timeout = float(sweep.get("timeout_s") or 0.0)
    by_cnf = {}
    for r in sweep["results"]:
        by_cnf.setdefault(r["cnf"], {})[r["solver"]] = r

    # Both side files are advisory: they add names, ground truth and header
    # counts to the report. An unreadable one must degrade the REPORT, never
    # abort the measurement -- the pairing and the certificates are what decide
    # the flip, and they come from the sweep and the manifest.
    def _load(path, what):
        try:
            return json.load(open(path))
        except (OSError, ValueError) as exc:
            print(f"note: {what} unavailable ({path}): {exc}", file=sys.stderr)
            return None

    truth = {}
    td = _load(args.truth, "ground truth") if os.path.exists(args.truth) else None
    for h, t in (td or {}).get("instances_by_hash", {}).items():
        truth[h + ".cnf"] = t

    pop = {}
    pd = _load(args.populations, "populations") if os.path.exists(args.populations) else None
    for L in (pd or {}).get("levers", []):
        if L["lever"] == args.lever:
            pop = {i["hash"] + ".cnf": i for i in L["instances"]}

    verdicts = load_verdict_rows(args.manifest)
    pending = load_pending(args.manifest)
    stats = load_stats(args.stats_dir, (args.base_arm, args.arm))

    def cert_status(arm, cnf):
        v = verdicts.get((arm, cnf))
        if v is not None:
            return v.get("status"), v
        if (arm, cnf) in pending:
            return "PENDING", None
        return "ABSENT", None

    pairs, alarms = [], []
    for cnf in sorted(by_cnf):
        b = by_cnf[cnf].get(args.base_solver)
        a = by_cnf[cnf].get(args.arm_solver)
        if b is None or a is None:
            alarms.append(f"{cnf}: missing an arm "
                          f"(base={b is not None} arm={a is not None}) -- the "
                          f"pair is not measured")
            continue
        bs, as_ = cert_status(args.base_arm, cnf), cert_status(args.arm, cnf)
        row = {
            "cnf": cnf,
            "name": truth.get(cnf, {}).get("name", "?"),
            "truth": truth.get(cnf, {}).get("truth", "?"),
            "field_solved": truth.get(cnf, {}).get("n_solved"),
            "vars": pop.get(cnf, {}).get("vars"),
            "clauses": pop.get(cnf, {}).get("clauses"),
            "tier": pop.get(cnf, {}).get("tier"),
            "base_verdict": b["verdict"], "arm_verdict": a["verdict"],
            "base_s": solve_seconds(b, verdicts.get((args.base_arm, cnf))),
            "arm_s": solve_seconds(a, verdicts.get((args.arm, cnf))),
            "base_cert": bs[0], "arm_cert": as_[0],
        }
        # Honest-score view: an UNSAT is a win only with an accepted certificate.
        row["base_scored"] = (b["verdict"] == "sat"
                              or (b["verdict"] == "unsat" and bs[0] == VERIFIED))
        row["arm_scored"] = (a["verdict"] == "sat"
                             or (a["verdict"] == "unsat" and as_[0] == VERIFIED))
        row["base_solved"] = b["verdict"] in SOLVED
        row["arm_solved"] = a["verdict"] in SOLVED
        pairs.append(row)

    # ---- soundness first. Nothing else matters if one of these fires. -------
    for r in pairs:
        if (r["base_verdict"] in SOLVED and r["arm_verdict"] in SOLVED
                and r["base_verdict"] != r["arm_verdict"]):
            alarms.append(f"{r['cnf']} ({r['name']}): ARMS DISAGREE "
                          f"base={r['base_verdict']} arm={r['arm_verdict']} -- "
                          f"a wrong answer, not a performance result")
        for side in ("base", "arm"):
            if r[f"{side}_cert"] == REJECTED:
                alarms.append(f"{r['cnf']} ({r['name']}): {side} certificate "
                              f"REJECTED by the external checker")
        tv = r["truth"]
        for side in ("base", "arm"):
            if tv in SOLVED and r[f"{side}_verdict"] in SOLVED \
                    and r[f"{side}_verdict"] != tv:
                alarms.append(f"{r['cnf']} ({r['name']}): {side} answered "
                              f"{r[f'{side}_verdict']} against ground truth {tv}")

    unresolved = [r for r in pairs
                  if r["base_cert"] in ("PENDING", "ABSENT") and r["base_verdict"] == "unsat"] \
        + [r for r in pairs
           if r["arm_cert"] in ("PENDING", "ABSENT") and r["arm_verdict"] == "unsat"]

    gains = [r for r in pairs if r["arm_scored"] and not r["base_solved"]]
    losses = [r for r in pairs if r["base_solved"] and not r["arm_solved"]]
    # An UNSAT the arm produced but whose certificate is not accepted is NOT a
    # gain -- but it is also not nothing. Name it.
    unverified_gains = [r for r in pairs
                        if r["arm_solved"] and not r["base_solved"] and not r["arm_scored"]]

    def split(rows):
        return (sum(1 for r in rows if r["truth"] == "sat"),
                sum(1 for r in rows if r["truth"] == "unsat"),
                sum(1 for r in rows if r["truth"] not in SOLVED))

    both = [r for r in pairs if r["base_solved"] and r["arm_solved"]
            and r["base_s"] and r["arm_s"]]
    regressions = [r for r in both
                   if r["arm_s"] > r["base_s"] * REGRESSION_RATIO
                   and r["arm_s"] - r["base_s"] > REGRESSION_ABS_S]
    speedups = [r for r in both
                if r["base_s"] > r["arm_s"] * REGRESSION_RATIO
                and r["base_s"] - r["arm_s"] > REGRESSION_ABS_S]
    inert = [r for r in pairs
             if r["base_verdict"] == r["arm_verdict"]
             and r["base_s"] and r["arm_s"]
             and abs(r["arm_s"] - r["base_s"]) < INERT_ABS_S
             and max(r["arm_s"], r["base_s"]) <= min(r["arm_s"], r["base_s"]) * INERT_RATIO]

    def par2(rows, key):
        return sum((r[f"{key}_s"] if r[f"{key}_scored"] and r[f"{key}_s"] is not None
                    else 2 * timeout) for r in rows)

    net = len(gains) - len(losses)

    # ---- lever-specific watches -------------------------------------------
    # Ground truth is UNKNOWN for a large slice of this corpus (the field
    # solved none of them), so keying a regression watch on `truth` alone
    # silently exempts exactly the instances no one has an answer for. Treat a
    # row as SAT/UNSAT when ground truth says so OR when either arm produced
    # that answer.
    def is_truth(r, want):
        return (r["truth"] == want
                or r["base_verdict"] == want or r["arm_verdict"] == want)

    watches = []
    if args.lever == "bve-giant-raw":
        floor = [r for r in pairs if is_truth(r, "sat") and (r["vars"] or 0) > 150_000]
        lost_sat = [r for r in floor if r["base_solved"] and not r["arm_solved"]]
        watches.append({
            "name": "giant SAT floor controls",
            "detail": f"{len(floor)} in-band SAT instance(s); "
                      f"{len(lost_sat)} lost under the arm",
            "fail": bool(lost_sat),
            "rows": [r["name"] for r in lost_sat]})
        inband_unsat = [r for r in pairs if is_truth(r, "unsat")]
        u_reg = [r for r in regressions if is_truth(r, "unsat")]
        u_lost = [r for r in losses if is_truth(r, "unsat")]
        watches.append({
            "name": "in-band UNSAT",
            "detail": f"{len(inband_unsat)} in-band UNSAT; {len(u_lost)} lost, "
                      f"{len(u_reg)} slower by >{REGRESSION_RATIO}x",
            "fail": bool(u_lost),
            "rows": [r["name"] for r in u_lost + u_reg]})
        bad_cert = [r for r in gains + unverified_gains
                    if r["arm_verdict"] == "unsat" and r["arm_cert"] != VERIFIED]
        watches.append({
            "name": "every gained UNSAT carries an accepted certificate",
            "detail": f"{len(bad_cert)} gained UNSAT without an accepted certificate",
            "fail": bool(bad_cert),
            "rows": [f"{r['name']} ({r['arm_cert']})" for r in bad_cert]})
    elif args.lever == "mode-equiticks-large":
        big_unsat_reg = [r for r in regressions
                         if is_truth(r, "unsat") and (r["clauses"] or 0) > 1_000_000]
        big_unsat_lost = [r for r in losses
                          if is_truth(r, "unsat") and (r["clauses"] or 0) > 1_000_000]
        watches.append({
            "name": ">1M-clause UNSAT regressions",
            "detail": f"{len(big_unsat_lost)} lost, {len(big_unsat_reg)} slower "
                      f"by >{REGRESSION_RATIO}x (the known witness went "
                      f"26.4s -> 58.2s, which this rule catches)",
            "fail": bool(big_unsat_lost or big_unsat_reg),
            "rows": [f"{r['name']} {r['base_s']}s->{r['arm_s']}s"
                     for r in big_unsat_lost + big_unsat_reg]})
    elif args.lever == "vivify-converge":
        pp_deltas, dead, bdgt, reached, have_counter = [], 0, 0, 0, 0
        for r in pairs:
            sb = stats.get((args.base_arm, r["cnf"]), {})
            sa = stats.get((args.arm, r["cnf"]), {})
            if "preprocess_ms" in sb and "preprocess_ms" in sa:
                pp_deltas.append((sa["preprocess_ms"] - sb["preprocess_ms"], r["name"]))
            dead += sa.get("viv_pp_stop_dead", 0)
            bdgt += sa.get("viv_pp_stop_bdgt", 0)
            # "counter absent" and "counter zero" are different findings. The
            # viv_pp_* counters were introduced BY 05d1b59745, so a binary that
            # predates the lever emits none of them -- exactly the stale-binary
            # failure this harness exists to catch. Absent must not be silently
            # read as "never reached".
            if "viv_irr_calls_pp" in sa:
                have_counter += 1
                if sa["viv_irr_calls_pp"] > 0:
                    reached += 1
        pp_deltas.sort(reverse=True)
        worst = pp_deltas[:5]
        tot = sum(d for d, _ in pp_deltas)
        watches.append({
            "name": "preprocess_ms cost",
            "detail": f"total +{tot} ms across {len(pp_deltas)} measured pair(s); "
                      f"worst: " + ", ".join(f"{n} +{d}ms" for d, n in worst),
            "fail": False, "rows": [f"{n} +{d}ms" for d, n in worst]})
        watches.append({
            "name": "convergence loop stop reasons (arm)",
            "detail": f"viv_pp_stop_dead={dead} (30 s wall net binding), "
                      f"viv_pp_stop_bdgt={bdgt} (tick budget binding). Both "
                      f"non-zero means the loop still never reaches a fixed "
                      f"point -- the defect the commit set out to fix.",
            "fail": False, "rows": []})
        if have_counter == 0:
            watches.append({
                "name": "the arm was actually REACHED",
                "detail": "UNKNOWN -- viv_irr_calls_pp is absent from every "
                          "stats file. That counter was introduced BY commit "
                          "05d1b59745, so its absence means the measured binary "
                          "PREDATES the lever and both arms ran the same code. "
                          "Rebuild and re-measure; do not read this run as a null.",
                "fail": True, "rows": []})
        else:
            watches.append({
                "name": "the arm was actually REACHED",
                "detail": f"{reached}/{have_counter} instance(s) with counters ran "
                          f"preprocessing vivification at all (viv_irr_calls_pp > 0). "
                          f"A low number here means the population was "
                          f"over-approximated and the null is about reachability, "
                          f"not about the lever.",
                "fail": reached == 0, "rows": []})

    # ---- verdict -----------------------------------------------------------
    hard_fail = bool(alarms) or any(w["fail"] for w in watches)
    flip = (net > 0 and not losses and not hard_fail and not unresolved)

    print(f"lever        : {args.lever}")
    print(f"sweep        : {args.sweep}")
    print(f"arms         : {args.base_solver} (control) vs {args.arm_solver}")
    print(f"pairs        : {len(pairs)}   timeout {timeout:g}s   "
          f"configuration: {sweep.get('solver_configuration')}")
    print()
    g = split(gains); l = split(losses)
    print(f"  GAINS  {len(gains):3d}   sat={g[0]} unsat={g[1]} unknown-truth={g[2]}")
    for r in gains:
        print(f"      + {r['name']}  {r['arm_verdict']} @{r['arm_s']}s "
              f"(cert {r['arm_cert']}, field solved {r['field_solved']})")
    print(f"  LOSSES {len(losses):3d}   sat={l[0]} unsat={l[1]} unknown-truth={l[2]}")
    for r in losses:
        print(f"      - {r['name']}  base {r['base_verdict']} @{r['base_s']}s "
              f"-> arm {r['arm_verdict']}")
    print(f"  NET    {net:+d}")
    if unverified_gains:
        print(f"  NOT COUNTED AS GAINS ({len(unverified_gains)}): arm answered but "
              f"the certificate is not accepted")
        for r in unverified_gains:
            print(f"      ? {r['name']} {r['arm_verdict']} cert={r['arm_cert']}")
    print()
    print(f"  PAR-2 (honest/scored) base {par2(pairs,'base'):.1f} -> "
          f"arm {par2(pairs,'arm'):.1f}")
    print(f"  both-arms-solved pairs: {len(both)}  "
          f"speedups>{REGRESSION_RATIO}x: {len(speedups)}  "
          f"regressions>{REGRESSION_RATIO}x: {len(regressions)}")
    for r in regressions[:10]:
        print(f"      slower: {r['name']} {r['base_s']}s -> {r['arm_s']}s")
    for r in speedups[:10]:
        print(f"      faster: {r['name']} {r['base_s']}s -> {r['arm_s']}s")
    print(f"  INERT pairs (arms agree within {INERT_ABS_S}s): {len(inert)}/{len(pairs)}"
          f"  -- the dilution the eligible-population filter could not remove")
    print()
    for w in watches:
        print(f"  [{'FAIL' if w['fail'] else 'ok  '}] {w['name']}: {w['detail']}")
        for r in w["rows"][:8]:
            print(f"           {r}")
    if unresolved:
        print(f"\n### {len(unresolved)} UNSAT row(s) with no accepted certificate "
              f"decision (PENDING/ABSENT) -- DRAIN THE MANIFEST AND RE-SCORE. "
              f"This verdict is NOT reproducible until then. ###")
        for r in unresolved[:10]:
            print(f"      {r['name']}")
    if alarms:
        print(f"\n*** {len(alarms)} SOUNDNESS ALARM(S) ***")
        for a in alarms:
            print(f"    {a}")
    print()
    print("  ============================================================")
    print(f"  VERDICT: {'FLIP' if flip else 'NO FLIP'} -- {args.lever}")
    print("  ============================================================")
    print("  bar: net solved > 0 AND zero losses AND no lever-specific FAIL")
    print(f"       net={net:+d}  losses={len(losses)}  "
          f"lever-fails={sum(1 for w in watches if w['fail'])}  "
          f"alarms={len(alarms)}  undecided-certs={len(unresolved)}")
    if not flip and net > 0 and losses:
        print("  NOTE: the arm gained solves AND lost solves. That is a trade, "
              "not an improvement; the standing bar is zero losses.")
    if flip:
        print("  NEXT: flipping the default is a SEPARATE change. This verdict "
              "licenses it on THIS corpus at THIS timeout only.")

    out = {"lever": args.lever, "sweep": args.sweep, "flip": flip,
           "net": net, "n_pairs": len(pairs), "timeout_s": timeout,
           "gains": [r["cnf"] for r in gains], "losses": [r["cnf"] for r in losses],
           "gain_split_sat_unsat_unknown": g, "loss_split_sat_unsat_unknown": l,
           "unverified_gains": [r["cnf"] for r in unverified_gains],
           "par2_base": round(par2(pairs, "base"), 1),
           "par2_arm": round(par2(pairs, "arm"), 1),
           "regressions": [r["cnf"] for r in regressions],
           "speedups": [r["cnf"] for r in speedups],
           "n_inert": len(inert), "watches": watches, "alarms": alarms,
           "undecided_certificates": len(unresolved), "pairs": pairs}
    if args.out:
        with open(args.out, "w") as fh:
            json.dump(out, fh, indent=2)
        print(f"\nwrote {args.out}")
    if alarms:
        return 2
    if unresolved:
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
