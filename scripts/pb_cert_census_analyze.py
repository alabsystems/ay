#!/usr/bin/env python3
"""Turn the census arms into ONE row per instance, with a miss cause.

The census is the ground truth the PB-certificate program is measured against,
so this script is written to make the number RE-DERIVABLE rather than
believable: it consumes only the TSVs the harness wrote, states every
denominator it uses, and refuses to report a pass for an arm that measured
nothing.

TWO BINARIES
------------
`cli` is the shipped `ay pb solve` (crates/ay, src/cmd_pb.rs). `aypb` is the
competition binary `ay-pb` (crates/ay-pb, src/bin/ay.rs). They are DIFFERENT
PROGRAMS with different certificate routes -- the four OPT-LIN floor emitters
are named only in the latter -- so the census reports a coverage figure per
binary and never blends them.

WHY THERE ARE TWO ARMS PER BINARY
---------------------------------
In proof mode AY is fail-closed: `solve_optimization_with_proof` discards its
proof file and downgrades `s OPTIMUM FOUND` to `s SATISFIABLE`/`s UNKNOWN`
whenever it cannot certify. So in the proof arm "solved to optimum" and "emitted
a certificate" are very nearly the same event, and dividing one by the other
would report a coverage near 100% that means nothing. The DENOMINATOR comes from
the no-proof arm, which is that binary's honest answer at that budget.

THE MISS TAXONOMY, operationally
--------------------------------
A MISS is an instance the no-proof arm solves to OPTIMUM at budget B and for
which the pinned checker does not accept a matching certificate from the proof
arm of the SAME binary.

  DELIVERY          the derivation exists but was not produced in budget --
                    MEASURED, not assumed. Either the escalation probe
                    (`pb_cert_delivery_probe.sh`, which gives the certificate
                    routes a deadline of their OWN) produced a checker-accepted
                    proof, or a larger budget did.
  SEARCH-PROOF-GAP  the no-proof arm PROVED the optimum inside the budget and
                    the certificate path still fails after escalation. AY's
                    optimality argument exists; it is simply never logged --
                    `try_opt_lin_cert_fallback` throws the search away and
                    re-derives a refutation of `instance /\\ obj <= opt-1` from
                    scratch with a different engine.
  EXPRESSION        the bound is computed but cannot be written in the proof
                    system as the emitter has it (structural decline).
  REFUSED           a fourth cause, and NOT a forced fit: AY answers
                    `s UNSUPPORTED` -- the proof path declines the instance
                    class before any search happens.
  OTHER-BINARY-CERTIFIES
                    a fifth cause, and the one the taxonomy could not have
                    predicted: this binary misses an instance the OTHER binary
                    certifies at the same budget, back to back. The derivation
                    exists, is produced in budget, and is checker-accepted --
                    it is simply not wired into this program.
  UNRESOLVED-*      not a cause: an honest refusal to name one. A miss is only
                    a SEARCH-PROOF GAP if the routes were actually TRIED, and
                    with `route=all` the three refutation routes share one
                    deadline in production's order, so the first can eat all of
                    it and the rest report 0 ms. Scoring that as a gap would
                    manufacture a negative out of a scheduling artifact.

A REJECT or WRONG-CONCLUSION is never a coverage miss. It is a soundness alarm,
reported separately and loudly.
"""

import json
import os
import sys
from collections import Counter, OrderedDict

FIELDS = [
    "path", "arm", "budget_ms", "status", "objective", "wall_ms",
    "proof_bytes", "proof_lines", "proof_sha256", "route",
    "checker_exit", "checker_verdict", "want_verdict", "score",
]

BINARIES = ("cli", "aypb")


def wilson(k, n, z=1.96):
    """95% Wilson score interval for k successes in n, as a printable string."""
    if n == 0:
        return "n/a (denominator 0)"
    p = k / n
    d = 1 + z * z / n
    centre = (p + z * z / (2 * n)) / d
    half = z * ((p * (1 - p) / n + z * z / (4 * n * n)) ** 0.5) / d
    return (f"[{100 * max(0.0, centre - half):.1f}%, "
            f"{100 * min(1.0, centre + half):.1f}%] (n={n})")


ROUTES = ("bounds_compact", "bounds_auxfree", "bounds_pb_native")


def starved_routes(timings):
    """Routes the escalation probe never actually ran, across ALL its sweeps.

    `timings` is the union of every probe's `name=Nms` fields for this instance
    (the `route=all` sweep plus any per-route sweeps). A route counts as TRIED
    if ANY sweep gave it a non-zero slice: `bounds_pb_native=0ms` from the
    shared-deadline sweep and `bounds_pb_native=60127ms` from its own sweep
    means it WAS tried, and reading only the first would invent a starvation
    that a later probe had already resolved.
    """
    seen = {r: 0 for r in ROUTES}
    for field in timings.split(","):
        if "=" not in field:
            continue
        name, ms = field.split("=", 1)
        if name in seen:
            try:
                seen[name] = max(seen[name], int(ms.rstrip("ms") or 0))
            except ValueError:
                pass
    return [r for r, ms in seen.items() if ms == 0]


def load(path):
    rows = {}
    if not os.path.exists(path):
        return rows
    with open(path) as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line:
                continue
            parts = line.split("\t")
            if len(parts) != len(FIELDS):
                raise SystemExit(
                    f"ERROR: {path}: expected {len(FIELDS)} fields, got {len(parts)}"
                )
            row = dict(zip(FIELDS, parts))
            rows[row["path"]] = row
    return rows


def main():
    if len(sys.argv) < 4:
        raise SystemExit(
            "usage: pb_cert_census_analyze.py <list> <datadir> <out.json> "
            "[budget_ms=5000] [escalation.tsv]"
        )
    list_path, datadir, out_path = sys.argv[1], sys.argv[2], sys.argv[3]
    budget_ms = int(sys.argv[4]) if len(sys.argv) > 4 else 5000
    esc_path = sys.argv[5] if len(sys.argv) > 5 else None

    with open(list_path) as fh:
        instances = [l.strip() for l in fh if l.strip()]
    total = len(instances)

    arms = {}
    for b in BINARIES:
        for mode in ("noproof", "proof"):
            arms[(b, mode)] = load(
                os.path.join(datadir, f"{b}-{mode}-{budget_ms}.tsv"))

    # The escalation probe's rows: path -> score (VERIFIED / NO-PROOF / ...).
    escalation = {}
    if esc_path and os.path.exists(esc_path):
        with open(esc_path) as fh:
            for line in fh:
                p = line.rstrip("\n").split("\t")
                if len(p) >= 8:
                    escalation[p[0]] = OrderedDict(
                        optimum=p[1], route=p[3], proof_bytes=int(p[4] or 0),
                        timings=p[5], verdict=p[6], score=p[7])

    measured = min(len(t) for t in arms.values())
    missing = {f"{b}-{m}": total - len(t) for (b, m), t in arms.items()
               if len(t) != total}

    rows = []
    for path in instances:
        rec = OrderedDict(name=os.path.basename(path), path=path)
        for (b, mode), table in arms.items():
            r = table.get(path)
            key = f"{b}_{mode}"
            if r is None:
                rec[key] = None
                continue
            e = OrderedDict(status=r["status"], objective=r["objective"],
                            wall_ms=int(r["wall_ms"]))
            if mode == "proof":
                e["proof_bytes"] = int(r["proof_bytes"])
                e["proof_lines"] = int(r["proof_lines"])
                e["proof_sha256"] = r["proof_sha256"]
                e["route"] = r["route"]
                e["checker_exit"] = r["checker_exit"]
                e["checker_verdict"] = r["checker_verdict"]
                e["want_verdict"] = r["want_verdict"]
                e["score"] = r["score"]
            rec[key] = e
        rec["escalation"] = escalation.get(path)
        rows.append(rec)

    def classify(rec, b):
        npf, pf = rec[f"{b}_noproof"], rec[f"{b}_proof"]
        if npf is None or pf is None:
            return "UNMEASURED", None
        score = pf["score"]
        if score in ("REJECT", "WRONG-CONCLUSION"):
            return "SOUNDNESS-ALARM", score
        if npf["status"] != "OPTIMUM FOUND":
            if score == "VERIFIED":
                return "CERTIFIED-BUT-UNSOLVED-IN-NOPROOF-ARM", None
            return "NOT-SOLVED", None
        if score == "VERIFIED":
            return "COVERED", None
        if pf["status"] == "UNSUPPORTED" or npf["status"] == "UNSUPPORTED":
            return "MISS", "REFUSED"
        other = "aypb" if b == "cli" else "cli"
        opf = rec.get(f"{other}_proof")
        if opf is not None and opf["score"] == "VERIFIED":
            return "MISS", "OTHER-BINARY-CERTIFIES"
        esc = rec.get("escalation")
        if esc is not None and esc["score"] == "VERIFIED":
            return "MISS", "DELIVERY"
        if score == "OVERSIZE":
            return "MISS", "DELIVERY"
        # A NEGATIVE FROM THE ESCALATION PROBE IS ONLY EVIDENCE IF EVERY ROUTE
        # ACTUALLY RAN. With `route=all` the three refutation routes share one
        # deadline in production's order, so the first can consume all of it and
        # leave `bounds_auxfree=0ms, bounds_pb_native=0ms` -- routes that were
        # never tried. Calling that a SEARCH-PROOF GAP would be inventing a
        # negative out of a scheduling artifact, so it is named for what it is
        # and stays a miss with an UNRESOLVED cause until a per-route probe
        # decides it.
        if esc is not None and starved_routes(esc.get("timings") or ""):
            return "MISS", "UNRESOLVED-ROUTES-STARVED-IN-PROBE"
        if esc is None:
            return "MISS", "UNRESOLVED-NOT-PROBED"
        return "MISS", "SEARCH-PROOF-GAP"

    summary = OrderedDict()
    summary["corpus"] = ("PB25 OPT-LIN "
                         "(benchmarks/pb-comp/selected-PB25, **/OPT-LIN/**/*.opb)")
    summary["corpus_size"] = total
    summary["budget_ms"] = budget_ms
    summary["instances_measured_in_every_arm"] = measured
    if missing:
        summary["arms_incomplete"] = missing

    for b in BINARIES:
        cls, cause = Counter(), Counter()
        for rec in rows:
            c, why = classify(rec, b)
            rec[f"class_{b}"] = c
            rec[f"cause_{b}"] = why
            cls[c] += 1
            if why:
                cause[why] += 1
        solved = cls["COVERED"] + cls["MISS"] + cls["SOUNDNESS-ALARM"]
        s = OrderedDict()
        s["binary"] = ("ay pb solve (shipped CLI, crates/ay)" if b == "cli"
                       else "ay-pb (competition binary, crates/ay-pb)")
        s["corpus"] = total
        s["measured"] = total - cls["UNMEASURED"]
        s["solved_to_optimum_noproof_arm"] = solved
        s["certificate_accepted_by_pinned_checker"] = cls["COVERED"]
        s["soundness_alarms"] = cls["SOUNDNESS-ALARM"]
        s["misses"] = cls["MISS"]
        s["not_solved_to_optimum"] = cls["NOT-SOLVED"]
        s["certified_but_unsolved_in_noproof_arm"] = cls[
            "CERTIFIED-BUT-UNSOLVED-IN-NOPROOF-ARM"]
        s["unmeasured"] = cls["UNMEASURED"]
        s["coverage_of_solved"] = f"{cls['COVERED']}/{solved}" if solved else "0/0"
        s["coverage_of_solved_pct"] = (
            round(100.0 * cls["COVERED"] / solved, 1) if solved else None)
        # The census runs the corpus in a FIXED-SEED SHUFFLED order, so any
        # prefix is an unbiased random sample of it and a partial run is a
        # sample statistic rather than a truncated fact. The interval is Wilson
        # (it does not collapse at 0 or 1 the way the normal approximation
        # does). When the run is complete this is a census, not a sample, and
        # the interval is reported as exact.
        s["coverage_of_solved_ci95"] = (
            "exact (complete census)" if not missing
            else wilson(cls["COVERED"], solved))
        s["coverage_of_measured_corpus"] = f"{cls['COVERED']}/{s['measured']}"
        s["miss_causes"] = OrderedDict(sorted(cause.items(), key=lambda kv: -kv[1]))
        summary[b] = s

    # ---- observations that are NOT coverage and would be lost in a ratio.
    obs = OrderedDict()

    for (b, mode), table in sorted(arms.items()):
        ratios = sorted(int(r["wall_ms"]) / budget_ms for r in table.values())
        if not ratios:
            continue
        obs[f"budget_overshoot_{b}_{mode}"] = OrderedDict(
            n=len(ratios), median=round(ratios[len(ratios) // 2], 2),
            p90=round(ratios[int(0.9 * (len(ratios) - 1))], 2),
            max=round(ratios[-1], 2),
            over_2x=sum(1 for x in ratios if x > 2.0),
            over_5x=sum(1 for x in ratios if x > 5.0))

    for b in BINARIES:
        t = arms[(b, "proof")]
        sat = [r for r in t.values() if r["status"] == "SATISFIABLE"]
        obs[f"sat_answers_shipped_{b}"] = OrderedDict(
            total=len(sat),
            with_accepted_certificate=sum(1 for r in sat if r["score"] == "VERIFIED"),
            with_no_proof_emitted=sum(1 for r in sat
                                      if r["score"] == "NO-PROOF-EMITTED"))

    for (b, mode), table in sorted(arms.items()):
        killed = [os.path.basename(p) for p, r in table.items()
                  if r["status"].startswith("<no-s-line")]
        if killed:
            obs[f"no_status_line_{b}_{mode}"] = killed

    # The two binaries, head to head on the same instances.
    both = [r for r in rows
            if r.get("class_cli") != "UNMEASURED"
            and r.get("class_aypb") != "UNMEASURED"]
    only_aypb = [r["name"] for r in both
                 if r["class_aypb"] == "COVERED" and r["class_cli"] != "COVERED"]
    only_cli = [r["name"] for r in both
                if r["class_cli"] == "COVERED" and r["class_aypb"] != "COVERED"]
    disagree_obj = []
    for r in both:
        a, c = r["cli_noproof"], r["aypb_noproof"]
        if (a["status"] == "OPTIMUM FOUND" and c["status"] == "OPTIMUM FOUND"
                and a["objective"] != c["objective"]):
            disagree_obj.append((r["name"], a["objective"], c["objective"]))
    obs["head_to_head"] = OrderedDict(
        instances_measured_in_both=len(both),
        certified_by_aypb_only=len(only_aypb),
        certified_by_cli_only=len(only_cli),
        certified_by_aypb_only_names=sorted(only_aypb)[:40],
        certified_by_cli_only_names=sorted(only_cli)[:40],
        optimum_disagreements=disagree_obj)
    summary["observations"] = obs

    with open(out_path, "w") as fh:
        json.dump(OrderedDict(summary=summary, instances=rows), fh, indent=1)
        fh.write("\n")
    print(json.dumps(summary, indent=2))

    alarms = [r["name"] for r in rows
              if r.get("class_cli") == "SOUNDNESS-ALARM"
              or r.get("class_aypb") == "SOUNDNESS-ALARM"]
    if alarms:
        print("\n*** SOUNDNESS ALARMS (stop the line) ***", file=sys.stderr)
        for a in alarms:
            print("   " + a, file=sys.stderr)
    if missing:
        print(f"\nWARNING: arms incomplete: {missing}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
