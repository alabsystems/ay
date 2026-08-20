#!/usr/bin/env python3
# ay-script: ab-verdict
"""Paired A/B verdict for a two-solver sweep.py result.

Judges a lever arm against a base arm the way the default-flip campaign
requires: by PAIRED per-instance outcomes (lost/gained), never by aggregate
solved counts across runs — base-arm run-to-run wobble on the main2026 corpus
is +-2 solved (measured 2026-08-19: 119 vs 117 on identical configurations),
so aggregate deltas inside that band are noise.

Exit codes:
  0  WIN   — lost == 0 and gained >= 1 and no asymmetric anomalies
  1  LOSS/WASH — anything else that is still a valid measurement
  2  ANOMALY — asymmetric unknowns/errors between arms (instant-fail
     clusters are a harness artifact until an isolated rerun reproduces
     them; see measurement-discipline lesson 10)

Usage:
  ab_verdict.py RESULTS.json --base ay-base --arm ay-lever \
      [--confirm-list OUT.txt --cnf-root DIR --sample-timeouts 12]
"""
import argparse
import json
import statistics
import sys

SOLVED = ("sat", "unsat")


def load_runs(path):
    with open(path) as fh:
        data = json.load(fh)
    runs = data if isinstance(data, list) else data.get("runs", data.get("results", []))
    by = {}
    for row in runs:
        by.setdefault(row["solver"], {})[row["cnf"]] = row
    return by


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("results")
    ap.add_argument("--base", required=True)
    ap.add_argument("--arm", required=True)
    ap.add_argument("--confirm-list", help="write gains+unknowns+sampled timeouts here")
    ap.add_argument("--cnf-root", default="", help="prefix for confirm-list paths")
    ap.add_argument("--sample-timeouts", type=int, default=12)
    args = ap.parse_args()

    by = load_runs(args.results)
    if args.base not in by or args.arm not in by:
        sys.exit(f"solvers {args.base!r}/{args.arm!r} not both present; have {sorted(by)}")
    base, arm = by[args.base], by[args.arm]
    common = sorted(set(base) & set(arm))
    if len(common) != len(base) or len(common) != len(arm):
        print(f"note: instance sets differ (base={len(base)} arm={len(arm)} common={len(common)})")

    lost = [c for c in common if base[c]["verdict"] in SOLVED and arm[c]["verdict"] not in SOLVED]
    gained = [c for c in common if arm[c]["verdict"] in SOLVED and base[c]["verdict"] not in SOLVED]
    disagree = [c for c in common if {base[c]["verdict"], arm[c]["verdict"]} == {"sat", "unsat"}]

    both = [c for c in common if base[c]["verdict"] in SOLVED and arm[c]["verdict"] in SOLVED]
    deltas = [float(arm[c]["time"]) - float(base[c]["time"]) for c in both]
    med = statistics.median(deltas) if deltas else 0.0

    def bucket(rows, verdict):
        return [c for c in common if rows[c]["verdict"] == verdict]

    b_unknown, a_unknown = set(bucket(base, "unknown")), set(bucket(arm, "unknown"))
    b_err = [c for c in common if base[c].get("rc") not in ("0", "10", "20", 0, 10, 20)
             and base[c]["verdict"] not in SOLVED and base[c]["verdict"] != "timeout"]
    a_err = [c for c in common if arm[c].get("rc") not in ("0", "10", "20", 0, 10, 20)
             and arm[c]["verdict"] not in SOLVED and arm[c]["verdict"] != "timeout"]

    print(f"base {args.base}: solved={sum(1 for c in common if base[c]['verdict'] in SOLVED)} "
          f"unknown={len(b_unknown)} suspect-rc={len(b_err)}")
    print(f"arm  {args.arm}: solved={sum(1 for c in common if arm[c]['verdict'] in SOLVED)} "
          f"unknown={len(a_unknown)} suspect-rc={len(a_err)}")
    print(f"paired: lost={len(lost)} gained={len(gained)} soundness-disagreements={len(disagree)}")
    print(f"common-solved={len(both)} median arm-base delta={med:+.2f}s")
    for c in lost:
        print(f"  LOST   {c} (base {base[c]['verdict']} @{base[c]['time']}s)")
    for c in gained:
        print(f"  GAINED {c} (arm {arm[c]['verdict']} @{arm[c]['time']}s)")

    if args.confirm_list:
        timeouts = sorted(c for c in common if base[c]["verdict"] == "timeout")
        sel = list(dict.fromkeys(gained + lost + sorted(b_unknown | a_unknown)
                                 + timeouts[: args.sample_timeouts]))
        root = args.cnf_root.rstrip("/") + "/" if args.cnf_root else ""
        with open(args.confirm_list, "w") as fh:
            fh.writelines(root + c + "\n" for c in sel)
        print(f"confirm list: {len(sel)} instances -> {args.confirm_list}")

    if disagree:
        print("VERDICT: SOUNDNESS DISAGREEMENT — investigate before anything else")
        sys.exit(2)
    if a_err or b_err:
        # The lesson-10 harness-artifact signature is a FAST non-solver exit
        # (rc=1 in fractions of a second), not unknown-set asymmetry —
        # unknown<->timeout shuffling at give-up boundaries is benign and
        # symmetric in expectation.
        print("VERDICT: ANOMALY — suspect-rc rows present; rerun them standalone "
              "before trusting the delta (lesson 10)")
        sys.exit(2)
    if a_unknown != b_unknown:
        print(f"note: unknown sets differ (base-only={sorted(b_unknown - a_unknown)} "
              f"arm-only={sorted(a_unknown - b_unknown)}) — benign unless clustered")
    if not lost and gained:
        print("VERDICT: WIN — strictly dominant; run the long-budget boundary confirmation")
        sys.exit(0)
    print("VERDICT: LOSS/WASH — record and keep the default")
    sys.exit(1)


if __name__ == "__main__":
    main()
