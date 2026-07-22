# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# CLI for the differential soundness fuzzer.
#
#   python -m ayz3_fuzz --fragment qf_lia --count 1000 --seed 0
#   python -m ayz3_fuzz --fragment all --count 500
#
# Prints a per-fragment summary (agreements / unknown-skips / DISAGREEMENTS)
# and exits non-zero if ANY sat-vs-unsat disagreement is found.

import argparse
import sys

from .gen import FRAGMENTS
from .differential import have_z3, run_campaign


def main(argv=None):
    # Subcommand dispatch: `python -m ayz3_fuzz incremental ...` routes to the
    # INCREMENTAL push/pop differential fuzzer; everything else is the original
    # one-shot fuzzer (flags unchanged, for backward compatibility).
    sub = argv if argv is not None else sys.argv[1:]
    if sub and sub[0] == "incremental":
        from .incremental import main as incremental_main
        return incremental_main(sub[1:])

    p = argparse.ArgumentParser(
        prog="ayz3_fuzz",
        description="Differential SOUNDNESS fuzzer: ayz3 vs real z3py. "
                    "Flags sat-vs-unsat disagreements (wrong answers). "
                    "Subcommand 'incremental' runs the push/pop session fuzzer.",
    )
    p.add_argument("--fragment", default="all",
                   help="fragment to fuzz: " + ", ".join(sorted(FRAGMENTS)) + ", or 'all'")
    p.add_argument("--count", type=int, default=1000,
                   help="number of random formulas per fragment (default 1000)")
    p.add_argument("--seed", type=int, default=0,
                   help="starting seed (default 0); seeds are [seed, seed+count)")
    p.add_argument("--timeout-ms", type=int, default=2000,
                   help="per-check timeout in ms (default 2000); a check that "
                        "exceeds it is unknown -> SKIP, so runs never hang")
    p.add_argument("--stop-on-disagree", action="store_true",
                   help="stop a fragment at its first disagreement")
    p.add_argument("--quiet", action="store_true",
                   help="suppress periodic progress output")
    p.add_argument("--inventory", action="store_true",
                   help="run a categorized differential-finding campaign over "
                        "all fragments and write FINDINGS.md (categories A/B/C)")
    p.add_argument("--findings-path", default=None,
                   help="output path for the inventory Markdown (default: "
                        "ayz3_fuzz/FINDINGS.md)")
    args = p.parse_args(argv)

    if not have_z3():
        print("z3py is not installed; the differential fuzzer needs real z3 to "
              "compare against. Install z3-solver. (Aborting.)", file=sys.stderr)
        return 2

    if args.inventory:
        return _run_inventory(args)

    if args.fragment == "all":
        frags = sorted(FRAGMENTS)
    elif args.fragment in FRAGMENTS:
        frags = [args.fragment]
    else:
        p.error(f"unknown fragment {args.fragment!r}; "
                f"choose from {sorted(FRAGMENTS)} or 'all'")

    progress = None if args.quiet else (lambda s: print(s, flush=True))

    print(f"Differential soundness fuzz: fragments={frags} "
          f"count={args.count}/frag seed_start={args.seed}")
    print("Comparison: both-sat/both-unsat=AGREE; any unknown/binding-gap=SKIP; "
          "sat-vs-unsat=DISAGREE (unadjudicated dispute)\n")

    total_disagree = 0
    total_agree = total_skip = total_checked = 0
    total_model_ok = total_model_bad = total_model_partial = 0
    all_disagreements = []

    for frag in frags:
        summ = run_campaign(frag, args.count, seed_start=args.seed,
                            stop_on_disagree=args.stop_on_disagree,
                            progress=progress, timeout_ms=args.timeout_ms)
        print(summ.line())
        total_disagree += summ.disagree
        total_agree += summ.agree
        total_skip += summ.skip
        total_checked += summ.count
        total_model_ok += summ.model_validated
        total_model_bad += summ.model_invalid
        total_model_partial += summ.model_partial
        all_disagreements.extend(summ.disagreements)
        # Surface own-side model bugs (ayz3 said sat but model didn't satisfy).
        for case in summ.self_model_bugs:
            print(f"  [warn] {frag} seed={case.seed}: ayz3 reported sat but its "
                  f"model did NOT satisfy the formula (CAT_B wrong-model)")

    print("\n" + "-" * 70)
    print(f"TOTAL: checked={total_checked} agree={total_agree} "
          f"skip={total_skip} DISAGREE={total_disagree} "
          f"model_ok={total_model_ok} model_BAD={total_model_bad} "
          f"model_partial={total_model_partial}")

    if all_disagreements:
        print(f"\n!!! {len(all_disagreements)} VERDICT DISPUTE(S) FOUND !!!")
        for dis in all_disagreements:
            print(dis.banner())
        return 1

    print("\nNo sat-vs-unsat disagreements in this bounded campaign.")
    return 0


def _run_inventory(args):
    """Run the categorized inventory campaign and write FINDINGS.md."""
    from .inventory import (
        HISTORICAL_ARRAY_SEEDS,
        HISTORICAL_BV_MODEL_SEEDS,
        write_findings_md,
    )
    from .differential import CAT_A, CAT_B

    progress = None if args.quiet else (lambda s: print(s, flush=True))
    # When --count is given explicitly (non-default 1000), apply it uniformly;
    # otherwise use the per-fragment inventory defaults.
    counts = None
    if args.count != 1000:
        counts = {f: args.count for f in FRAGMENTS}

    # When the user did not override --timeout-ms (still the 2000 default), let
    # the inventory pick its own (tighter) default; otherwise honor the override.
    inv_timeout = None if args.timeout_ms == 2000 else args.timeout_ms

    print("Building categorized differential-finding INVENTORY "
          "(A=sat/unsat, B=wrong-model, C=partial-model NON-bug)...\n", flush=True)
    path, inv = write_findings_md(
        path=args.findings_path, counts=counts, seed_start=args.seed,
        timeout_ms=inv_timeout, progress=progress,
    )
    cats = inv.by_category()
    print("\n" + "-" * 70)
    print(f"Inventory written to: {path}")
    print(f"  Category A (sat-vs-unsat soundness bugs): {len(cats[CAT_A])} distinct")
    print(f"  Category B (wrong-model bugs):            {len(cats[CAT_B])} distinct")
    print(f"  Category C (partial models, NOT bugs):    "
          f"{sum(r.model_partial for r in inv.reports)} occurrences")
    # Make any recurrence of a historical fixed seed impossible to overlook.
    array_regressions = [f for f in cats[CAT_A]
                         if f.fragment == "arrays"
                         and f.seed in HISTORICAL_ARRAY_SEEDS]
    if array_regressions:
        print(f"  REGRESSION: {len(array_regressions)} Category A finding(s) match "
              f"historical fixed seeds {HISTORICAL_ARRAY_SEEDS}")
    bv_regressions = [f for f in cats[CAT_B]
                      if f.fragment == "qf_bv"
                      and f.seed in HISTORICAL_BV_MODEL_SEEDS]
    if bv_regressions:
        print(f"  REGRESSION: {len(bv_regressions)} Category B finding(s) match "
              f"historical fixed seeds {HISTORICAL_BV_MODEL_SEEDS}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
