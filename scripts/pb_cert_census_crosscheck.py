#!/usr/bin/env python3
"""Cross-check this census's optima against the committed 2026-08-27 census.

WHY. A census is only ground truth if an independent record agrees with it.
the development design notes recorded the
optimum AY reached for 163 OPT-LIN instances on a different day, at a different
budget (12 s), under a different load, with a DIFFERENT BINARY. Every instance
present in both should carry the same optimum: an optimum is a number about the
instance, not about the run. A disagreement is either a bug or a corpus-path
mismatch, and either one has to be found before the coverage number is quoted.

This is also the only place the census can check its own DENOMINATOR. The
no-proof arm's `s OPTIMUM FOUND` is AY's own uncertified claim -- that is
precisely the thing the certificate program exists to make checkable -- so an
independent record agreeing on the VALUE is the strongest available evidence
that the denominator is not fiction.

Usage: pb_cert_census_crosscheck.py <census.json> <reference.tsv>
"""

import json
import sys


def main():
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    census = json.load(open(sys.argv[1]))

    ref = {}
    with open(sys.argv[2]) as fh:
        for line in fh:
            if line.startswith("#") or not line.strip():
                continue
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 2:
                continue
            ref[parts[0]] = parts[1]

    agree = disagree = only_census = 0
    # Guard: if the join key never matches, the script reports "0 disagreements"
    # for having compared NOTHING. That is exactly the vacuous-pass failure this
    # repo keeps finding, so an empty intersection is an ERROR, not a pass.
    rows = []
    for rec in census["instances"]:
        mine = None
        for key in ("cli_noproof", "aypb_noproof"):
            arm = rec.get(key)
            if arm and arm["status"] == "OPTIMUM FOUND":
                mine = arm["objective"]
                break
        if mine is None:
            continue
        theirs = ref.get(rec["path"])
        if theirs is None:
            only_census += 1
            continue
        if str(theirs) == str(mine):
            agree += 1
        else:
            disagree += 1
            rows.append((rec["name"], mine, theirs))

    print(f"reference rows:                    {len(ref)}")
    print(f"optima in BOTH, values AGREE:      {agree}")
    print(f"optima in BOTH, values DISAGREE:   {disagree}")
    print(f"optima only in this census:        {only_census}")
    if agree + disagree == 0:
        print("ERROR: the two records share NO instance path -- this comparison",
              file=sys.stderr)
        print("       measured nothing and must not be read as agreement.",
              file=sys.stderr)
        return 2
    for name, mine, theirs in rows:
        print(f"  DISAGREE {name}: census={mine} reference={theirs}")
    return 1 if disagree else 0


if __name__ == "__main__":
    sys.exit(main())
