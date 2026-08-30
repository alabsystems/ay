#!/usr/bin/env python3
"""Pull working sets out of a census JSON.

  misses <budget>   instances the no-proof arm solved to OPTIMUM at that budget
                    and that carry no accepted certificate. This is the input to
                    the budget-ESCALATION probe, which is what separates a
                    DELIVERY miss (more budget produces the derivation) from a
                    SEARCH-PROOF GAP (it does not).
  covered <budget>  instances whose certificate the pinned checker accepted.
                    This is the input to the adversarial mutation battery: the
                    census's VERIFIED count means nothing unless those exact
                    proofs reject when damaged.
  alarms            REJECT / WRONG-CONCLUSION rows, at any budget. A non-empty
                    list is a stop-the-line event, not a coverage number.

Usage: pb_cert_census_misses.py <census.json> <misses|covered|alarms> [budget]
"""

import json
import sys


def main():
    if len(sys.argv) < 3:
        raise SystemExit(__doc__)
    data = json.load(open(sys.argv[1]))
    what = sys.argv[2]
    budget = sys.argv[3] if len(sys.argv) > 3 else "60"
    for rec in data["instances"]:
        cls = rec.get(f"class_{budget}s")
        if what == "misses" and cls == "MISS":
            print(rec["path"])
        elif what == "covered" and cls == "COVERED":
            print(rec["path"])
        elif what == "alarms":
            if rec.get("class_5s") == "SOUNDNESS-ALARM" or \
               rec.get("class_60s") == "SOUNDNESS-ALARM":
                print(rec["path"])


if __name__ == "__main__":
    main()
