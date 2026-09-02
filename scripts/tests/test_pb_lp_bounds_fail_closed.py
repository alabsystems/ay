#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Adversarial guard for the exact LP* bound machinery the miss probe relies on.

The probe classifies a residual certificate miss as SEARCH-PROOF-GAP or as an
emission gap by comparing `ceil(LP*)` with the optimum. If a "lower bound on
LP*" can come back ABOVE LP*, the probe declares an LP-dual floor reachable
when weak duality caps every such floor below the optimum — it fails OPEN, and
the next family hunt is sent after a route that cannot exist.

`exact_lower` did exactly that: `w := max(0, A'y - c)` was accumulated only over
variables touched by a row with `y_i != 0`, so an untouched variable with a
NEGATIVE objective coefficient (excess `-c_j > 0`) contributed no `w` at all.
On PB25 OPT-LIN's `bnn_mnist_rot_16_label5_adversarial_norm_1` that returned
15502 against a true LP* of 0, and 34 of the 90 residual-miss instances carry a
negative objective coefficient.

Run:  python3 scripts/tests/test_pb_lp_bounds_fail_closed.py
"""

import os
import subprocess
import sys
import tempfile
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from pb_lp_relaxation_ceiling import (  # noqa: E402
    exact_lower,
    exact_upper,
    exact_upper_margin,
    parse_opb,
    solve_float,
)

# (name, opb text, exact LP*) — every LP* here is checked by hand below.
CASES = [
    (
        # min -3 x1 + 1 x2  s.t. x1 + x2 >= 1, 0<=x<=1.  Take x1=1, x2=0: -3.
        # No untouched-variable w term => the pre-fix code was already right.
        "negative-objective-touched",
        "min: -3 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n",
        Fraction(-3),
    ),
    (
        # min -5 x1 + 1 x2 s.t. x2 >= 1.  x1 carries a NEGATIVE objective
        # coefficient and appears in NO row, so no dual y can ever touch it and
        # its w = 5 is invisible to a sweep over touched variables only.
        # LP* = -5 + 1 = -4; the pre-fix sweep returned +1, i.e. a "lower bound"
        # five above LP*. THIS CASE IS THE REGRESSION GUARD.
        "negative-objective-untouched",
        "min: -5 x1 +1 x2 ;\n+1 x2 >= 1 ;\n",
        Fraction(-4),
    ),
    (
        # Fractional vertex: min x1+x2+x3 s.t. each pair sums to >= 1.
        # LP* = 3/2 at x = (1/2, 1/2, 1/2); ceil(LP*) = 2.
        "half-integral-triangle",
        "min: +1 x1 +1 x2 +1 x3 ;\n"
        "+1 x1 +1 x2 >= 1 ;\n+1 x2 +1 x3 >= 1 ;\n+1 x1 +1 x3 >= 1 ;\n",
        Fraction(3, 2),
    ),
    (
        # Equality row, split into two >= rows by the parser.
        "equality-row",
        "min: +2 x1 +3 x2 ;\n+1 x1 +1 x2 = 1 ;\n",
        Fraction(2),
    ),
]


def check(name, text, lp_star):
    with tempfile.NamedTemporaryFile("w", suffix=".opb", delete=False) as handle:
        handle.write(text)
        path = handle.name
    try:
        objective, rows, num_vars, _nnz = parse_opb(path)
        result = solve_float(objective, rows, num_vars)
        low = exact_lower(objective, rows, result, num_vars)
        high = exact_upper(objective, rows, num_vars, result)
        if high is None:
            high = exact_upper_margin(objective, rows, num_vars, result)
        bad = []
        if low is None:
            bad.append("no lower bound produced")
        elif low > lp_star:
            bad.append(f"LOWER BOUND {low} EXCEEDS LP* {lp_star} — FAILS OPEN")
        if high is not None and high < lp_star:
            bad.append(f"upper bound {high} below LP* {lp_star} — FAILS OPEN")
        print(f"  {'FAIL' if bad else 'ok  '}  {name:32s} "
              f"LP*={lp_star}  lower={low}  upper={high}")
        for message in bad:
            print(f"        {message}")
        return not bad
    finally:
        os.unlink(path)


def main():
    print("exact LP* bound machinery — fail-closed guard")
    ok = all([check(*case) for case in CASES])

    # The self-check in the probe must turn an impossible bound into a REFUSAL,
    # never into an LP-REACHABLE verdict.
    probe = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                         "pb_cert_miss_probe.py")
    spec = subprocess.run([sys.executable, "-c",
                           f"import sys;sys.path.insert(0,{os.path.dirname(probe)!r});"
                           "import pb_cert_miss_probe as p;"
                           "print(p.lp_verdict({'lp_lower_exact':'9',"
                           "'lp_upper_exact':'2'}, 3))"],
                          capture_output=True, text=True)
    got = spec.stdout.strip()
    if got != "LP-BOUND-INCONSISTENT":
        print(f"  FAIL  probe self-check: lower 9 > optimum 3 gave {got!r}")
        ok = False
    else:
        print("  ok    probe refuses an impossible bound (LP-BOUND-INCONSISTENT)")

    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
