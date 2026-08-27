#!/usr/bin/env python3
"""The 33rd case of the divisor split: b = 0."""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_obligations import circuit, HDR  # noqa: E402

N = 32
defs, q, r = circuit(N)
body = (
    HDR.format(n=N)
    + "\n".join(defs)
    + "\n(assert (= b (_ bv0 32)))\n"
    + "(assert (not (and (= %s (bvudiv a b)) (= %s (bvurem a b)))))\n(check-sat)\n" % (q, r)
)
open(HERE + "/ctl/Szz_udiv_urem_zero_W32.smt2", "w").write(body)
print("Szz_udiv_urem_zero_W32.smt2")
