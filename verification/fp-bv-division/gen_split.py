#!/usr/bin/env python3
"""O1/O2 at width 32, split on the position of the divisor's highest set bit.

The 33 cases (b = 0, plus one per bit position k = 0..31) are exhaustive and
pairwise disjoint, so all 33 coming back `unsat` IS the width-32 statement --
no induction, no prose, just a case split the oracles can each check.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_obligations import circuit, HDR  # noqa: E402

OUT = HERE + "/ctl"
N = 32
defs, q, r = circuit(N)
head = HDR.format(n=N) + "\n".join(defs) + "\n"

for k in [int(x) for x in sys.argv[1:]] or list(range(N)):
    guard = "(assert (= ((_ extract %d %d) b) #b1))\n" % (k, k)
    if k < N - 1:
        guard += "(assert (= ((_ extract %d %d) b) (_ bv0 %d)))\n" % (N - 1, k + 1, N - 1 - k)
    body = (
        head
        + guard
        + "(assert (not (and (= %s (bvudiv a b)) (= %s (bvurem a b)))))\n(check-sat)\n" % (q, r)
    )
    name = "S%02d_udiv_urem_msb%d_W32.smt2" % (k, k)
    open(os.path.join(OUT, name), "w").write(body)
    print(name)
