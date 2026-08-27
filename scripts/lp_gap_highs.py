#!/usr/bin/env python3
"""One LP through HiGHS, timed exactly the way the ay arms time themselves.

WHY A SUBPROCESS. The three arms of `milp_lp_gap.py` must be symmetric: each is
one fresh process, one model read that is NOT charged, one solve that IS. An
in-process HiGHS would accumulate state across instances and would be the only
arm not paying process startup, which is precisely the kind of asymmetry that
turns a harness into the thing under audit.

INTEGRALITY IS DROPPED, matching what both ay diag lanes do (their float
lowering ignores column kinds) and what `milp_w0.py`'s Gurobi arm did
(`Model.relax()`). The subject of all three arms is therefore the same LP.

Prints ONE line to stdout:
    highs_lp: status=<name> obj=<f64> wall=<s> iters=<n>
`wall` excludes the model read, as ay's `wall=` does.
"""
from __future__ import annotations

import sys
import time


def main() -> int:
    if len(sys.argv) < 3:
        print("usage: lp_gap_highs.py <model.mps[.gz]> <secs>", file=sys.stderr)
        return 2
    path, secs = sys.argv[1], float(sys.argv[2])
    import highspy

    h = highspy.Highs()
    h.setOptionValue("output_flag", False)
    h.setOptionValue("threads", 1)
    h.setOptionValue("time_limit", secs)
    st = h.readModel(path)
    if not str(st).endswith("kOk"):
        print(f"highs_lp: status=READFAIL({st}) obj=nan wall=nan iters=0")
        return 1
    n = h.getNumCol()
    if n:
        # Relax every column to continuous. Cheap and unconditional: on an
        # already-continuous LP it is a no-op, so the same code path serves the
        # oracle_v2 corpus (continuous) and the W0 corpus (integral).
        h.changeColsIntegrality(n, list(range(n)), [highspy.HighsVarType.kContinuous] * n)
    t0 = time.monotonic()
    h.run()
    wall = time.monotonic() - t0
    status = str(h.getModelStatus()).split(".")[-1]
    info = h.getInfo()
    iters = int(getattr(info, "simplex_iteration_count", 0) or 0)
    obj = float(h.getObjectiveValue())
    print(f"highs_lp: status={status} obj={obj:.9g} wall={wall:.6f} iters={iters}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
