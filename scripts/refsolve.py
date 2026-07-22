#!/usr/bin/env python3
# ay-script: milp-refsolve
"""refsolve.py — HiGHS + SCIP + Gurobi verdicts on the downstream optimization consumer's .milp corpus (exact-MPS bridge).

Emits one CSV row per instance: stem,highs,scip,gurobi  where each verdict is
SAT / UNSAT / OTHER. ay's IN-PROCESS verdict is joined separately (mip-diff).
The MPS is milp2mps's exact-decimal export, so all three float readers round
each long decimal back to the same f64 ay stores in-process: everyone sees the
identical instance. Gurobi is optional (its free `pip install gurobipy`
restricted licence — <=2000 vars/cons/nz — covers these small NN/window MILPs
at zero cost); if gurobipy is absent the gurobi column is reported as SKIP.
"""
import glob
import json
import math
import os
import re
import sys
from pathlib import Path

import milp2mps
import pyscipopt
from _oom_guard import (  # noqa: E402
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)

try:
    import gurobipy as _gp
    from gurobipy import GRB as _GRB
    _GENV = _gp.Env(empty=True)
    _GENV.setParam("OutputFlag", 0)
    _GENV.start()
except Exception:  # noqa
    _gp = None

if len(sys.argv) < 2:
    sys.exit("usage: refsolve.py <corpus_dir> [timeout_s] [out.csv]")
CORPUS = sys.argv[1]
TMO = float(sys.argv[2]) if len(sys.argv) > 2 else 30.0
OUT = sys.argv[3] if len(sys.argv) > 3 else "/tmp/refsolve.csv"
TMP = "/tmp/cmp_mps"
os.makedirs(TMP, exist_ok=True)
PLAN = None


def highs(mps):
    try:
        r = run_captured(
            ["highs", "--time_limit", str(TMO), mps],
            PLAN.memlimit_mb, TMO + 30, label="refsolve.py[highs]",
            env=dict(os.environ, MEMLIMIT=str(PLAN.memlimit_mb),
                     NBCORE=str(PLAN.nbcore), OMP_NUM_THREADS=str(PLAN.nbcore)),
        )
    except OSError:
        return "OTHER"
    if r.timed_out or r.memout or r.output_truncated:
        return "OTHER"
    txt = r.stdout or ""
    m = re.search(r"^\s*Model status\s*:?\s*(.+)$", txt, re.M) or re.search(r"^\s*Status\s+(.+)$", txt, re.M)
    st = m.group(1).strip() if m else "?"
    if st == "Optimal":
        return "SAT"
    if "Infeasible" in st:
        return "UNSAT"
    return "OTHER"


def scip(mps):
    try:
        m = pyscipopt.Model()
        m.hideOutput()
        m.setParam("limits/time", TMO)
        m.setParam("parallel/maxnthreads", 1)
        m.readProblem(mps)
        m.optimize()
        st = m.getStatus()
    except Exception:  # noqa
        return "OTHER"
    if st in ("optimal", "bestsollimit"):
        return "SAT"
    if st == "infeasible":
        return "UNSAT"
    return "OTHER"


def gurobi(mps):
    if _gp is None:
        return "SKIP"
    try:
        m = _gp.read(mps, _GENV)
        m.Params.OutputFlag = 0
        m.Params.TimeLimit = TMO
        m.Params.Threads = 1
        m.optimize()
        if m.Status == _GRB.OPTIMAL:
            return "SAT"
        if m.Status == _GRB.INFEASIBLE:
            return "UNSAT"
        return "OTHER"
    except Exception:  # noqa
        return "OTHER"


def main():
    global PLAN
    if not math.isfinite(TMO) or TMO <= 0:
        raise SystemExit("timeout_s must be finite and positive")
    warn_concurrent_build()
    PLAN = plan_solver_resources(1, label="refsolve.py")
    resource_plan = {
        "requested_jobs": 1, "jobs": PLAN.jobs,
        "memlimit_mb_per_child": PLAN.memlimit_mb,
        "nbcore_per_child": PLAN.nbcore,
        "headroom_mb": PLAN.headroom_mb,
        "external_enforcement": "process-group rss_watchdog; MEMLIMIT/NBCORE environment",
        "in_process_references": "single-threaded; share the harness process",
    }
    files = sorted(glob.glob(os.path.join(CORPUS, "*.milp")))
    rows = []
    for f in files:
        stem = os.path.splitext(os.path.basename(f))[0]
        mps = os.path.join(TMP, stem + ".mps")
        try:
            cols, r = milp2mps.parse(f)
            with open(mps, "w") as fh:
                fh.write(milp2mps.emit(cols, r, name=stem[:8]))
        except Exception as e:  # noqa
            rows.append((stem, "CONVERT_FAIL", "CONVERT_FAIL", "CONVERT_FAIL"))
            continue
        rows.append((stem, highs(mps), scip(mps), gurobi(mps)))
    with open(OUT, "w") as fh:
        fh.write("stem,highs,scip,gurobi\n")
        for stem, h, s, g in rows:
            fh.write(f"{stem},{h},{s},{g}\n")
    Path(OUT + ".resource-envelope.json").write_text(
        json.dumps(resource_plan, indent=2) + "\n"
    )

    def tally(idx, name):
        sat = sum(1 for r in rows if r[idx] == "SAT")
        uns = sum(1 for r in rows if r[idx] == "UNSAT")
        return f"{name}: sat={sat} unsat={uns}"

    # Any pair of decisive reference verdicts that disagree is a hard bug.
    dis = sum(1 for _, h, s, g in rows
              for a, b in [(h, s), (h, g), (s, g)]
              if a in ("SAT", "UNSAT") and b in ("SAT", "UNSAT") and a != b)
    print(f"instances={len(rows)}  " + "  ".join(
        tally(i, n) for i, n in [(1, "highs"), (2, "scip"), (3, "gurobi")]))
    print(f"reference-solver pairwise hard disagreements: {dis}")
    print(f"wrote {OUT}")


if __name__ == "__main__":
    main()
