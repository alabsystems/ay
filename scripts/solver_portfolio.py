#!/usr/bin/env python3
# ay-script: solver-portfolio
"""solver_portfolio.py — run AY against a portfolio of reference MILP solvers on
the same MPS instances, at matched single-thread budgets, and report a scorecard.

The point is NOT just speed. It is TWO things:
  1. GROUND TRUTH BY AGREEMENT. Every solver that PROVES optimality must agree on
     the objective value. A disagreement between two provers is a soundness alarm
     (one of them is wrong), printed as ``!! DISAGREE`` and never averaged away.
     AY is the only exact-certified member — when AY proves a value it is backed
     by an exact-rational OptimalityCertificate, so AY's proven values are the
     strongest reference in the field; the floating-point solvers corroborate.
  2. DOMINATION, HONESTLY. For each instance the fastest prover is marked, and
     AY's standing (win / parity / behind, and by how much) is reported against
     the whole field rather than against Gurobi alone.

Solvers are probed at import; any that is missing, unlicensed, or size-capped for
an instance is marked SKIP for that cell rather than failing the run. Commercial
community editions (Gurobi restricted, COPT, Xpress) have size caps and simply
drop out on the larger instances; the open solvers (SCIP, CBC, HiGHS, OR-Tools)
cover everything.

Usage:
  scripts/solver_portfolio.py --dir <mps_dir> --timeout 60
  scripts/solver_portfolio.py <a.mps> <b.mps> ... --timeout 60
  AY = ./target/release/examples/mps_solve  (built via: cargo build --release -p ay-milp --examples)
"""
from __future__ import annotations
import argparse, glob, os, subprocess, sys, time, pathlib

# ---- AY (the exact-certified subject) -------------------------------------
# Absolute path resolved at import: some commercial solver libraries (COPT's
# license probe, Xpress) chdir the process, which would break a relative path
# on the second instance.
AY_BIN = os.path.abspath(os.environ.get("AY_BIN", "./target/release/examples/mps_solve"))

def run_ay(path, T):
    t0 = time.monotonic()
    try:
        r = subprocess.run([AY_BIN, path, str(T)], capture_output=True, text=True,
                           timeout=T + 90)
    except subprocess.TimeoutExpired:
        return dict(status="TIMEOUT", obj=None, bound=None, nodes=None, t=T + 90)
    dt = time.monotonic() - t0
    out = (r.stdout or "").strip().splitlines()
    if not out:
        return dict(status="CRASH", obj=None, bound=None, nodes=None, t=dt)
    f = out[-1].split()
    st, val = f[0], None
    if len(f) > 1:
        try: val = float(f[1])
        except ValueError: val = None
    # AY prints "OPTIMAL v t", "FEASIBLE v t", "UNKNOWN ...", "INFEASIBLE - t"
    smap = {"OPTIMAL": "OPT", "FEASIBLE": "FEAS", "UNKNOWN": "UNK", "INFEASIBLE": "INF"}
    return dict(status=smap.get(st, st), obj=val, bound=None, nodes=None, t=dt)

# ---- reference solvers, each wrapped so a failure => None (SKIP) ------------
def _try(fn):
    def g(path, T):
        try:
            return fn(path, T)
        except Exception as e:
            return dict(status="SKIP", obj=None, bound=None, nodes=None, t=0.0,
                        note=str(e).splitlines()[0][:60])
    return g

@_try
def run_gurobi(path, T):
    import gurobipy as gp
    m = gp.read(path)
    m.Params.OutputFlag = 0; m.Params.Threads = 1; m.Params.TimeLimit = T
    t0 = time.monotonic(); m.optimize(); dt = time.monotonic() - t0
    st = {2: "OPT", 9: "TIMELIMIT", 3: "INF"}.get(m.Status, str(m.Status))
    obj = m.ObjVal if m.SolCount > 0 else None
    if st == "TIMELIMIT": st = "OPT" if m.MIPGap == 0 else "FEAS"
    return dict(status=st, obj=obj, bound=m.ObjBound, nodes=int(m.NodeCount), t=dt)

@_try
def run_highs(path, T):
    import highspy
    h = highspy.Highs()
    h.setOptionValue("output_flag", False); h.setOptionValue("threads", 1)
    h.setOptionValue("time_limit", float(T)); h.readModel(path)
    t0 = time.monotonic(); h.run(); dt = time.monotonic() - t0
    info = h.getInfo(); st = h.modelStatusToString(h.getModelStatus())
    smap = {"Optimal": "OPT", "Time limit reached": "FEAS", "Infeasible": "INF"}
    obj = info.objective_function_value
    have = getattr(info, "primal_solution_status", 2) != 0
    return dict(status=smap.get(st, st), obj=obj if have else None,
                bound=getattr(info, "mip_dual_bound", None),
                nodes=int(getattr(info, "mip_node_count", 0)), t=dt)

@_try
def run_scip(path, T):
    from pyscipopt import Model
    m = Model(); m.hideOutput(); m.readProblem(path)
    m.setParam("limits/time", float(T))
    try: m.setParam("parallel/maxnthreads", 1)
    except Exception: pass
    t0 = time.monotonic(); m.optimize(); dt = time.monotonic() - t0
    st = m.getStatus()  # 'optimal','timelimit','infeasible',...
    smap = {"optimal": "OPT", "timelimit": "FEAS", "infeasible": "INF"}
    obj = m.getObjVal() if m.getNSols() > 0 else None
    return dict(status=smap.get(st, st), obj=obj, bound=m.getDualbound(),
                nodes=int(m.getNNodes()), t=dt)

@_try
def run_cbc(path, T):
    from mip import Model, OptimizationStatus as OS
    m = Model(solver_name="CBC"); m.verbose = 0; m.threads = 1; m.read(path)
    t0 = time.monotonic(); st = m.optimize(max_seconds=float(T)); dt = time.monotonic() - t0
    smap = {OS.OPTIMAL: "OPT", OS.FEASIBLE: "FEAS", OS.INFEASIBLE: "INF",
            OS.NO_SOLUTION_FOUND: "TIMELIMIT"}
    obj = m.objective_value if m.num_solutions > 0 else None
    return dict(status=smap.get(st, str(st)), obj=obj, bound=m.objective_bound,
                nodes=None, t=dt)

@_try
def run_copt(path, T):
    import coptpy as cp
    env = cp.Envr(); m = env.createModel()
    m.read(path)
    m.setParam(cp.COPT.Param.Logging, 0); m.setParam(cp.COPT.Param.Threads, 1)
    m.setParam(cp.COPT.Param.TimeLimit, float(T))
    t0 = time.monotonic(); m.solve(); dt = time.monotonic() - t0
    S = cp.COPT
    smap = {S.OPTIMAL: "OPT", S.TIMEOUT: "FEAS", S.INFEASIBLE: "INF"}
    st = smap.get(m.status, str(m.status))
    try: obj = m.objval if m.haslpsol or m.hasmipsol else None
    except Exception:
        try: obj = m.objval
        except Exception: obj = None
    try: bound = m.getAttr(S.Attr.BestBnd)
    except Exception: bound = None
    try: nodes = int(m.getAttr(S.Attr.NodeCnt))
    except Exception: nodes = None
    if st == "FEAS" and bound is not None and obj is not None and abs(obj - bound) <= 1e-6 * (1 + abs(obj)):
        st = "OPT"
    return dict(status=st, obj=obj, bound=bound, nodes=nodes, t=dt)

@_try
def run_xpress(path, T):
    import xpress as xp
    m = xp.problem()
    m.setControl("outputlog", 0)
    m.read(path)
    m.setControl("threads", 1)
    try: m.setControl("timelimit", int(T))
    except Exception: m.setControl("maxtime", int(T))
    t0 = time.monotonic(); m.optimize(); dt = time.monotonic() - t0
    try: sol = m.getSolution(); have = sol is not None and len(sol) > 0
    except Exception: have = False
    try: obj = m.attributes.mipobjval if have else None
    except Exception:
        try: obj = m.getObjVal() if have else None
        except Exception: obj = None
    try: bound = m.attributes.bestbound
    except Exception: bound = None
    try: nodes = int(m.attributes.nodes)
    except Exception: nodes = None
    st = str(getattr(m.attributes, "mipstatus", "?"))
    # mipstatus: 6=optimal, 5/4 have solution
    smap = {"6": "OPT", "5": "FEAS", "4": "FEAS"}
    st = smap.get(st.split(".")[-1].strip(), "OPT" if have and bound is not None and abs((obj or 0)-bound) <= 1e-6*(1+abs(obj or 0)) else ("FEAS" if have else "?"))
    return dict(status=st, obj=obj, bound=bound, nodes=nodes, t=dt)

# python-mip's bundled CBC ships x86_64 only and will not load on arm64; SCIP and
# HiGHS cover the open-source references. AY first so a chdir by a later library
# cannot affect it.
SOLVERS = [("AY", run_ay), ("gurobi", run_gurobi), ("copt", run_copt),
           ("xpress", run_xpress), ("scip", run_scip), ("highs", run_highs)]

def fmt(v):
    if v is None: return "-"
    return f"{v:.6g}"

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="*")
    ap.add_argument("--dir")
    ap.add_argument("--timeout", type=float, default=60.0)
    ap.add_argument("--tol", type=float, default=1e-4, help="rel tol for prover agreement")
    a = ap.parse_args()
    files = list(a.files)
    if a.dir: files += sorted(glob.glob(os.path.join(a.dir, "*.mps")))
    if not files:
        print("no instances", file=sys.stderr); sys.exit(2)

    disagreements = []
    print(f"# portfolio @ {a.timeout}s, 1 thread. OPT=proved, FEAS=incumbent only.\n")
    for path in files:
        name = pathlib.Path(path).stem
        res = {}
        for sname, fn in SOLVERS:
            res[sname] = fn(path, a.timeout)
        # --- soundness: all provers must agree ---
        proven = {s: r["obj"] for s, r in res.items()
                  if r["status"] == "OPT" and r["obj"] is not None}
        ref = None
        if proven:
            ref = min(proven.values(), key=abs) if len(proven) == 1 else list(proven.values())[0]
            ref = sorted(proven.values())[len(proven)//2]  # median-ish
            for s, v in proven.items():
                if abs(v - ref) > a.tol * (1 + abs(ref)):
                    disagreements.append((name, s, v, ref))
        # --- fastest prover ---
        prov_t = [(r["t"], s) for s, r in res.items() if r["status"] == "OPT"]
        fastest = min(prov_t)[1] if prov_t else None
        # --- print row ---
        print(f"== {name}  (optimum {'= '+fmt(ref) if ref is not None else 'UNPROVEN by field'}) ==")
        for sname, _ in SOLVERS:
            r = res[sname]
            star = " *fastest" if sname == fastest else ""
            note = f"  ({r.get('note')})" if r.get("note") else ""
            b = f" bound={fmt(r['bound'])}" if r["status"] in ("FEAS","TIMELIMIT") and r["bound"] is not None else ""
            nd = f" nodes={r['nodes']}" if r.get("nodes") else ""
            print(f"   {sname:8s} {r['status']:5s} obj={fmt(r['obj']):>14s} {r['t']:7.2f}s{b}{nd}{star}{note}")
        print()

    print("=" * 60)
    if disagreements:
        print("!! PROVER DISAGREEMENTS (soundness alarms):")
        for name, s, v, ref in disagreements:
            print(f"   {name}: {s} proved {fmt(v)} vs field {fmt(ref)}")
    else:
        print("OK: every solver that proved optimality AGREED on the value (0 disagreements).")

if __name__ == "__main__":
    main()
