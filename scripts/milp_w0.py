#!/usr/bin/env python3
# ay-script: milp-w0
"""milp_w0.py — the W0 measurement harness from the MILP engine gap-closing plan.

The plan's first finding was that ay-milp's gap to the commercial solvers is
per-component QUALITY, not a missing component — and that without attribution you
cannot tell a refinement from noise. This is the attribution tool.

Modes, each answering one question:

``closure``   *What are the cuts worth, on their own?*
    Root dual bound before and after the cut loop, no branching (``AY_ROOT_CLOSURE``).
    Normalised against MIPLIB's reference optimum this is the **root closure** —
    the fraction of the integrality gap the cut loop closes. It is the cleanest
    cut-quality signal there is, because no tree, heuristic or branching decision
    can contaminate it.

``baseline``  *What do the other solvers get on the same bytes?*
    Gurobi and HiGHS at a matched budget. Gurobi is also run at ``NodeLimit=0`` to
    extract ITS root bound, which is the number ay's closure is actually racing.

``ablate``    *What is each component worth?*
    Re-runs ``closure`` (or a full solve) with one env knob flipped at a time and
    reports the per-instance delta. This is the tool that says which of the eight
    cut families is carrying the bound and which is freight.

``gate``      *Did this change break anything?*
    Full solves across the corpus, checked against MIPLIB's reference values.
    A proven optimum that disagrees with the reference is a hard FAIL and is
    reported as a soundness alarm, never averaged into a score. Wall/node
    regressions are reported separately, because a slow answer and a wrong answer
    are not the same kind of event.

``lp``        *How much of the gap is the LP core?*
    The same relaxation through ay's float lane and through Gurobi. Measured 8.2x
    geomean, which is why cut quality is not affordable: every adopted cut row is
    charged as LP work at every node.

``par``       *What are threads WORTH, and on which shapes?*
    P0 of the development design notes. Gurobi at
    1/2/4/8T gives the ceiling a parallel ay could buy per shape; ay's deterministic
    nodes-to-proof is recorded as the byte-equality gate a future parallel path must
    pass at one thread.

Results are JSON so that two runs can be diffed exactly; ``compare`` does that.

Usage:
  scripts/milp_w0.py closure  --tier gurobi --secs 30 --out the development design notes
  scripts/milp_w0.py baseline --tier gurobi --secs 30 --out the development design notes
  scripts/milp_w0.py ablate   --tier gurobi --secs 30 --knob AY_MILP_NO_ZERO_HALF=1
  scripts/milp_w0.py gate     --tier gurobi --secs 30 --out the development design notes
  scripts/milp_w0.py compare  the development design notes the development design notes
"""
from __future__ import annotations

import argparse
import concurrent.futures
import json
import math
import os
import pathlib
import re
import subprocess
import sys
import time

# B20: the env locator is retired; pass --corpus <dir> or symlink at the
# default path.
CORPUS = (
    pathlib.Path(sys.argv[sys.argv.index("--corpus") + 1])
    if "--corpus" in sys.argv
    else pathlib.Path.home() / "ay-bench" / "milp"
)
MANIFEST = CORPUS / "manifest.json"
AY_BIN = os.path.abspath(os.environ.get("AY_BIN", "./target/release/examples/mps_solve"))

# Relative tolerance for calling two objective values "the same number". The
# reference values in MIPLIB's .solu are themselves rounded decimals, and the
# float solvers stop at their own MIP gap, so anything tighter produces false
# alarms rather than real ones.
REL_TOL = 1e-6


# --------------------------------------------------------------------------- corpus

def load_corpus(tier: str | None, only: list[str] | None, limit: int,
                opt_only: bool) -> list[dict]:
    if not MANIFEST.exists():
        sys.exit(f"no corpus manifest at {MANIFEST}; run scripts/milp_corpus.py fetch && index")
    man = json.loads(MANIFEST.read_text())
    out = []
    for name, e in man["instances"].items():
        if tier and e.get("tier") != tier:
            continue
        if only and name not in only:
            continue
        if opt_only and e.get("ref_status") != "opt":
            continue
        out.append({"name": name, **e})
    out.sort(key=lambda e: (e.get("cols") or 0, e["name"]))
    return out[:limit] if limit else out


def close_enough(a: float | None, b: float | None, tol: float = REL_TOL) -> bool:
    if a is None or b is None:
        return False
    return abs(a - b) <= tol * max(1.0, abs(a), abs(b))


# --------------------------------------------------------------------------- ay

def run_ay(inst: dict, secs: float, env_extra: dict[str, str] | None = None,
           mode: str = "solve") -> dict:
    env = dict(os.environ)
    env.pop("AY_ROOT_CLOSURE", None)
    if mode == "closure":
        env["AY_ROOT_CLOSURE"] = "1"
    if env_extra:
        for k, v in env_extra.items():
            if v == "":
                env.pop(k, None)
            else:
                env[k] = v
    t0 = time.monotonic()
    try:
        r = subprocess.run([AY_BIN, inst["file"], str(secs)], capture_output=True,
                           text=True, timeout=secs + 120, env=env)
    except subprocess.TimeoutExpired:
        return {"status": "HARDTIMEOUT", "t": secs + 120}
    except OSError as e:
        return {"status": "CRASH", "err": str(e), "t": time.monotonic() - t0}
    wall = time.monotonic() - t0
    out = (r.stdout or "").strip().splitlines()
    if r.returncode != 0 and not out:
        return {"status": "CRASH", "rc": r.returncode,
                "err": (r.stderr or "").strip()[-400:], "t": wall}
    if not out:
        return {"status": "NOOUTPUT", "t": wall}
    last = out[-1]
    if mode == "closure":
        d = {"status": "CLOSURE", "t": wall}
        for tok in last.split():
            if "=" in tok:
                k, v = tok.split("=", 1)
                try:
                    d[k] = float(v)
                except ValueError:
                    d[k] = v
        if not last.startswith("ROOTCLOSURE"):
            d["status"] = "BADLINE"
            d["raw"] = last[:200]
        return d
    f = last.split()
    st = f[0]
    val = None
    if len(f) > 1 and f[1] != "-":
        try:
            val = float(f[1])
        except ValueError:
            val = None
    # The rigorous dual bound is on stderr; a FEASIBLE result without it cannot be
    # scored on how close it got.
    bound = None
    mb = re.search(r"dual bound \(rigorous\) = ([-\d.eE+]+)", r.stderr or "")
    if mb:
        try:
            bound = float(mb.group(1))
        except ValueError:
            bound = None
    # Field 3 is nodes-to-proof — deterministic for a given build and input, where wall
    # clock is not. It is the signal that says whether two builds ran the SAME search.
    nodes = None
    if len(f) > 3:
        try:
            nodes = int(f[3])
        except ValueError:
            nodes = None
    # THE GUROBI-COMPARABLE SPLIT. `nodes` above is `nodes_explored()`, which is
    # process-global and CUMULATIVE ACROSS RENS/RINS SUB-MIPS; Gurobi's
    # `Model.NodeCount` (recorded by `run_gurobi` below) excludes the sub-MIPs its
    # heuristics run. Comparing the two biases the result in BOTH directions at once
    # — it inflates ay's node count and, off the same numbers, deflates ay's per-node
    # cost. `root_nodes` is the field that compares to Gurobi's; `nodes` keeps its
    # historical meaning so every recorded run stays readable.
    #
    # The split rides STDERR by design (see `examples/mps_solve`): a fifth stdout
    # field would re-point `scripts/milp_node_gate.py`'s `line[-1]` parse and with it
    # all twenty node ratchet pins. `None` here means an older ay binary that predates
    # the counter — a missing datum, never silently folded into `nodes`.
    root_nodes = submip_nodes = None
    mn = re.search(r"^nodes: total=(\d+) root=(\d+) submip=(\d+)\s*$", r.stderr or "",
                   re.M)
    if mn:
        root_nodes, submip_nodes = int(mn.group(2)), int(mn.group(3))
    return {"status": st, "obj": val, "bound": bound, "t": wall, "nodes": nodes,
            "root_nodes": root_nodes, "submip_nodes": submip_nodes}


# --------------------------------------------------------------------------- gurobi

_GRB = None


def gurobi():
    global _GRB
    if _GRB is None:
        try:
            import gurobipy as gp
            _GRB = gp
        except ImportError:
            _GRB = False
    return _GRB


def run_gurobi(inst: dict, secs: float, node_limit: int | None = None,
               threads: int = 1) -> dict:
    gp = gurobi()
    if not gp:
        return {"status": "SKIP", "why": "gurobipy missing"}
    t0 = time.monotonic()
    try:
        env = gp.Env(params={"OutputFlag": 0})
        m = gp.read(inst["file"], env=env)
        m.setParam("Threads", threads)
        m.setParam("TimeLimit", secs)
        if node_limit is not None:
            m.setParam("NodeLimit", node_limit)
        m.optimize()
    except Exception as e:  # size-limited license, unreadable file, ...
        msg = str(e)
        why = "size-limited" if "size-limited" in msg else msg[:200]
        return {"status": "SKIP", "why": why, "t": time.monotonic() - t0}
    wall = time.monotonic() - t0
    st = {2: "OPTIMAL", 3: "INFEASIBLE", 5: "UNBOUNDED", 9: "TIMEOUT",
          11: "INTERRUPTED", 13: "SUBOPTIMAL"}.get(m.Status, f"STATUS{m.Status}")
    obj = None
    try:
        obj = m.ObjVal if m.SolCount > 0 else None
    except Exception:
        obj = None
    bound = None
    try:
        bound = m.ObjBound
    except Exception:
        bound = None
    nodes = None
    try:
        nodes = int(m.NodeCount)
    except Exception:
        nodes = None
    m.dispose()
    return {"status": st, "obj": obj, "bound": bound, "nodes": nodes, "t": wall}


def gurobi_root(inst: dict, secs: float) -> dict:
    """Gurobi's dual bound after root processing — the number ay's closure races.

    ``NodeLimit=1``, not ``0``: with a zero node limit Gurobi stops *before* its root
    cut loop and reports the bare presolved LP bound (measured — on gt2 it returned
    20147, exactly ay's presolved relaxation, and on neos5 a flat 13.0). One node lets
    the root cut loop and root heuristics run and then stops, which is the bound the
    closure metric is actually racing. Where Gurobi proves optimality at the root the
    status is OPTIMAL and the bound IS the optimum — that is an honest root result, not
    an artefact.
    """
    r = run_gurobi(inst, secs, node_limit=1)
    return {"root_bound": r.get("bound"), "status": r.get("status"),
            "why": r.get("why"), "t": r.get("t")}


# --------------------------------------------------------------------------- highs

def run_highs(inst: dict, secs: float) -> dict:
    exe = os.environ.get("HIGHS_BIN", "highs")
    t0 = time.monotonic()
    try:
        r = subprocess.run([exe, "--time_limit", str(secs), "--parallel", "off",
                            inst["file"]],
                           capture_output=True, text=True, timeout=secs + 120)
    except FileNotFoundError:
        return {"status": "SKIP", "why": "highs missing"}
    except subprocess.TimeoutExpired:
        return {"status": "HARDTIMEOUT", "t": secs + 120}
    wall = time.monotonic() - t0
    txt = (r.stdout or "") + (r.stderr or "")
    st = "UNKNOWN"
    if re.search(r"Status\s+Optimal", txt):
        st = "OPTIMAL"
    elif re.search(r"Status\s+Infeasible", txt):
        st = "INFEASIBLE"
    elif re.search(r"Status\s+Time limit reached", txt):
        st = "TIMEOUT"
    obj = bound = None
    mo = re.search(r"Objective value\s*:\s*([-\d.eE+]+)", txt)
    if mo:
        obj = float(mo.group(1))
    md = re.search(r"Dual bound\s*([-\d.eE+]+)", txt)
    if md:
        bound = float(md.group(1))
    mn = re.search(r"Nodes\s+(\d+)", txt)
    nodes = int(mn.group(1)) if mn else None
    return {"status": st, "obj": obj, "bound": bound, "nodes": nodes, "t": wall}


# --------------------------------------------------------------------------- modes

def closure_row(inst: dict, secs: float, env_extra=None) -> dict:
    r = run_ay(inst, secs, env_extra, mode="closure")
    ref = inst.get("ref_obj")
    row = {"name": inst["name"], "rows": inst.get("rows"), "cols": inst.get("cols"),
           "ref_obj": ref, "ref_status": inst.get("ref_status"), **r}
    # Root closure as a FRACTION of the integrality gap: 0 = the cut loop bought
    # nothing, 1 = the cuts alone closed the problem. Reported only when the
    # reference optimum is known and the gap is real; a zero-gap instance has no
    # closure to measure and reporting 0/0 as "0%" would defame the cut loop.
    bl, bc = r.get("bound_lp"), r.get("bound_cut")
    if (ref is not None and isinstance(bl, float) and isinstance(bc, float)
            and math.isfinite(bl) and math.isfinite(bc)):
        gap = abs(ref - bl)
        row["gap0"] = gap
        if gap > 1e-9 * max(1.0, abs(ref)):
            row["closure"] = max(0.0, min(1.0, abs(bc - bl) / gap))
    return row


def cmd_closure(args) -> int:
    corpus = load_corpus(args.tier, args.only, args.limit, opt_only=True)
    print(f"[closure] {len(corpus)} instances, {args.secs}s each", flush=True)
    env_extra = parse_knobs(args.knob)
    rows = []
    for i, inst in enumerate(corpus):
        row = closure_row(inst, args.secs, env_extra)
        if args.with_gurobi:
            g = gurobi_root(inst, args.secs)
            row["gurobi_root"] = g.get("root_bound")
            row["gurobi_root_status"] = g.get("status")
            # Gurobi's root closure on the SAME denominator as ay's, so the two
            # numbers are the same measurement of the same thing.
            bl, ref, gb = row.get("bound_lp"), row.get("ref_obj"), g.get("root_bound")
            if row.get("gap0") and isinstance(bl, float) and isinstance(gb, float) \
                    and ref is not None:
                row["gurobi_closure"] = max(0.0, min(1.0, abs(gb - bl) / row["gap0"]))
        rows.append(row)
        c, gc = row.get("closure"), row.get("gurobi_closure")
        extra = "" if gc is None else f" grb={100*gc:6.2f}%"
        print(f"  {i+1:3d}/{len(corpus)} {inst['name']:26s} "
              f"closure={'--' if c is None else f'{100*c:6.2f}%'}{extra} "
              f"cuts={row.get('cuts', '?')} t={row.get('t', 0):6.1f}s "
              f"{row.get('SUSPECT', '')}", flush=True)
    emit(args.out, {"mode": "closure", "secs": args.secs, "tier": args.tier,
                    "knobs": env_extra, "rows": rows})
    summarise_closure(rows)
    return 0


def summarise_closure(rows: list[dict]) -> None:
    have = [r for r in rows if r.get("closure") is not None]
    if not have:
        print("[closure] no measurable instances")
        return
    mean = sum(r["closure"] for r in have) / len(have)
    full = sum(1 for r in have if r["closure"] > 0.999)
    zero = sum(1 for r in have if r["closure"] < 1e-9)
    print(f"[closure] mean={100*mean:.2f}% over {len(have)} instances "
          f"({full} fully closed, {zero} closed nothing)")
    both = [r for r in have if r.get("gurobi_closure") is not None]
    if both:
        gm = sum(r["gurobi_closure"] for r in both) / len(both)
        am = sum(r["closure"] for r in both) / len(both)
        win = sum(1 for r in both if r["closure"] > r["gurobi_closure"] + 1e-9)
        loss = sum(1 for r in both if r["closure"] < r["gurobi_closure"] - 1e-9)
        print(f"[closure] head-to-head on {len(both)}: ay {100*am:.2f}% vs "
              f"gurobi {100*gm:.2f}%  ({win} ay-better, {loss} gurobi-better, "
              f"{len(both)-win-loss} tied)")


def cmd_baseline(args) -> int:
    corpus = load_corpus(args.tier, args.only, args.limit, opt_only=False)
    print(f"[baseline] {len(corpus)} instances, {args.secs}s each", flush=True)
    rows = []
    for i, inst in enumerate(corpus):
        row = {"name": inst["name"], "rows": inst.get("rows"), "cols": inst.get("cols"),
               "ref_obj": inst.get("ref_obj"), "ref_status": inst.get("ref_status")}
        row["gurobi"] = run_gurobi(inst, args.secs)
        row["gurobi_root"] = gurobi_root(inst, args.secs)
        row["highs"] = run_highs(inst, args.secs)
        rows.append(row)
        g, h = row["gurobi"], row["highs"]
        print(f"  {i+1:3d}/{len(corpus)} {inst['name']:26s} "
              f"grb={g['status']:9s} {g.get('t', 0):6.1f}s | "
              f"highs={h['status']:9s} {h.get('t', 0):6.1f}s", flush=True)
    emit(args.out, {"mode": "baseline", "secs": args.secs, "tier": args.tier, "rows": rows})
    return 0


def parse_knobs(spec: list[str] | None) -> dict[str, str]:
    """``["A=1", "B=2 C=3"]`` -> ``{A:1, B:2, C:3}``.

    A single argument may carry several assignments separated by whitespace, which is how
    `ablate` expresses a COMBINED setting as one arm: components often only pay together
    (a bigger per-round cut budget is only affordable once selection is filtering it), and
    an ablation that can only flip one knob at a time cannot see that.
    """
    out: dict[str, str] = {}
    for s in spec or []:
        for part in s.split():
            k, _, v = part.partition("=")
            if k:
                out[k] = v
    return out


def cmd_ablate(args) -> int:
    corpus = load_corpus(args.tier, args.only, args.limit, opt_only=True)
    knobs = args.knob or []
    print(f"[ablate] {len(corpus)} instances x {len(knobs)} knobs, {args.secs}s each",
          flush=True)
    results = {"mode": "ablate", "secs": args.secs, "tier": args.tier,
               "base": [], "knobs": {}}

    def pass_over(env_extra, label):
        rows = []
        # Published into `results` BEFORE the pass runs, so the per-instance checkpoint
        # below carries this arm's partial rows too. Appending the arm only on completion
        # meant an interrupted sweep lost everything it had measured for the arm in flight
        # — which is the arm you most want to look at when you interrupt it.
        if label != "base":
            results["knobs"][label] = rows
        for j, inst in enumerate(corpus):
            rows.append(closure_row(inst, args.secs, env_extra))
            print(f"  [{label}] {j+1}/{len(corpus)} {inst['name']}", flush=True)
            # Written every instance: a sweep this long WILL be interrupted, and a
            # partial measurement you can still read beats a complete one you lost.
            emit(args.out, results, quiet=True)
        return rows

    base = pass_over(None, "base")
    results["base"] = base
    base_by = {r["name"]: r for r in base}
    summarise_closure(base)
    for k in knobs:
        env_extra = parse_knobs([k])
        rows = pass_over(env_extra, k)
        results["knobs"][k] = rows
        deltas = []
        for r in rows:
            b = base_by.get(r["name"], {})
            if r.get("closure") is not None and b.get("closure") is not None:
                deltas.append((r["closure"] - b["closure"], r["name"]))
        deltas.sort()
        tot = sum(d for d, _ in deltas)
        print(f"[ablate] {k}: sum_delta_closure={100*tot:+.2f}pp over {len(deltas)} "
              f"instances", flush=True)
        for d, n in deltas[:3]:
            if abs(d) > 1e-9:
                print(f"           worst {n}: {100*d:+.2f}pp")
        for d, n in deltas[-3:]:
            if abs(d) > 1e-9:
                print(f"           best  {n}: {100*d:+.2f}pp")
    emit(args.out, results)
    return 0


def cmd_gate(args) -> int:
    corpus = load_corpus(args.tier, args.only, args.limit, opt_only=False)
    print(f"[gate] {len(corpus)} instances, {args.secs}s each", flush=True)
    env_extra = parse_knobs(args.knob)
    rows, alarms = [], []
    for i, inst in enumerate(corpus):
        r = run_ay(inst, args.secs, env_extra, mode="solve")
        ref, refst = inst.get("ref_obj"), inst.get("ref_status")
        row = {"name": inst["name"], "ref_obj": ref, "ref_status": refst, **r}
        # THE SOUNDNESS GATE. A proven OPTIMAL that disagrees with MIPLIB's
        # reference value is the one event that is never a performance result.
        if r.get("status") == "OPTIMAL" and refst == "opt" and ref is not None:
            if not close_enough(r.get("obj"), ref, args.tol):
                row["ALARM"] = f"OPTIMAL {r['obj']} vs reference {ref}"
                alarms.append(row)
        if r.get("status") == "INFEASIBLE" and refst in ("opt", "best"):
            row["ALARM"] = "INFEASIBLE on an instance with a known solution"
            alarms.append(row)
        rows.append(row)
        print(f"  {i+1:3d}/{len(corpus)} {inst['name']:26s} {r.get('status', '?'):10s} "
              f"obj={r.get('obj')} t={r.get('t', 0):6.1f}s{'  ** ALARM **' if 'ALARM' in row else ''}",
              flush=True)
    solved = sum(1 for r in rows if r.get("status") == "OPTIMAL")
    print(f"[gate] {solved}/{len(rows)} proved optimal; {len(alarms)} soundness alarms")
    for a in alarms:
        print(f"  !! {a['name']}: {a['ALARM']}")
    emit(args.out, {"mode": "gate", "secs": args.secs, "tier": args.tier,
                    "knobs": env_extra, "rows": rows,
                    "solved": solved, "alarms": len(alarms)})
    return 1 if alarms else 0


def ay_truncated(ay: dict) -> bool:
    """Did ay's LP row fail to reach a terminating Optimal?

    DERIVED, never stored — and that distinction is the whole point. The
    `truncated` KEY is only written on the branch that successfully parses a
    `diag_float_lp` line, so `HARDTIMEOUT`, `CRASH`, `TIMEOUT` and `NOPARSE`
    rows carried no key at all and `.get("truncated")` read them as CLEAN.
    Those are precisely the rows whose `t` is a deadline rather than a
    measurement, so they were the ones contaminating the "restricted to rows
    where both arms terminated" geomean this predicate exists to protect.
    Anything that is not a terminating `Optimal` is a FLOOR.
    """
    return ay.get("status") != "Optimal"


def run_ay_lp(inst: dict, secs: float) -> dict:
    """ay's root LP relaxation on the MEASUREMENT SCAFFOLD lane, not the shipped one.

    `AY_LP_ONLY=1` reaches `diag_float_lp`: ONE COLD WALK, no float-lane ladder,
    no eager-perturb retry, nothing certified — and `plain_cold` OFF, where the
    shipped continuous entry (`session::continuous_float_first_optimum`) has it
    unconditionally ON and retries a declined walk on a fresh `FloatLp`. So:

    * `primal_iters` / `dual_iters` / `primal_degen` are what this instrument is
      FOR and are sound — deterministic counters on a named lane;
    * `status` is the SCAFFOLD's status. `Stopped` here does not mean the solver
      cannot answer the LP; `ay-milp diag shipped-lp` is the lane that says that;
    * `t` on a non-`Optimal` row is the DEADLINE, i.e. a lower bound on the
      walk's cost, and `cmd_lp` divides it by Gurobi's completed time anyway.
      Ratios built from truncated rows are floors, not measurements.
    """
    env = dict(os.environ, AY_LP_ONLY="1")
    env.pop("AY_ROOT_CLOSURE", None)
    try:
        r = subprocess.run([AY_BIN, inst["file"], str(secs)], capture_output=True,
                           text=True, timeout=secs + 120, env=env)
    except (subprocess.TimeoutExpired, OSError):
        return {"status": "TIMEOUT", "t": secs + 120}
    txt = (r.stderr or "")
    m = re.search(r"diag_float_lp: status=(\w+).*?wall=([\d.]+)s", txt, re.S)
    if not m:
        return {"status": "NOPARSE", "t": None}
    it = re.search(r"primal=(\d+).*?dual=(\d+)", txt, re.S)
    # Degenerate-step count: how many pivots moved the objective by nothing. This is the
    # discriminator for what an LP-primal build should target — a walk that is mostly
    # degenerate wants an anti-degeneracy device, one that is not wants better pricing.
    dg = re.search(r"degen=(\d+)", txt)
    return {"status": m.group(1), "t": float(m.group(2)),
            # Which lane produced the row above, recorded in the artifact so a
            # later reader cannot mistake it for the shipped one.
            "lane": "scaffold-cold-walk(diag_float_lp): no ladder, no retry, plain_cold off",
            "truncated": m.group(1) != "Optimal",
            "primal_iters": int(it.group(1)) if it else None,
            "dual_iters": int(it.group(2)) if it else None,
            "primal_degen": int(dg.group(1)) if dg else None}


def run_gurobi_lp(inst: dict, secs: float) -> dict:
    """Gurobi on the SAME LP: the model with integrality dropped."""
    gp = gurobi()
    if not gp:
        return {"status": "SKIP"}
    try:
        env = gp.Env(params={"OutputFlag": 0})
        m = gp.read(inst["file"], env=env).relax()
        m.setParam("Threads", 1)
        m.setParam("TimeLimit", secs)
        t0 = time.monotonic()
        m.optimize()
        wall = time.monotonic() - t0
        st = "Optimal" if m.Status == 2 else f"STATUS{m.Status}"
        iters = None
        try:
            iters = int(m.IterCount)
        except Exception:
            iters = None
        m.dispose()
        return {"status": st, "t": wall, "iters": iters}
    except Exception as e:
        msg = str(e)
        return {"status": "SKIP", "why": "size-limited" if "size-limited" in msg else msg[:120]}


def cmd_lp(args) -> int:
    """W5: the LP-throughput gap, measured rather than inferred.

    The W1/W2 gate found that ay cannot afford a Gurobi-sized root cut pool because
    every adopted row is carried by every LP of every node. That makes LP cost the
    binding constraint on cut quality, and this is the number behind that claim: the
    same LP relaxation, solved by ay's float lane and by Gurobi, single-threaded.

    WHAT THE RATIO IS AND IS NOT. The ay arm is `run_ay_lp` — the measurement
    SCAFFOLD's cold walk, not the lane a solve runs (see that function). Two
    consequences the summary below now prints rather than leaving to the reader:

    * a row whose ay arm is not `Optimal` contributes `deadline / gurobi_time`,
      which is a FLOOR on the true ratio, not the ratio;
    * the ay arm runs with `plain_cold` OFF and with no declined-walk retry, so
      the ratio is against a configuration production does not use.

    The counter columns (`primal_iters`, `primal_degen`) carry neither caveat.
    """
    corpus = load_corpus(args.tier, args.only, args.limit, opt_only=False)
    print(f"[lp] {len(corpus)} instances, {args.secs}s each", flush=True)
    rows = []
    for i, inst in enumerate(corpus):
        a = run_ay_lp(inst, args.secs)
        g = run_gurobi_lp(inst, args.secs)
        row = {"name": inst["name"], "rows": inst.get("rows"), "cols": inst.get("cols"),
               "ay": a, "gurobi": g}
        ta, tg = a.get("t"), g.get("t")
        if ta is not None and tg is not None and tg > 0:
            row["ratio"] = ta / tg
        rows.append(row)
        rt = "" if row.get("ratio") is None else f"{row['ratio']:8.1f}x"
        print(f"  {i+1:3d}/{len(corpus)} {inst['name']:26s} ay={ta if ta is None else f'{ta:7.3f}s'} "
              f"grb={tg if tg is None else f'{tg:7.3f}s'} {rt}", flush=True)
        emit(args.out, {"mode": "lp", "secs": args.secs, "rows": rows}, quiet=True)
    emit(args.out, {"mode": "lp", "secs": args.secs, "rows": rows})
    # `is not None`, NOT truthiness. A ratio of exactly 0.0 is FALSY, and `wall=`
    # was printed at THREE decimals, so every LP ay answered in under a millisecond
    # reported `wall=0.000s`, produced ratio `0.0`, and was DELETED here — silently,
    # and only ever from the rows where ay is FASTEST. A geomean whose sample is
    # filtered by the metric's own smallness is not a geomean of the corpus.
    # (The emission now prints six decimals; this guard is what makes that reach
    # the summary, and it keeps the drop VISIBLE if a zero ever recurs.)
    have = [r for r in rows if r.get("ratio") is not None and r["ratio"] > 0.0]
    dropped_zero = [r for r in rows if r.get("ratio") == 0.0]
    if dropped_zero:
        print(f"[lp] {len(dropped_zero)} rows had ay wall below the emission's resolution "
              f"(ratio 0.0) and are EXCLUDED — these are ay's FASTEST rows, so the "
              f"geomean below is biased AGAINST ay by exactly this set: "
              + ", ".join(sorted(r["name"] for r in dropped_zero)))
    if have:
        # GEOMETRIC mean: these are ratios spanning orders of magnitude, and an
        # arithmetic mean of ratios is dominated by whichever instance is worst.
        logs = sorted(math.log(r["ratio"]) for r in have)
        geo = math.exp(sum(logs) / len(logs))
        med = math.exp(logs[len(logs) // 2])
        slower = sum(1 for r in have if r["ratio"] > 1.0)
        print(f"\n[lp] ay/gurobi LP time over {len(have)}: geomean {geo:.1f}x, "
              f"median {med:.1f}x, ay slower on {slower}")
        trunc = [r for r in have if ay_truncated(r["ay"])]
        print(f"[lp] ay arm = SCAFFOLD cold walk (no ladder, no retry, plain_cold off), "
              f"NOT the shipped lane; {len(trunc)}/{len(have)} ay rows did not reach Optimal, "
              f"so their ratios are FLOORS (deadline/gurobi), not measurements")
        if trunc:
            clean = [r["ratio"] for r in have if not ay_truncated(r["ay"])]
            if clean:
                clogs = sorted(math.log(x) for x in clean)
                print(f"[lp] restricted to the {len(clean)} rows where BOTH arms terminated: "
                      f"geomean {math.exp(sum(clogs)/len(clogs)):.1f}x, "
                      f"median {math.exp(clogs[len(clogs)//2]):.1f}x")
        worst = sorted(have, key=lambda r: -r["ratio"])[:8]
        for r in worst:
            flag = "  [FLOOR: ay truncated]" if ay_truncated(r["ay"]) else ""
            print(f"   {r['name']:26s} {r['ratio']:8.1f}x  ({r['rows']}x{r['cols']}){flag}")
    return 0


def cmd_par(args) -> int:
    """P0 of the parallel-B&B design: what are threads WORTH, and on which shapes?

    See the development design notes. Two questions,
    and they are different:

    1. **The prize.** How much does a solver that keeps its algorithms get from N
       threads, per instance? Gurobi at 1/2/4/8T answers that, and it is the number
       that says whether a parallel ay would be worth building for a given shape —
       measured, this is 5-8x on the dense-binary ladder and 1.13x on markshare.
    2. **The gate.** ay's nodes-to-proof, which is deterministic. When a parallel path
       exists, P1 requires its 1T node count to be byte-EQUAL to serial's; anything
       else means the workers are not running ay's search, and no number of threads
       repairs that. Recording serial's counts now makes that comparison possible
       later rather than requiring a re-run.

    ay is single-threaded, so its column is the 1T baseline until a parallel path lands.
    """
    corpus = load_corpus(args.tier, args.only, args.limit, opt_only=False)
    threads = [int(t) for t in (args.threads or "1,2,4,8").split(",")]
    print(f"[par] {len(corpus)} instances, gurobi threads {threads}, {args.secs}s each",
          flush=True)
    rows = []
    for i, inst in enumerate(corpus):
        a = run_ay(inst, args.secs, parse_knobs(args.knob), mode="solve")
        row = {"name": inst["name"], "ay_1t": a, "gurobi": {}}
        for t in threads:
            g = run_gurobi(inst, args.secs, threads=t)
            row["gurobi"][str(t)] = g
        g1 = row["gurobi"].get(str(threads[0]), {})
        gn = row["gurobi"].get(str(threads[-1]), {})
        # The parallel speedup is only meaningful where BOTH thread counts proved.
        if g1.get("status") == gn.get("status") == "OPTIMAL" and (gn.get("t") or 0) > 0:
            row["gurobi_speedup"] = (g1.get("t") or 0) / gn["t"]
        rows.append(row)
        sp = row.get("gurobi_speedup")
        print(f"  {i+1:3d}/{len(corpus)} {inst['name']:26s} "
              f"ay1T={a.get('status','?'):9s} {a.get('t',0):6.1f}s nodes={a.get('nodes')} | "
              f"grb {threads[0]}T={g1.get('t')} {threads[-1]}T={gn.get('t')} "
              f"{'' if sp is None else f'speedup={sp:.2f}x'}", flush=True)
        emit(args.out, {"mode": "par", "secs": args.secs, "threads": threads, "rows": rows},
             quiet=True)
    emit(args.out, {"mode": "par", "secs": args.secs, "threads": threads, "rows": rows})
    sp = [r["gurobi_speedup"] for r in rows if r.get("gurobi_speedup")]
    if sp:
        logs = sorted(math.log(s) for s in sp)
        print(f"\n[par] gurobi {threads[0]}T->{threads[-1]}T speedup over {len(sp)}: "
              f"geomean {math.exp(sum(logs)/len(logs)):.2f}x, "
              f"median {math.exp(logs[len(logs)//2]):.2f}x, "
              f"max {max(sp):.2f}x")
        print("[par] that geomean IS the ceiling a parallel ay could buy on this set — "
              "and ay currently buys none of it.")
    return 0


def cmd_audit(args) -> int:
    """Head-to-head against Gurobi, judged on correctness FIRST and speed second.

    Two different claims live here and they must not be blurred:

    CORRECTNESS. ay's OPTIMAL is an exact-rational optimum with a re-checkable
    certificate; Gurobi's is an optimum *within its tolerances*. MIPLIB's reference
    value is the independent judge. Gurobi is run twice — once at its shipped defaults
    (which is what a user actually gets) and once at ``MIPGap=0``, so a disagreement is
    attributed to the default gap rather than being passed off as an error. A
    disagreement that survives ``MIPGap=0`` is a genuine numerical miss.

    SPEED. Time-to-proof on the instances where both prove. Reported as a per-instance
    win/loss, never as an average — an average over a corpus where one solver times out
    is not a measurement of anything.
    """
    corpus = load_corpus(args.tier, args.only, args.limit, opt_only=True)
    print(f"[audit] {len(corpus)} instances, {args.secs}s each", flush=True)
    rows = []
    for i, inst in enumerate(corpus):
        ref = inst.get("ref_obj")
        a = run_ay(inst, args.secs, parse_knobs(args.knob), mode="solve")
        g = run_gurobi(inst, args.secs)
        row = {"name": inst["name"], "ref_obj": ref, "ay": a, "gurobi": g}
        # Only re-run Gurobi exactly when its default-tolerance answer disagrees; a
        # second full solve on every instance would double the corpus cost for nothing.
        if g.get("status") == "OPTIMAL" and not close_enough(g.get("obj"), ref, args.tol):
            row["gurobi_exact"] = run_gurobi_tight(inst, args.secs)
        rows.append(row)
        verdict = classify(row, args.tol)
        row["verdict"] = verdict
        print(f"  {i+1:3d}/{len(corpus)} {inst['name']:26s} "
              f"ay={a.get('status', '?'):9s} {a.get('t', 0):6.1f}s | "
              f"grb={g.get('status', '?'):9s} {g.get('t', 0):6.1f}s | {verdict}", flush=True)
    emit(args.out, {"mode": "audit", "secs": args.secs, "tier": args.tier,
                    "knobs": parse_knobs(args.knob), "rows": rows})
    summarise_audit(rows)
    return 0


def run_gurobi_tight(inst: dict, secs: float) -> dict:
    gp = gurobi()
    if not gp:
        return {"status": "SKIP"}
    try:
        env = gp.Env(params={"OutputFlag": 0})
        m = gp.read(inst["file"], env=env)
        m.setParam("Threads", 1)
        m.setParam("TimeLimit", secs)
        m.setParam("MIPGap", 0.0)
        m.setParam("MIPGapAbs", 0.0)
        m.optimize()
        st = "OPTIMAL" if m.Status == 2 else f"STATUS{m.Status}"
        obj = m.ObjVal if m.SolCount > 0 else None
        m.dispose()
        return {"status": st, "obj": obj}
    except Exception as e:
        return {"status": "SKIP", "why": str(e)[:200]}


def classify(row: dict, tol: float) -> str:
    ref, a, g = row.get("ref_obj"), row["ay"], row["gurobi"]
    ao, go = a.get("status"), g.get("status")
    # Correctness first: a wrong proven optimum outranks every timing result there is.
    if ao == "OPTIMAL" and not close_enough(a.get("obj"), ref, tol):
        return "!! AY-WRONG"
    if go == "OPTIMAL" and not close_enough(g.get("obj"), ref, tol):
        tight = row.get("gurobi_exact", {})
        if tight.get("status") == "OPTIMAL" and close_enough(tight.get("obj"), ref, tol):
            return "grb-default-gap"   # its shipped tolerance, not a numerical error
        return "!! GRB-WRONG"
    if ao == "OPTIMAL" and go != "OPTIMAL":
        return "AY-ONLY"
    if go == "OPTIMAL" and ao != "OPTIMAL":
        return "GRB-ONLY"
    if ao == go == "OPTIMAL":
        ta, tg = a.get("t") or 0.0, g.get("t") or 0.0
        if ta < tg * 0.95:
            return f"AY-FASTER {tg/max(ta,1e-9):.1f}x"
        if tg < ta * 0.95:
            return f"grb-faster {ta/max(tg,1e-9):.1f}x"
        return "tie"
    return "neither"


def summarise_audit(rows: list[dict]) -> None:
    tally: dict[str, int] = {}
    for r in rows:
        key = r["verdict"].split()[0]
        tally[key] = tally.get(key, 0) + 1
    print("\n[audit] " + ", ".join(f"{k}={v}" for k, v in sorted(tally.items())))
    wrong = [r for r in rows if r["verdict"].startswith("!!")]
    if wrong:
        print("[audit] CORRECTNESS EVENTS:")
        for r in wrong:
            print(f"  {r['verdict']:14s} {r['name']:24s} ref={r['ref_obj']} "
                  f"ay={r['ay'].get('obj')} grb={r['gurobi'].get('obj')}")
    gap = [r for r in rows if r["verdict"] == "grb-default-gap"]
    if gap:
        print(f"[audit] {len(gap)} instances where Gurobi's DEFAULT tolerance returned a "
              f"non-optimal value it labelled OPTIMAL:")
        for r in gap:
            print(f"  {r['name']:24s} ref={r['ref_obj']} grb={r['gurobi'].get('obj')} "
                  f"ay={r['ay'].get('obj')}")
    both = [r for r in rows if r["ay"].get("status") == "OPTIMAL"
            and r["gurobi"].get("status") == "OPTIMAL"]
    faster = [r for r in both if (r["ay"].get("t") or 0) < (r["gurobi"].get("t") or 0) * 0.95]
    print(f"[audit] both prove on {len(both)}; ay faster on {len(faster)}")
    for r in sorted(faster, key=lambda r: -(r["gurobi"]["t"] / max(r["ay"]["t"], 1e-9)))[:10]:
        print(f"  {r['name']:24s} ay {r['ay']['t']:.2f}s vs grb {r['gurobi']['t']:.2f}s")


def cmd_compare(args) -> int:
    a = json.loads(pathlib.Path(args.base).read_text())
    b = json.loads(pathlib.Path(args.head).read_text())
    ar = {r["name"]: r for r in a["rows"]}
    br = {r["name"]: r for r in b["rows"]}
    names = sorted(set(ar) | set(br))
    mode = a.get("mode")
    if mode == "closure":
        print(f"{'instance':26s} {'base':>9s} {'head':>9s} {'delta':>9s}")
        tot = n = 0.0
        for nm in names:
            ca, cb = ar.get(nm, {}).get("closure"), br.get(nm, {}).get("closure")
            if ca is None or cb is None:
                continue
            d = cb - ca
            tot += d
            n += 1
            if abs(d) > 1e-9:
                print(f"{nm:26s} {100*ca:8.2f}% {100*cb:8.2f}% {100*d:+8.2f}pp")
        if n:
            print(f"\nmean delta {100*tot/n:+.3f}pp over {int(n)} instances "
                  f"(total {100*tot:+.2f}pp)")
        return 0
    # gate/solve comparison: verdict changes first, then wall.
    #
    # A verdict change is not one kind of event. FEASIBLE -> OPTIMAL is a proof gained;
    # OPTIMAL -> FEASIBLE is a proof LOST; FEASIBLE -> UNKNOWN means the run stopped
    # finding any incumbent at all, which is worse than either. Scoring them together as
    # "changes" hides whether a build got better or worse, so they are tallied apart.
    rank = {"OPTIMAL": 3, "INFEASIBLE": 3, "FEASIBLE": 2, "UNKNOWN": 1,
            "HARDTIMEOUT": 0, "TIMEOUT": 0, "CRASH": 0, "NOOUTPUT": 0}
    regressed = improved = 0
    verdict_lost = verdict_gained = 0
    for nm in names:
        x, y = ar.get(nm, {}), br.get(nm, {})
        sx, sy = x.get("status"), y.get("status")
        if sx != sy:
            dr = rank.get(sy, 1) - rank.get(sx, 1)
            tag = "LOST   " if dr < 0 else ("gained " if dr > 0 else "changed")
            if dr < 0:
                verdict_lost += 1
            elif dr > 0:
                verdict_gained += 1
            print(f"VERDICT {tag} {nm:24s} {sx} -> {sy}")
        elif sx == "OPTIMAL" and not close_enough(x.get("obj"), y.get("obj")):
            print(f"OBJECTIVE {nm:22s} {x.get('obj')} -> {y.get('obj')}   ** ALARM **")
            verdict_lost += 1
    for nm in names:
        x, y = ar.get(nm, {}), br.get(nm, {})
        if x.get("status") == y.get("status") == "OPTIMAL":
            tx, ty = x.get("t"), y.get("t")
            if tx and ty and abs(ty - tx) > 0.1 + 0.10 * tx:
                tag = "SLOWER" if ty > tx else "faster"
                if ty > tx:
                    regressed += 1
                else:
                    improved += 1
                print(f"{tag:8s} {nm:24s} {tx:7.2f}s -> {ty:7.2f}s  ({100*(ty-tx)/tx:+.0f}%)")
    pa = sum(1 for r in a["rows"] if r.get("status") in ("OPTIMAL", "INFEASIBLE"))
    pb = sum(1 for r in b["rows"] if r.get("status") in ("OPTIMAL", "INFEASIBLE"))
    print(f"\nproved: {pa} -> {pb}   verdicts: {verdict_gained} gained, {verdict_lost} LOST"
          f"   wall: {improved} faster, {regressed} slower")
    # A build that loses a verdict or slows more instances than it speeds has not earned
    # its default, whatever a leading indicator said about it.
    return 1 if (verdict_lost or pb < pa) else 0


def emit(path: str | None, payload: dict, quiet: bool = False) -> None:
    if not path:
        return
    p = pathlib.Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(payload, indent=1))
    if not quiet:
        print(f"[out] {p}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(p):
        p.add_argument("--tier", default="gurobi",
                       choices=["gurobi", "mid", "large", "all"])
        p.add_argument("--only", nargs="*")
        p.add_argument("--limit", type=int, default=0)
        p.add_argument("--secs", type=float, default=30.0)
        p.add_argument("--out")
        p.add_argument("--knob", nargs="*", help="env knob(s), e.g. AY_MILP_NO_ZERO_HALF=1")

    for name, fn in (("closure", cmd_closure), ("baseline", cmd_baseline),
                     ("ablate", cmd_ablate), ("gate", cmd_gate), ("audit", cmd_audit),
                     ("lp", cmd_lp), ("par", cmd_par)):
        p = sub.add_parser(name)
        common(p)
        if name in ("gate", "audit"):
            p.add_argument("--tol", type=float, default=REL_TOL)
        if name == "par":
            p.add_argument("--threads", default="1,2,4,8",
                           help="comma-separated Gurobi thread counts (default 1,2,4,8)")
        if name == "closure":
            p.add_argument("--with-gurobi", action="store_true",
                           help="also measure Gurobi's root bound, head-to-head")
        p.set_defaults(fn=fn)

    c = sub.add_parser("compare")
    c.add_argument("base")
    c.add_argument("head")
    c.set_defaults(fn=cmd_compare)

    args = ap.parse_args()
    if getattr(args, "tier", None) == "all":
        args.tier = None
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
