#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0
"""milp_portfolio.py — measure AY's configuration space so AY can tune ITSELF.

ay-milp reads ~300 tuning decisions from `std::env::var` at scattered call sites.
Every one of those is a setting a *user* would otherwise have to discover, and a
solver that needs its user to know 300 environment variables is not competitive
with one that reads the model and decides. This tool exists to remove them: it
measures which configuration wins on which model shape, so the winning policy can
be compiled into the engine as a selector rather than documented as a knob.

Two questions, deliberately separated:

``portfolio``  *Is the capability already there?*
    Every arm on every instance. The union over arms — the ORACLE — is what ay
    could prove if it always guessed right. Oracle minus default is the coverage
    ay is leaving on the floor with a static configuration, and it is reachable
    by selection alone. Instances no arm proves are a genuinely missing
    capability and need new algorithms, not tuning. Conflating those two is what
    makes a gap look unbounded when part of it is free.

``baseline``   *What is the bar?*
    Gurobi at one thread on the same bytes and the same budget.

Soundness outranks speed everywhere here. An arm whose objective disagrees with
the MIPLIB reference is an ALARM: it is never counted as a win, never averaged
into a score, and is reported separately, because a fast wrong answer is not a
weaker version of a right one.

Wall times from a parallel run are contended and are upper bounds — good enough
to rank coverage, not to claim a speedup. Time claims get a serial rerun.

Usage:
  scripts/milp_portfolio.py portfolio --secs 30 --jobs 10 --out the development design notes
  scripts/milp_portfolio.py baseline  --secs 30 --out the development design notes
  scripts/milp_portfolio.py analyze   the development design notes --gurobi the development design notes
"""
from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import pathlib
import re
import subprocess
import sys
import threading
import time

# B20: the env locator is retired; pass --corpus <dir> or symlink the corpus
# at the default path.
def _corpus_dir() -> pathlib.Path:
    argv = sys.argv
    if "--corpus" in argv:
        return pathlib.Path(argv[argv.index("--corpus") + 1])
    return pathlib.Path.home() / "ay-bench" / "milp"

CORPUS = _corpus_dir()
MANIFEST = CORPUS / "manifest.json"
AY_BIN = os.path.abspath(os.environ.get("AY_BIN", "./target/release/examples/mps_solve"))
REL_TOL = 1e-6

PROVED = ("OPTIMAL", "INFEASIBLE")

# The arms. Each is a hypothesis about a regime where a non-default setting pays.
# They are deliberately coarse: the point is to find WHICH DECISIONS MATTER and on
# which shapes, not to land a final constant. A no-op arm costs one run and shows
# up as a duplicate of default, which is itself a useful (negative) result.
# B38: each arm is (env_extra, cli_args) — the retired knob env spellings ride
# the shared engine CLI now; names with surviving env verdicts stay env.
ARMS: dict[str, tuple[dict[str, str], list[str]]] = {
    "default":     ({}, []),
    # Root cut volume. The campaign measured 40x10 as +9.25pp closure but -7
    # verdicts GLOBALLY; that is exactly the shape of a setting that should be
    # selected per-instance rather than switched on or off for everyone.
    "cuts-big":    ({}, ["--root-cuts-per-round", "40", "--gmi-rounds", "10"]),
    "cuts-mid":    ({}, ["--root-cuts-per-round", "16", "--gmi-rounds", "5"]),
    "cuts-off":    ({}, ["--no-cuts"]),
    # Presolve / probing.
    "probe":       ({}, ["--root-probe", "--root-probe-all"]),
    "singleton":   ({"AY_MILP_SINGLETON_SUB": "1"}, []),
    # Tree.
    "dfs":         ({}, ["--dfs"]),
    "noplunge":    ({}, ["--no-plunge"]),
    "vsids":       ({}, ["--vsids"]),
    "nodecuts":    ({}, ["--node-cuts"]),
    # LP.
    "devex":       ({"AY_MILP_DEVEX": "1"}, []),
    # One combination, because the terminal finding of the previous campaign was
    # that single-component transplants each regress; a saddle is crossed by
    # moving more than one coordinate.
    "cuts-probe":  ({},
                    ["--root-cuts-per-round", "40", "--gmi-rounds", "10",
                     "--root-probe", "--root-probe-all"]),
}


def load_corpus(tier: str, only: list[str] | None, limit: int) -> list[dict]:
    if not MANIFEST.exists():
        sys.exit(f"no corpus manifest at {MANIFEST}")
    man = json.loads(MANIFEST.read_text())
    out = []
    for name, e in man["instances"].items():
        if tier != "all" and e.get("tier") != tier:
            continue
        if only and name not in only:
            continue
        if e.get("ref_status") != "opt":
            continue
        out.append({"name": name, **e})
    out.sort(key=lambda e: (e.get("cols") or 0, e["name"]))
    return out[:limit] if limit else out


def close_enough(a, b, tol: float = REL_TOL) -> bool:
    if a is None or b is None:
        return False
    return abs(a - b) <= tol * max(1.0, abs(a), abs(b))


def run_ay(inst: dict, secs: float, arm: tuple[dict[str, str], list[str]]) -> dict:
    env_extra, cli_args = arm
    env = dict(os.environ)
    env.pop("AY_ROOT_CLOSURE", None)
    env.update(env_extra)
    t0 = time.monotonic()
    try:
        r = subprocess.run([AY_BIN, inst["file"], str(secs), *cli_args],
                           capture_output=True,
                           text=True, timeout=secs + 120, env=env)
    except subprocess.TimeoutExpired:
        return {"status": "HARDTIMEOUT", "t": secs + 120}
    except OSError as e:
        return {"status": "CRASH", "err": str(e), "t": time.monotonic() - t0}
    wall = time.monotonic() - t0
    out = (r.stdout or "").strip().splitlines()
    if not out:
        return {"status": "CRASH" if r.returncode else "NOOUTPUT",
                "err": (r.stderr or "").strip()[-300:], "t": wall}
    f = out[-1].split()
    val = None
    if len(f) > 1 and f[1] != "-":
        try:
            val = float(f[1])
        except ValueError:
            val = None
    nodes = None
    if len(f) > 3:
        try:
            nodes = int(f[3])
        except ValueError:
            nodes = None
    return {"status": f[0], "obj": val, "t": wall, "nodes": nodes}


def run_gurobi(inst: dict, secs: float, threads: int = 1) -> dict:
    try:
        import gurobipy as gp
    except ImportError:
        return {"status": "SKIP", "why": "gurobipy missing"}
    t0 = time.monotonic()
    try:
        env = gp.Env(params={"OutputFlag": 0})
        m = gp.read(inst["file"], env=env)
        m.setParam("Threads", threads)
        m.setParam("TimeLimit", secs)
        m.optimize()
    except Exception as e:
        msg = str(e)
        return {"status": "SKIP",
                "why": "size-limited" if "size-limited" in msg else msg[:200],
                "t": time.monotonic() - t0}
    wall = time.monotonic() - t0
    st = {2: "OPTIMAL", 3: "INFEASIBLE", 5: "UNBOUNDED", 9: "TIMEOUT",
          11: "INTERRUPTED", 13: "SUBOPTIMAL"}.get(m.Status, f"STATUS{m.Status}")
    obj = None
    try:
        obj = m.ObjVal if m.SolCount > 0 else None
    except Exception:
        pass
    nodes = None
    try:
        nodes = int(m.NodeCount)
    except Exception:
        pass
    return {"status": st, "obj": obj, "t": wall, "nodes": nodes}


# A float solver that stops at a RELATIVE MIP GAP and reports "optimal" is doing what it
# documents, not answering wrongly. Gurobi's default MIPGap is 1e-4, so an objective within
# that of the reference is expected behaviour and must not be scored as an error — reporting
# it as one would be a false alarm, and false alarms are how a soundness signal gets ignored.
# Beyond that band there is no tolerance story left and the answer is simply wrong.
GAP_BAND = 1e-4


def score(inst: dict, r: dict, gap_band: float = 0.0) -> dict:
    """Classify the answer against the reference.

    Three outcomes, kept apart on purpose:
      - agreement (within REL_TOL),
      - ``gap`` — outside REL_TOL but inside the solver's own documented stopping gap,
      - ``alarm`` — outside both, i.e. a claimed-proved objective that is simply wrong.
    """
    ref = inst.get("ref_obj")
    if r.get("status") not in PROVED or ref is None or r.get("obj") is None:
        return r
    if close_enough(r["obj"], ref):
        return r
    rel = abs(r["obj"] - ref) / max(1.0, abs(ref))
    if gap_band and rel <= gap_band:
        r["gap_slack"] = rel
    else:
        r["alarm"] = f"obj {r['obj']} != ref {ref} (rel {rel:.3e})"
    return r


def cmd_portfolio(args) -> int:
    insts = load_corpus(args.tier, args.only, args.limit)
    arms = {k: v for k, v in ARMS.items() if not args.arms or k in args.arms}
    jobs = [(i, a) for i in insts for a in arms]
    print(f"[portfolio] {len(insts)} instances x {len(arms)} arms = {len(jobs)} runs, "
          f"{args.secs}s cap, {args.jobs} workers", flush=True)
    rows: dict[str, dict] = {i["name"]: {"name": i["name"],
                                        "rows_n": i.get("rows"), "cols_n": i.get("cols"),
                                        "nnz": i.get("nnz"), "ints": i.get("ints"),
                                        "bins": i.get("bins"), "ref_obj": i.get("ref_obj"),
                                        "arms": {}} for i in insts}
    lock = threading.Lock()
    done = [0]
    out_path = pathlib.Path(args.out) if args.out else None

    def work(job):
        inst, arm = job
        r = score(inst, run_ay(inst, args.secs, arms[arm]))
        with lock:
            rows[inst["name"]]["arms"][arm] = r
            done[0] += 1
            n = done[0]
            if r.get("alarm"):
                print(f"  ** ALARM ** {inst['name']:24s} {arm:12s} {r['alarm']}", flush=True)
            if n % 25 == 0 or n == len(jobs):
                print(f"  [{n}/{len(jobs)}]", flush=True)
                if out_path:  # checkpoint: a long run must survive being killed
                    out_path.parent.mkdir(parents=True, exist_ok=True)
                    out_path.write_text(json.dumps(
                        {"mode": "portfolio", "secs": args.secs, "arms": list(arms),
                         "contended": args.jobs > 1, "rows": list(rows.values())}, indent=1))

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        list(ex.map(work, jobs))

    payload = {"mode": "portfolio", "secs": args.secs, "arms": list(arms),
               "contended": args.jobs > 1, "rows": list(rows.values())}
    if out_path:
        out_path.write_text(json.dumps(payload, indent=1))
        print(f"[out] {out_path}")
    summarize(payload, None)
    return 0


def cmd_baseline(args) -> int:
    insts = load_corpus(args.tier, args.only, args.limit)
    print(f"[baseline] gurobi 1T, {len(insts)} instances, {args.secs}s", flush=True)
    rows = []
    for n, i in enumerate(insts, 1):
        # The gap band applies to the FLOAT solver only. ay is exact: it does not stop at a
        # relative gap, so it has no documented slack to be forgiven, and any disagreement
        # from it is a real alarm. Granting ay the same band would hide exactly the class of
        # defect ay exists to make impossible.
        r = score(i, run_gurobi(i, args.secs, threads=args.threads), gap_band=GAP_BAND)
        r["name"] = i["name"]
        rows.append(r)
        if r.get("alarm"):
            print(f"  ** ALARM ** {i['name']:24s} {r['alarm']}", flush=True)
        elif r.get("gap_slack"):
            print(f"  [gap]      {i['name']:24s} rel {r['gap_slack']:.3e} "
                  f"(within documented MIPGap)", flush=True)
        if n % 20 == 0:
            print(f"  [{n}/{len(insts)}]", flush=True)
    n_alarm = sum(1 for r in rows if r.get("alarm"))
    n_gap = sum(1 for r in rows if r.get("gap_slack"))
    print(f"proved {sum(1 for r in rows if r['status'] in PROVED)}/{len(rows)}   "
          f"wrong {n_alarm}   within-gap {n_gap}")
    payload = {"mode": "baseline", "secs": args.secs, "threads": args.threads,
               "gap_band": GAP_BAND, "rows": rows}
    if args.out:
        p = pathlib.Path(args.out)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(payload, indent=1))
        print(f"[out] {p}")
    print(f"gurobi proved {sum(1 for r in rows if r['status'] in PROVED)}/{len(rows)}")
    return 0


def summarize(pf: dict, grb: dict | None) -> None:
    rows = pf["rows"]
    arms = pf["arms"]
    alarms = [(r["name"], a, d["alarm"]) for r in rows for a, d in r["arms"].items()
              if d.get("alarm")]
    print()
    print(f"{'arm':14s} {'proved':>7s} {'of':>4s}")
    per_arm = {}
    for a in arms:
        n = sum(1 for r in rows if r["arms"].get(a, {}).get("status") in PROVED
                and not r["arms"][a].get("alarm"))
        per_arm[a] = n
        print(f"{a:14s} {n:7d} {len(rows):4d}")
    oracle = [r for r in rows
              if any(d.get("status") in PROVED and not d.get("alarm")
                     for d in r["arms"].values())]
    base = per_arm.get("default", 0)
    print(f"\nORACLE (union of arms) {len(oracle)}/{len(rows)}   "
          f"default {base}   reachable-by-selection +{len(oracle)-base}")
    if grb:
        g = {r["name"]: r for r in grb["rows"]}
        gp_ = {n for n, r in g.items() if r["status"] in PROVED and not r.get("alarm")}
        op = {r["name"] for r in oracle}
        dp = {r["name"] for r in rows
              if r["arms"].get("default", {}).get("status") in PROVED}
        print(f"gurobi 1T proved {len(gp_)}")
        print(f"  gurobi-only vs default : {len(gp_ - dp)}")
        print(f"  gurobi-only vs ORACLE  : {len(gp_ - op)}   <- genuinely missing capability")
        print(f"  ay-only  vs gurobi     : {len(op - gp_)}")
    if alarms:
        print(f"\n** {len(alarms)} SOUNDNESS ALARMS **")
        for nm, a, why in alarms[:20]:
            print(f"  {nm:24s} {a:12s} {why}")
    else:
        print("\nsoundness: 0 alarms")


def cmd_analyze(args) -> int:
    pf = json.loads(pathlib.Path(args.portfolio).read_text())
    grb = json.loads(pathlib.Path(args.gurobi).read_text()) if args.gurobi else None
    summarize(pf, grb)
    # Per-instance winner, which is the selector's training signal.
    if args.winners:
        print(f"\n{'instance':26s} {'best arm':14s} {'t':>8s}  (proved-only)")
        for r in sorted(pf["rows"], key=lambda r: r["name"]):
            ok = [(a, d) for a, d in r["arms"].items()
                  if d.get("status") in PROVED and not d.get("alarm")]
            if not ok:
                continue
            a, d = min(ok, key=lambda kv: kv[1].get("t", 1e9))
            dflt = r["arms"].get("default", {})
            mark = "" if a == "default" else "  <-- selection wins"
            if dflt.get("status") not in PROVED:
                mark = "  <-- ONLY non-default proves"
            print(f"{r['name']:26s} {a:14s} {d.get('t', 0):8.2f}{mark}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("portfolio")
    p.add_argument("--tier", default="gurobi")
    p.add_argument("--only", nargs="*")
    p.add_argument("--limit", type=int, default=0)
    p.add_argument("--secs", type=float, default=30.0)
    p.add_argument("--jobs", type=int, default=8)
    p.add_argument("--arms", nargs="*")
    p.add_argument("--out")
    p.set_defaults(fn=cmd_portfolio)

    b = sub.add_parser("baseline")
    b.add_argument("--tier", default="gurobi")
    b.add_argument("--only", nargs="*")
    b.add_argument("--limit", type=int, default=0)
    b.add_argument("--secs", type=float, default=30.0)
    b.add_argument("--threads", type=int, default=1)
    b.add_argument("--out")
    b.set_defaults(fn=cmd_baseline)

    a = sub.add_parser("analyze")
    a.add_argument("portfolio")
    a.add_argument("--gurobi")
    a.add_argument("--winners", action="store_true")
    a.set_defaults(fn=cmd_analyze)

    args = ap.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    raise SystemExit(main())
