#!/usr/bin/env python3
# ay-script: pb-sweep
"""Pseudo-Boolean sweep harness — AY-PB vs a reference (RoundingSat) on OPB/WBO.

Parses PB-competition output (s SATISFIABLE/UNSATISFIABLE/OPTIMUM FOUND, o <obj>),
records solved-count, and cross-checks the optimum value / decision verdict between
solvers (a disagreement on UNSAT-vs-SAT or on a *proven* optimum = soundness bug).

Every child runs under the same persisted memory/core envelope.  The shared
planner may reduce --workers to fit RAM, and NBCORE is capped to the planner's
per-child share so concurrent portfolio solvers cannot each claim the machine.
"""
import argparse, concurrent.futures as cf, glob, json, math, os, signal, subprocess, sys, tempfile, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _oom_guard import (copy_stream_limited, plan_solver_resources,
                        run_captured, warn_concurrent_build)

def parse_pb(out):
    status, obj = "unknown", None
    lines = (out or "").splitlines() if isinstance(out, str) else out
    for line in lines:
        if isinstance(line, bytes):
            line = line.decode("utf-8", errors="replace")
        s = line.strip()
        if s.startswith("o "):
            try: obj = int(s.split()[1])
            except (ValueError, IndexError): pass
        elif s == "s SATISFIABLE": status = "sat"
        elif s == "s UNSATISFIABLE": status = "unsat"
        elif s == "s OPTIMUM FOUND": status = "optimum"
        elif s == "s UNKNOWN": status = "unknown"
    return status, obj

def _decompress_to_temp(f):
    """Return (usable_path, temp_path_or_None). Solvers read plain OPB/WBO on
    argv (exactly as the competition harness passes uncompressed paths); a
    compressed corpus file is decompressed to a temp file first, else the solver
    reads the raw compressed bytes as UTF-8 and spuriously reports UNKNOWN."""
    openers = {".xz": ("lzma", "open"), ".bz2": ("bz2", "open"), ".gz": ("gzip", "open")}
    ext = os.path.splitext(f)[1].lower()
    if ext not in openers:
        return f, None
    import importlib, tempfile
    mod = importlib.import_module(openers[ext][0])
    inner_ext = os.path.splitext(os.path.splitext(f)[0])[1] or ".opb"
    fd, tmp = tempfile.mkstemp(suffix=inner_ext, prefix="pbsweep-")
    try:
        with mod.open(f, "rb") as src, os.fdopen(fd, "wb") as dst:
            copy_stream_limited(src, dst)
    except Exception:
        try: os.remove(tmp)
        except OSError: pass
        raise
    return tmp, tmp


def run_one(name, cmd_tmpl, f, timeout_s, env=None, memlimit_mb=0,
            resource_envelope=None):
    def result(**fields):
        row = {"solver": name, "file": os.path.basename(f), **fields}
        if resource_envelope is not None:
            row["resource_envelope"] = resource_envelope
        return row

    try:
        solve_path, tmp_path = _decompress_to_temp(f)
    except Exception as e:
        return result(status="error", obj=None, time=0.0,
                      err=f"decompress: {e}")
    if name.startswith("ay"):
        cmd = [cmd_tmpl, "pb", "solve", "-t", str(int(timeout_s*1000))]
        if "native" in name:
            cmd.append("--native")
        cmd.append(solve_path)
    else:  # roundingsat: reads OPB on argv; external timeout
        cmd = [cmd_tmpl, solve_path]
    start = time.monotonic()
    try:
        captured = run_captured(
            cmd, memlimit_mb, timeout_s,
            label=f"pb_sweep.py[{name}]", env=env,
        )
        status, obj = parse_pb(captured.stdout)
        if captured.memout:
            status = "memout"
        elif captured.timed_out:
            status = "timeout"
        elif captured.cancelled or captured.output_truncated:
            status = "error"
    except Exception as e:
        if tmp_path:
            try: os.remove(tmp_path)
            except OSError: pass
        return result(status="error", obj=None, time=0.0, err=str(e))
    finally:
        if tmp_path:
            try: os.remove(tmp_path)
            except OSError: pass
    el = captured.wall_sec
    return result(status=status, obj=obj, time=round(el, 2))

def solved(s): return s in ("sat", "unsat", "optimum")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir"); ap.add_argument("--list")
    ap.add_argument("--timeout", type=float, default=60.0)
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--nbcore", type=int, default=None,
                    help="optional per-child NBCORE reduction; cannot exceed "
                         "the shared planner's admitted core share")
    ap.add_argument("--mem-mb", type=int, default=4000,
                    help="per-child RAM envelope (MiB): sizes the OOM worker cap, is "
                         "exported as MEMLIMIT for solvers that honor it (the ay-pb "
                         "binary; the main ay binary's `pb` subcommand and roundingsat "
                         "ignore it), and is enforced on EVERY child by a harness RSS "
                         "watchdog kill (status: memout)")
    ap.add_argument("--solver", action="append", default=[])
    ap.add_argument("--out", default="pb_sweep.json")
    ap.add_argument("--limit", type=int, default=0)
    args = ap.parse_args()

    if args.workers <= 0:
        ap.error("--workers must be positive")
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        ap.error("--timeout must be finite and positive")
    if args.mem_mb <= 0:
        ap.error("--mem-mb must be positive; unenveloped sweeps are refused")
    if args.nbcore is not None and args.nbcore <= 0:
        ap.error("--nbcore must be positive")
    if args.limit < 0:
        ap.error("--limit cannot be negative")

    # OOM guard: plan before constructing any child environment or job list.
    warn_concurrent_build()
    requested_workers = args.workers
    plan = plan_solver_resources(
        requested_workers, mem_floor_mb=args.mem_mb, label="pb_sweep.py"
    )
    args.workers = plan.jobs
    # --mem-mb is an explicit ceiling, while the planner verifies that every
    # admitted worker fits at least that much.  A user NBCORE may reduce the
    # planned share but may never enlarge it.
    memlimit_mb = min(args.mem_mb, plan.memlimit_mb)
    nbcore = min(args.nbcore, plan.nbcore) if args.nbcore else plan.nbcore
    env = dict(os.environ)
    env["MEMLIMIT"] = str(memlimit_mb)
    env["NBCORE"] = str(nbcore)

    # Enforce the memory budget inside each child too. Two layers, because
    # only the ay-pb binary reads the MEMLIMIT env (crates/ay-pb/src/bin/ay.rs);
    # the default ./target/release/ay `pb` subcommand has no memory knob at all
    # and would otherwise run unbounded, sibling-blind (the 2026-07-11 panic
    # arithmetic):
    #   1. authoritative MEMLIMIT/NBCORE env for self-enforcing solvers;
    #   2. exact process-group RSS watchdog for everything else.
    resource_envelope = {
        "requested_workers": requested_workers,
        "workers": args.workers,
        "memlimit_mb_per_child": memlimit_mb,
        "nbcore_per_child": nbcore,
        "headroom_mb": plan.headroom_mb,
        "planner": "scripts/_oom_guard.py",
        "enforcement": "rss_watchdog(grace=0)+MEMLIMIT/NBCORE",
    }

    solvers = dict(s.split("=", 1) for s in args.solver) or {"ay": "./target/release/ay"}
    files = []
    if args.dir:
        for ext in ("*.opb", "*.wbo", "*.opb.bz2", "*.opb.xz", "*.wbo.xz", "*.wbo.bz2", "*.opb.gz", "*.wbo.gz"):
            files += glob.glob(os.path.join(args.dir, "**", ext), recursive=True)
    if args.list:
        with open(args.list) as list_file:
            files += [line.split()[0] for line in list_file
                      if line.strip() and not line.startswith("#")]
    files = [f for f in files if os.path.exists(f)]
    # Dedup instances present in both compressed and plain form (e.g. X.opb and
    # X.opb.xz): key on the path with any compression suffix stripped, and prefer
    # the PLAIN file (no decompression cost) when both exist. Otherwise the same
    # instance is measured twice (and the .xz twin used to spuriously UNKNOWN).
    def _stem(p):
        return p[:-len(ext)] if (ext := next((e for e in (".xz", ".bz2", ".gz") if p.endswith(e)), "")) else p
    best = {}
    for f in files:
        k = _stem(f)
        if k not in best or f == k:  # first seen, or the uncompressed twin (f == stem)
            best[k] = f
    files = sorted(best.values())
    if args.limit: files = files[:args.limit]
    if not files:
        ap.error("no existing PB instances were selected")
    nbcore_desc = env["NBCORE"]
    memlimit_desc = env["MEMLIMIT"]
    print(f"instances: {len(files)} solvers: {list(solvers)} timeout: {args.timeout}s "
          f"NBCORE: {nbcore_desc} MEMLIMIT(env): {memlimit_desc} "
          f"rss-watchdog: {memlimit_mb} MiB/child", flush=True)

    jobs = [(n, p, f) for f in files for n, p in solvers.items()]
    results = []; done = 0
    with cf.ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = [ex.submit(run_one, n, p, f, args.timeout, env=env,
                          memlimit_mb=memlimit_mb,
                          resource_envelope=resource_envelope)
                for (n, p, f) in jobs]
        for fut in cf.as_completed(futs):
            results.append(fut.result()); done += 1
            if done % 20 == 0 or done == len(jobs): print(f"  {done}/{len(jobs)}", flush=True)

    by = {}
    for r in results: by.setdefault(r["file"], {})[r["solver"]] = r
    summary = {}
    for n in solvers:
        rs = [r for r in results if r["solver"] == n]
        summary[n] = {"solved": sum(1 for r in rs if solved(r["status"])),
                      "sat": sum(1 for r in rs if r["status"]=="sat"),
                      "unsat": sum(1 for r in rs if r["status"]=="unsat"),
                      "optimum": sum(1 for r in rs if r["status"]=="optimum"),
                      "timeout": sum(1 for r in rs if r["status"] in ("timeout","unknown")),
                      "memout": sum(1 for r in rs if r["status"]=="memout"),
                      "error": sum(1 for r in rs if r["status"]=="error")}
    # Soundness: disagreement on decision (sat vs unsat) or on a PROVEN optimum value.
    disagree = []
    for f, d in by.items():
        defs = {n: r for n, r in d.items() if solved(r["status"])}
        decisions = set()
        for n, r in defs.items():
            if r["status"] == "unsat": decisions.add(("dec", "unsat"))
            elif r["status"] in ("sat", "optimum"): decisions.add(("dec", "feasible"))
        if len(decisions) > 1:
            disagree.append({"file": f, "kind": "sat-vs-unsat", "verdicts": {n: d[n]["status"] for n in d}})
        opt_vals = {r["obj"] for n, r in defs.items() if r["status"] == "optimum" and r["obj"] is not None}
        if len(opt_vals) > 1:
            disagree.append({"file": f, "kind": "optimum-mismatch",
                             "objs": {n: defs[n]["obj"] for n in defs if defs[n]["status"]=="optimum"}})

    # Persist the measurement envelope: results taken under different budgets
    # are not comparable, so the record must carry what this run enforced.
    out = {"timeout_s": args.timeout, "n": len(files), "summary": summary,
           "resource_plan": resource_envelope,
           "disagreements": disagree, "results": results}
    with open(args.out, "w") as output_file:
        json.dump(out, output_file, indent=2)
        output_file.write("\n")
    print("\n=== SUMMARY ===", flush=True)
    for n, s in summary.items():
        print(f"{n:14s} solved={s['solved']:3d} (sat={s['sat']} unsat={s['unsat']} opt={s['optimum']}) "
              f"timeout={s['timeout']} memout={s['memout']} err={s['error']}", flush=True)
    if disagree:
        print(f"\n*** {len(disagree)} DISAGREEMENTS ***", flush=True)
        for d in disagree: print("  ", d, flush=True)
    else:
        print("\nno disagreements (decision + proven-optimum cross-check)", flush=True)
    print(f"wrote {args.out}", flush=True)

if __name__ == "__main__":
    main()
