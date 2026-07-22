#!/usr/bin/env python3
# ay-script: sat-sweep
"""Lightweight SAT sweep harness for local iteration benchmarking.

Runs one or more solvers over a directory of DIMACS CNFs at a fixed timeout,
records per-instance verdict + wall time, cross-checks solvers against each
other for soundness disagreements (SAT vs UNSAT = critical wrong answer), and
reports solved-count + PAR-2 per solver.

Not a competition harness — a fast, reproducible signal for before/after deltas.

Usage:
  sweep.py --dir DIR --timeout 60 --workers 8 \
      --solver ay=./target/release/ay [--solver kissat=/tmp/kissat/build/kissat] \
      --out results.json
"""
import argparse, concurrent.futures as cf, json, os, signal, subprocess, sys, time, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _oom_guard import plan_solver_resources, rss_watchdog, warn_concurrent_build

def run_one(solver_name, cmd_template, cnf, timeout_s, mem_mb, nbcore=1):
    """Run one solver on one instance. Returns dict."""
    if solver_name.startswith("ay"):
        cmd = [cmd_template, "--no-proof", "-t", str(int(timeout_s * 1000)),
               "--memory", str(mem_mb), cnf]
    elif solver_name.startswith("kissat"):
        cmd = [cmd_template, "-q", f"--time={int(timeout_s)}", cnf]
    else:
        cmd = [cmd_template, cnf]
    start = time.monotonic()
    verdict = "unknown"
    killed = False
    # External wall-clock guard = solver timeout + grace; SIGKILL the group.
    hard = timeout_s + 20
    try:
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                             start_new_session=True, text=True,
                             env=dict(os.environ, NBCORE=str(max(1, nbcore))))
        guard = rss_watchdog(
            p, mem_mb, label=f"sweep.py[{solver_name}]", grace_mb=0
        )
        try:
            out, _ = p.communicate(timeout=hard)
        except subprocess.TimeoutExpired:
            killed = True
            try:
                os.killpg(os.getpgid(p.pid), signal.SIGKILL)
            except ProcessLookupError:
                pass
            out, _ = p.communicate()
        finally:
            guard.stop()
        rc = p.returncode
    except Exception as e:
        return {"solver": solver_name, "cnf": os.path.basename(cnf),
                "verdict": "error", "time": 0.0, "rc": None, "err": str(e)}
    elapsed = time.monotonic() - start
    # Parse 's' line first; fall back to exit code 10/20.
    for line in (out or "").splitlines():
        ls = line.strip()
        if ls == "s SATISFIABLE" or ls.endswith(" SATISFIABLE"):
            verdict = "sat"; break
        if ls == "s UNSATISFIABLE" or ls.endswith(" UNSATISFIABLE"):
            verdict = "unsat"; break
    if verdict == "unknown" and not killed:
        if rc == 10: verdict = "sat"
        elif rc == 20: verdict = "unsat"
        elif rc == 124: verdict = "timeout"  # AY internal -t timeout exit code
    if guard.breached:
        verdict = "memout"
    elif killed:
        verdict = "timeout"
    return {"solver": solver_name, "cnf": os.path.basename(cnf),
            "verdict": verdict, "time": round(elapsed, 2), "rc": rc}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir")
    ap.add_argument("--list", help="file with one CNF path per line")
    ap.add_argument("--timeout", type=float, default=60.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--mem-mb", type=int, default=4000)
    ap.add_argument("--solver", action="append", default=[], help="name=path")
    ap.add_argument("--out", default="sweep_results.json")
    ap.add_argument("--limit", type=int, default=0)
    args = ap.parse_args()
    if args.mem_mb <= 0:
        ap.error("--mem-mb must be positive so every solver has an enforced envelope")

    solvers = {}
    for s in args.solver:
        name, path = s.split("=", 1)
        solvers[name] = path
    if not solvers:
        solvers["ay"] = "./target/release/ay"

    cnfs = []
    if args.dir:
        cnfs += sorted(glob.glob(os.path.join(args.dir, "*.cnf")))
    if args.list:
        with open(args.list) as f:
            for ln in f:
                ln = ln.strip()
                if ln and not ln.startswith("#"):
                    cnfs.append(ln.split()[0])
    cnfs = [c for c in cnfs if os.path.exists(c)]
    if args.limit:
        cnfs = cnfs[:args.limit]
    # OOM guard: plan aggregate concurrency through the repository admission
    # policy, then enforce the requested per-child budget on EVERY solver.
    # `--memory` is the graceful AY path; rss_watchdog is the hard backstop for
    # Kissat and arbitrary external solvers that have no memory knob.
    warn_concurrent_build()
    requested_workers = args.workers
    plan = plan_solver_resources(args.workers, mem_floor_mb=args.mem_mb,
                                 label="sweep.py")
    args.workers = plan.jobs
    enforced_mem_mb = args.mem_mb
    print(f"instances: {len(cnfs)}  solvers: {list(solvers)}  "
          f"timeout: {args.timeout}s  workers: {args.workers}  "
          f"memory: {enforced_mem_mb}MiB/child NBCORE={plan.nbcore} "
          f"enforcement=rss_watchdog", flush=True)

    jobs = [(name, path, cnf) for cnf in cnfs for name, path in solvers.items()]
    results = []
    done = 0
    with cf.ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = {ex.submit(run_one, n, p, c, args.timeout, enforced_mem_mb,
                          plan.nbcore): (n, c)
                for (n, p, c) in jobs}
        for fut in cf.as_completed(futs):
            r = fut.result()
            results.append(r)
            done += 1
            if done % 10 == 0 or done == len(jobs):
                print(f"  {done}/{len(jobs)} done", flush=True)

    # Aggregate per solver + cross-check soundness.
    by_inst = {}
    for r in results:
        by_inst.setdefault(r["cnf"], {})[r["solver"]] = r
    summary = {}
    for name in solvers:
        rs = [r for r in results if r["solver"] == name]
        solved = [r for r in rs if r["verdict"] in ("sat", "unsat")]
        par2 = sum(r["time"] if r["verdict"] in ("sat", "unsat") else 2 * args.timeout
                   for r in rs)
        summary[name] = {
            "solved": len(solved),
            "sat": sum(1 for r in rs if r["verdict"] == "sat"),
            "unsat": sum(1 for r in rs if r["verdict"] == "unsat"),
            "timeout": sum(1 for r in rs if r["verdict"] == "timeout"),
            "memout": sum(1 for r in rs if r["verdict"] == "memout"),
            "unknown": sum(1 for r in rs if r["verdict"] == "unknown"),
            "error": sum(1 for r in rs if r["verdict"] == "error"),
            "par2": round(par2, 1),
            "total_time": round(sum(r["time"] for r in rs), 1),
        }
    # Soundness disagreements: two solvers giving definite, opposite answers.
    disagreements = []
    for cnf, d in by_inst.items():
        verdicts = {n: v["verdict"] for n, v in d.items()}
        defs = {n: vv for n, vv in verdicts.items() if vv in ("sat", "unsat")}
        if len(set(defs.values())) > 1:
            disagreements.append({"cnf": cnf, "verdicts": verdicts})

    out = {"timeout_s": args.timeout, "workers": args.workers,
           "resource_plan": {
               "requested_jobs": requested_workers,
               "jobs": args.workers,
               "memlimit_mb_per_child": enforced_mem_mb,
               "nbcore_per_child": plan.nbcore,
               "headroom_mb": plan.headroom_mb,
               "enforcement": "rss_watchdog(all solvers) + ay --memory",
           },
           "n_instances": len(cnfs), "summary": summary,
           "disagreements": disagreements, "results": results}
    with open(args.out, "w") as f:
        json.dump(out, f, indent=2)

    print("\n=== SUMMARY ===", flush=True)
    for name, s in summary.items():
        print(f"{name:10s} solved={s['solved']:3d} (sat={s['sat']} unsat={s['unsat']}) "
              f"timeout={s['timeout']} memout={s['memout']} "
              f"unknown={s['unknown']} err={s['error']} "
              f"PAR2={s['par2']:.0f}", flush=True)
    if disagreements:
        print(f"\n*** {len(disagreements)} SOUNDNESS DISAGREEMENTS ***", flush=True)
        for d in disagreements:
            print(f"  {d['cnf']}: {d['verdicts']}", flush=True)
    else:
        print("\nno soundness disagreements", flush=True)
    print(f"\nwrote {args.out}", flush=True)

if __name__ == "__main__":
    main()
