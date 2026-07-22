#!/usr/bin/env python3
# ay-script: sat-compare
"""Head-to-head SAT solver comparison harness (AY vs reference, e.g. Kissat).

For each CNF: runs each solver with a wall-clock timeout, parses the DIMACS
verdict line, records time, cross-checks verdicts for soundness disagreements,
and computes solved counts + PAR-2.

Usage:
  sat_compare.py <cnf_dir_or_listfile> <timeout_sec> <out_json> [n_jobs]
"""
import subprocess, sys, os, time, json, glob, concurrent.futures as cf, math, signal, tempfile

# scripts/ dir (this file lives in scripts/sat_bench/)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from _oom_guard import plan_solver_resources, run_captured, warn_concurrent_build  # noqa: E402

_REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
AY = os.environ.get("AY_BIN", os.path.join(_REPO, "target/release/ay"))
KISSAT = os.environ.get("KISSAT_BIN", "/tmp/kissat/build/kissat")

# Per-child execution envelope, populated from the shared planner in main().
AY_MEMLIMIT_MB = 0
CHILD_ENV = None

def parse_verdict(stdout):
    lines = stdout.splitlines() if isinstance(stdout, str) else stdout
    for line in lines:
        if isinstance(line, bytes):
            line = line.decode("utf-8", errors="replace")
        if line.startswith("s "):
            if "UNSATISFIABLE" in line:
                return "UNSAT"
            if "SATISFIABLE" in line:
                return "SAT"
            if "UNKNOWN" in line:
                return "UNKNOWN"
    return "UNKNOWN"

def run_solver(cmd, timeout, label):
    """Run a solver under the exact process-group RSS envelope."""
    try:
        captured = run_captured(
            cmd, AY_MEMLIMIT_MB, timeout, label=label, env=CHILD_ENV,
        )
    except Exception as exc:
        return {"verdict": "ERROR", "time": 0.0, "rc": None,
                "err": str(exc)}
    if captured.memout:
        verdict = "MEMOUT"
    elif captured.timed_out:
        verdict = "TIMEOUT"
    elif captured.cancelled or captured.output_truncated:
        verdict = "ERROR"
    else:
        verdict = parse_verdict(captured.stdout)
    return {"verdict": verdict, "time": captured.wall_sec,
            "rc": captured.returncode}


def run_ay(cnf, timeout):
    cmd = [AY, "--no-proof", "-t", str(int(timeout * 1000))]
    cmd += ["--memory", str(AY_MEMLIMIT_MB)]
    cmd.append(cnf)
    return run_solver(cmd, timeout, "sat_compare.py[ay]")

def run_kissat(cnf, timeout):
    cmd = [KISSAT, "-q", f"--time={int(timeout)}", cnf]
    # Kissat has no trusted native memory knob, so the same external guard that
    # backstops AY is its primary enforcement. This removes the old asymmetric
    # comparison where only AY had a cap.
    return run_solver(cmd, timeout, "sat_compare.py[kissat]")

def collect(arg):
    if os.path.isdir(arg):
        return sorted(glob.glob(os.path.join(arg, "*.cnf")))
    files = []
    missing = []
    with open(arg) as list_file:
        for line in list_file:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            # accept "path" or "hash\tfn\tpath"
            path = line.split("\t")[-1]
            if os.path.exists(path):
                files.append(path)
            else:
                missing.append(path)
    if missing:
        preview = ", ".join(missing[:3])
        suffix = "" if len(missing) <= 3 else f" (and {len(missing) - 3} more)"
        raise FileNotFoundError(f"list references missing CNF files: {preview}{suffix}")
    return files

def one(cnf, timeout):
    ay = run_ay(cnf, timeout)
    ki = run_kissat(cnf, timeout)
    disagree = (ay["verdict"] in ("SAT", "UNSAT") and ki["verdict"] in ("SAT", "UNSAT")
                and ay["verdict"] != ki["verdict"])
    return {"cnf": os.path.basename(cnf), "path": cnf, "ay": ay, "kissat": ki, "disagree": disagree}

def par2(results, key, timeout):
    total = 0.0
    solved = 0
    for r in results:
        v = r[key]["verdict"]
        if v in ("SAT", "UNSAT"):
            total += r[key]["time"]
            solved += 1
        else:
            total += 2 * timeout
    return solved, total


def write_report(path, payload):
    with open(path, "w") as output:
        json.dump(payload, output, indent=1)
        output.write("\n")

def main():
    global AY_MEMLIMIT_MB, CHILD_ENV
    if len(sys.argv) < 4:
        sys.exit(__doc__)
    arg = sys.argv[1]
    timeout = float(sys.argv[2])
    out = sys.argv[3]
    jobs = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    if jobs <= 0:
        sys.exit("n_jobs must be positive")
    if not math.isfinite(timeout) or timeout <= 0:
        sys.exit("timeout_sec must be finite and positive")
    files = collect(arg)
    if not files:
        sys.exit("no CNF instances were selected")

    # OOM guard (scripts/_oom_guard.py; 2026-06-19 / 2026-07-11 watchdog
    # panics): each job runs ay then kissat sequentially, so concurrent
    # solvers = jobs. Cap jobs and give both children one authoritative
    # process-group envelope (AY additionally receives its native --memory).
    warn_concurrent_build()
    requested_jobs = jobs
    plan = plan_solver_resources(jobs, label="sat_compare.py")
    jobs = plan.jobs
    AY_MEMLIMIT_MB = plan.memlimit_mb
    CHILD_ENV = dict(os.environ)
    CHILD_ENV["MEMLIMIT"] = str(plan.memlimit_mb)
    CHILD_ENV["NBCORE"] = str(plan.nbcore)
    resource_plan = {
        "requested_jobs": requested_jobs,
        "jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "planner": "scripts/_oom_guard.py",
        "enforcement": "rss_watchdog(grace=0) for AY and Kissat; AY --memory",
    }

    print(f"instances: {len(files)}  timeout: {timeout}s  jobs: {jobs}  "
          f"memory: {AY_MEMLIMIT_MB} MiB/child  NBCORE: {plan.nbcore} "
          f"(same RSS watchdog for AY and Kissat)")
    results = []
    # NOTE: jobs>1 makes timings noisy (resource contention). Default sequential
    # for faithful per-instance timing; use jobs>1 only for quick coverage scans.
    if jobs == 1:
        for i, f in enumerate(files):
            r = one(f, timeout)
            results.append(r)
            flag = "  ***DISAGREE***" if r["disagree"] else ""
            print(f"[{i+1}/{len(files)}] {r['cnf'][:50]:50} "
                  f"AY={r['ay']['verdict']:8}{r['ay']['time']:7.1f}s  "
                  f"KI={r['kissat']['verdict']:8}{r['kissat']['time']:7.1f}s{flag}", flush=True)
            write_report(out, {"timeout": timeout,
                               "resource_plan": resource_plan,
                               "results": results})
    else:
        with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
            futs = {ex.submit(one, f, timeout): f for f in files}
            for i, fut in enumerate(cf.as_completed(futs)):
                r = fut.result()
                results.append(r)
                flag = "  ***DISAGREE***" if r["disagree"] else ""
                print(f"[{i+1}/{len(files)}] {r['cnf'][:50]:50} "
                      f"AY={r['ay']['verdict']:8} KI={r['kissat']['verdict']:8}{flag}", flush=True)
                write_report(out, {"timeout": timeout,
                                   "resource_plan": resource_plan,
                                   "results": results})

    ay_s, ay_p2 = par2(results, "ay", timeout)
    ki_s, ki_p2 = par2(results, "kissat", timeout)
    disagreements = [r["cnf"] for r in results if r["disagree"]]
    # gap: kissat solves, AY does not
    gap = [r["cnf"] for r in results
           if r["kissat"]["verdict"] in ("SAT", "UNSAT") and r["ay"]["verdict"] not in ("SAT", "UNSAT")]
    ay_only = [r["cnf"] for r in results
               if r["ay"]["verdict"] in ("SAT", "UNSAT") and r["kissat"]["verdict"] not in ("SAT", "UNSAT")]
    summary = {
        "n": len(results), "timeout": timeout,
        "jobs": jobs, "memory_mb_per_solver": AY_MEMLIMIT_MB,
        "nbcore_per_solver": plan.nbcore,
        "ay_solved": ay_s, "ay_par2": ay_p2,
        "kissat_solved": ki_s, "kissat_par2": ki_p2,
        "disagreements": disagreements,
        "gap_kissat_solves_ay_doesnt": gap,
        "ay_only_solves": ay_only,
    }
    write_report(out, {"timeout": timeout, "resource_plan": resource_plan,
                       "summary": summary, "results": results})
    print("\n===== SUMMARY =====")
    print(f"AY     solved {ay_s}/{len(results)}  PAR2={ay_p2:.0f}")
    print(f"Kissat solved {ki_s}/{len(results)}  PAR2={ki_p2:.0f}")
    print(f"DISAGREEMENTS (soundness!): {len(disagreements)} {disagreements}")
    print(f"GAP (Kissat solves, AY doesn't): {len(gap)}")
    print(f"AY-only solves: {len(ay_only)} {ay_only}")

if __name__ == "__main__":
    main()
