#!/usr/bin/env python3
# ay-script: mzn-run
"""Run AY over the MiniZinc Challenge 2025 corpus; emit a results vector for the
retroactive scorer (status/objective/time per global-instance index).

Drives `minizinc --solver org.ay.ay` on each model+data so solns2out maps the
objective (via --output-objective) and any solution checker runs.

Paths default to the repo's persistent (gitignored) corpus; override via env:
  MZN_CH_DATA   dir with <problem>/<model>.mzn + <instance>.{dzn,json}
  MZN_CH_RESULTS  reference results-2025.json (defines instance order)
  MINIZINC      minizinc binary (default: minizinc on PATH)

Usage: run.py <budget_ms> <free|fixed|par8> <workers> <out.json>
"""
import hashlib
import json
import os
import re
import shutil
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
sys.path.insert(0, os.path.join(REPO, "scripts"))
from _oom_guard import plan_solver_resources, run_captured, warn_concurrent_build  # noqa: E402

DATA = os.environ.get(
    "MZN_CH_DATA",
    f"{REPO}/benchmarks/minizinc/challenge-2025/mznc2025_probs",
)
RESULTS = os.environ.get("MZN_CH_RESULTS", f"{REPO}/benchmarks/minizinc/challenge-2025/results-2025.json")
MZN = os.environ.get("MINIZINC", "minizinc")
TIMEOUT_BIN = os.environ.get("GTIMEOUT", "gtimeout")
ENV = {**os.environ,
       "PATH": "/opt/homebrew/bin:" + os.environ.get("PATH", ""),
       "MZN_SOLVER_PATH": os.environ.get("MZN_SOLVER_PATH", REPO)}

SOL_RE = re.compile(r"^_objective\s*=\s*(-?\d+)\s*;")


def find_model(prob_dir):
    mzns = sorted(f for f in os.listdir(prob_dir) if f.endswith(".mzn"))
    return os.path.join(prob_dir, mzns[0]) if mzns else None


def executable_provenance(command):
    candidate = Path(command)
    if candidate.exists():
        resolved = candidate.resolve()
    else:
        found = shutil.which(command, path=ENV.get("PATH"))
        resolved = Path(found).resolve() if found else candidate
    try:
        stat = resolved.stat()
        digest = hashlib.sha256()
        with resolved.open("rb") as binary:
            for chunk in iter(lambda: binary.read(1024 * 1024), b""):
                digest.update(chunk)
        return {"path": str(resolved), "size": stat.st_size,
                "sha256": digest.hexdigest(),
                "runnable": resolved.is_file() and os.access(resolved, os.X_OK)}
    except OSError:
        return {"path": str(resolved), "size": None, "sha256": None,
                "runnable": False}


def parse_output(output):
    """Extract scoring fields from bounded solver output."""
    if hasattr(output, "read"):
        output.flush()
        output.seek(0)
        lines = (
            raw.decode("utf-8", errors="replace")
            if isinstance(raw, bytes) else raw
            for raw in output
        )
    else:
        lines = output.splitlines()
    sols = 0
    complete = unsat = err_marker = False
    best = None
    for line in lines:
        token = line.strip()
        if token == "----------":
            sols += 1
        elif token == "==========":
            complete = True
        elif token == "=====UNSATISFIABLE=====":
            unsat = True
        elif token in ("=====ERROR=====", "=====UNSATorUNBOUNDED====="):
            err_marker = True
        match = SOL_RE.match(line)
        if match:
            best = int(match.group(1))
    return sols, complete, unsat, err_marker, best


def run_instance(problem, model, data, budget_ms, search, memlimit_mb, nbcore,
                 parallelism):
    if memlimit_mb <= 0 or nbcore <= 0 or parallelism <= 0:
        raise ValueError("MiniZinc run requires positive memory and core budgets")
    flags = ["--output-objective", "-s", "-t", str(budget_ms)]
    # Globals library is passed EXPLICITLY via --globals-dir so the harness does
    # not depend on the ay.msc mznlib field (which a JSON linter has been known to
    # strip). MZN_CH_FORCE_STD points at std to measure the globals-OFF arm.
    force_std = os.environ.get("MZN_CH_FORCE_STD")
    gdir = force_std or os.environ.get("MZN_CH_GLOBALS_DIR", f"{REPO}/competition/minizinc/mznlib")
    flags += ["--globals-dir", gdir]
    if search == "free":
        flags += ["-f"]
    elif search == "par8":
        # `par8` requests up to eight workers, but the shared admission plan is
        # authoritative when concurrent instances divide the machine.
        flags += ["-p", str(parallelism)]
    # 'fixed' => respect the model's search annotation (no -f)
    cmd = [TIMEOUT_BIN, str(budget_ms // 1000 + 90), MZN, "--solver", "org.ay.ay",
           *flags, model, data]
    child_env = dict(ENV, MEMLIMIT=str(memlimit_mb), NBCORE=str(nbcore))
    try:
        captured = run_captured(
            cmd,
            memlimit_mb,
            budget_ms / 1000 + 120,
            label=f"mzn {problem}",
            env=child_env,
        )
    except Exception as exc:
        return {"problem": problem, "data": os.path.basename(data),
                "status": "ERR", "objective": None, "time_ms": 0,
                "n_sols": 0, "rc": None, "err": f"spawn: {exc}"[:200],
                "memout": False, "timed_out": False,
                "nbcore": nbcore, "parallelism": parallelism}
    sols, complete, unsat, err_marker, best = parse_output(captured.stdout)
    err = captured.stderr[-200:]
    rc = captured.returncode
    timed_out = captured.timed_out
    wall_ms = int(captured.wall_sec * 1000)
    if captured.memout:
        status = "MEMOUT"
        err = "MEM_BREACH" + (f": {err.strip()}" if err.strip() else "")
    elif timed_out or rc == 124:
        status = "TIMEOUT"
        if timed_out:
            err = "TIMEOUT_HARD" + (f": {err.strip()}" if err.strip() else "")
    elif captured.cancelled or captured.output_truncated:
        status = "ERR"
        err = "solver output truncated or capture cancelled"
    elif err_marker or (rc != 0 and not sols and not unsat):
        status = "ERR"
    elif unsat:
        status = "UNSAT"
    elif sols > 0 and complete:
        status = "SC"
    elif sols > 0:
        status = "S"
    else:
        status = "UNK"
    return {"problem": problem, "data": os.path.basename(data), "status": status,
            "objective": best, "time_ms": wall_ms, "n_sols": sols, "rc": rc,
            "err": (err or "").strip()[:200], "memout": captured.memout,
            "timed_out": timed_out or rc == 124, "nbcore": nbcore,
            "parallelism": parallelism}

def main():
    global MZN, TIMEOUT_BIN
    budget_ms = int(sys.argv[1]) if len(sys.argv) > 1 else 60000
    search = sys.argv[2] if len(sys.argv) > 2 else "free"
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    outpath = sys.argv[4] if len(sys.argv) > 4 else f"{REPO}/benchmarks/minizinc/challenge-2025/runs/ay-{search}-{budget_ms//1000}s.json"
    if budget_ms <= 0 or workers <= 0 or search not in {"free", "fixed", "par8"}:
        print("usage: run.py <positive-budget-ms> <free|fixed|par8> "
              "<positive-workers> <out.json>", file=sys.stderr)
        return 2
    if not os.path.isdir(DATA) or not os.path.isfile(RESULTS):
        print(f"mzn challenge: missing data/results input ({DATA}, {RESULTS})",
              file=sys.stderr)
        return 2
    minizinc_provenance = executable_provenance(MZN)
    timeout_provenance = executable_provenance(TIMEOUT_BIN)
    if not timeout_provenance["runnable"] and TIMEOUT_BIN == "gtimeout":
        timeout_provenance = executable_provenance("timeout")
    if not minizinc_provenance["runnable"] or not timeout_provenance["runnable"]:
        print("mzn challenge: minizinc or timeout executable unavailable",
              file=sys.stderr)
        return 2
    MZN = minizinc_provenance["path"]
    TIMEOUT_BIN = timeout_provenance["path"]
    os.makedirs(os.path.dirname(os.path.abspath(outpath)), exist_ok=True)

    # OOM guard (scripts/_oom_guard.py): cap the worker count so
    # `workers x per-child envelope` fits in RAM and enforce
    # the envelope per child with rss_watchdog (minizinc has no memory knob).
    try:
        warn_concurrent_build()
        requested_workers = workers
        plan = plan_solver_resources(requested_workers,
                                     label="mzn_challenge/run.py")
    except RuntimeError as exc:
        if "REFUSING" not in str(exc):
            print(f"mzn challenge: resource planning failed: {exc}",
                  file=sys.stderr)
        return 2
    if plan.memlimit_mb <= 0 or plan.nbcore <= 0:
        print("mzn challenge: resource planner returned no enforceable budget",
              file=sys.stderr)
        return 2
    if not hasattr(os, "killpg"):
        print("mzn challenge: exact process-group RSS enforcement requires POSIX",
              file=sys.stderr)
        return 2
    workers = plan.jobs
    memlimit_mb = plan.memlimit_mb
    nbcore = plan.nbcore
    parallelism = min(8, nbcore) if search == "par8" else 1
    resource_envelope = {
        "schema": "ay.benchmark-resource-envelope/v1",
        "requested_jobs": requested_workers,
        "jobs": workers,
        "memlimit_mb_per_child": memlimit_mb,
        "nbcore_per_child": nbcore,
        "parallelism_per_child": parallelism,
        "headroom_mb": plan.headroom_mb,
        "memory_enforcement": "process-group rss_watchdog",
        "rss_grace_mb": 0,
        "solver_env": {"MEMLIMIT": str(memlimit_mb), "NBCORE": str(nbcore)},
        "timeout_enforcement": "process-group SIGKILL + reap",
        "solver_budget_ms": budget_ms,
        "gtimeout_sec": budget_ms // 1000 + 90,
        "parent_wall_timeout_sec": budget_ms / 1000 + 120,
        "minizinc": minizinc_provenance,
        "timeout_wrapper": timeout_provenance,
        "results_file": str(Path(RESULTS).resolve()),
        "results_sha256": hashlib.sha256(Path(RESULTS).read_bytes()).hexdigest(),
    }
    print(f"[oom-guard] requested={requested_workers} workers={workers} "
          f"memlimit={memlimit_mb} MiB/child NBCORE={nbcore} "
          f"parallelism={parallelism} (exact rss watchdog), "
          f"headroom={plan.headroom_mb} MiB", flush=True)

    with open(RESULTS) as input_file:
        d = json.load(input_file)["results"]
    prob_order, inst_map, bench = d["problems"], d["instances"], d["benchmarks"]
    gi_problem = {}
    for p, idxs in enumerate(inst_map):
        for gi in idxs:
            gi_problem[gi] = prob_order[p]
    tasks = []
    for gi, datastem in enumerate(bench):
        problem = gi_problem[gi]
        pdir = os.path.join(DATA, problem)
        model = find_model(pdir) if os.path.isdir(pdir) else None
        cand = None
        for ext in (".dzn", ".json"):
            c = os.path.join(pdir, datastem + ext)
            if os.path.exists(c):
                cand = c; break
        tasks.append((gi, problem, model, cand))

    results = [None] * len(tasks)
    def work(t):
        gi, problem, model, data = t
        if not model or not data:
            return gi, {"problem": problem, "status": "ERR", "objective": None,
                        "time_ms": 0, "err": "missing model/data"}
        return gi, run_instance(problem, model, data, budget_ms, search,
                                memlimit_mb, nbcore, parallelism)
    done = 0
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for gi, r in ex.map(work, tasks):
            results[gi] = r; done += 1
            print(f"[{done}/{len(tasks)}] gi={gi} {r['problem']}/{r.get('data','?')} "
                  f"-> {r['status']} obj={r.get('objective')} {r.get('time_ms')}ms", flush=True)
    with open(outpath, "w") as output:
        json.dump({"budget_ms": budget_ms, "search": search, "jobs": workers,
                   "memlimit_mb": memlimit_mb,
                   "resource_envelope": resource_envelope,
                   "results": results}, output, indent=1)
        output.write("\n")
    print("WROTE", outpath)
    return 2 if any(result.get("status") == "ERR" for result in results) else 0

if __name__ == "__main__":
    sys.exit(main())
