#!/usr/bin/env python3
# ay-script: rewrite-oracle-check
"""Regression oracle for the hash-consing / fast-core rewrite.

Runs a given AY binary on the golden verdict set and reports:
  - confirmed: binary reproduces the golden verdict
  - regressed: golden was sat/unsat, binary now unknown/timeout (completeness loss)
  - FLIP:      golden sat<->unsat disagreement (SOUNDNESS BUG — must be zero)

Usage:
  python3 scripts/rewrite_oracle_check.py <ay_binary> [--timeout 30] [--jobs 6] [--sample N]
Exit code 2 if any FLIP (soundness) is detected.
"""
import json, os, sys, subprocess, signal, random, argparse, concurrent.futures as cf, tempfile, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _oom_guard import plan_solver_resources, run_captured, warn_concurrent_build  # noqa: E402

ORACLE = "evals/results/rewrite-oracle/golden_verdicts.jsonl"
BENCH_ROOT = "benchmarks/chc"


def resolve(inst):
    stem = os.path.basename(inst)
    for ext in (".yml", ".smt2"):
        if stem.endswith(ext):
            stem = stem[: -len(ext)]
    # fast path: try the literal path with .smt2 under each suite root
    cands = []
    rel = inst.lstrip("./")
    if rel.endswith(".yml"):
        rel = rel[:-4] + ".smt2"
    for suite in ("chc-comp25-benchmarks", "chc-comp26-benchmarks"):
        cands.append(os.path.join(BENCH_ROOT, suite, rel))
    for c in cands:
        if os.path.exists(c):
            return c
    # fallback: find by basename
    for dirpath, _, files in os.walk(BENCH_ROOT):
        if "worktree" in dirpath:
            continue
        f = stem + ".smt2"
        if f in files:
            return os.path.join(dirpath, f)
    return None


def run_one(binary, smt2, timeout, memlimit_mb, env):
    argv = [binary, "solve"]
    # Per-child envelope: the standalone default is 85% of RAM per process,
    # sibling-blind across jobs (scripts/_oom_guard.py).
    argv += ["--memory", str(memlimit_mb)]
    argv.append(smt2)
    try:
        captured = run_captured(
            argv, memlimit_mb, timeout, label="rewrite_oracle_check.py", env=env,
        )
    except Exception as e:
        return {"status": "error", "wall_s": 0.0, "exit_code": None,
                "error": str(e)}
    if captured.memout:
        status = "memout"
    elif captured.timed_out:
        status = "timeout"
    elif captured.cancelled or captured.output_truncated:
        status = "error"
    else:
        status = "none"
        for raw_line in captured.stdout.splitlines():
            value = raw_line.strip().lower()
            if value in ("sat", "unsat", "unknown"):
                status = value
                break
    return {"status": status, "wall_s": captured.wall_sec,
            "exit_code": captured.returncode}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("binary")
    ap.add_argument("--timeout", type=int, default=30)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--sample", type=int, default=0, help="0 = all")
    ap.add_argument("--out", default="rewrite_oracle_check.json",
                    help="persist verdicts and the exact execution envelope")
    args = ap.parse_args()

    if args.jobs <= 0:
        ap.error("--jobs must be positive")
    if args.timeout <= 0:
        ap.error("--timeout must be positive")
    if args.sample < 0:
        ap.error("--sample cannot be negative")

    # Admission happens before any work is assigned. The resulting plan is
    # authoritative even if the parent environment already set these names.
    warn_concurrent_build()
    requested_jobs = args.jobs
    plan = plan_solver_resources(args.jobs, label="rewrite_oracle_check.py")
    args.jobs = plan.jobs
    child_env = dict(os.environ)
    child_env["MEMLIMIT"] = str(plan.memlimit_mb)
    child_env["NBCORE"] = str(plan.nbcore)
    resource_plan = {
        "requested_jobs": requested_jobs,
        "jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "planner": "scripts/_oom_guard.py",
        "enforcement": "ay --memory + rss_watchdog(grace=0); NBCORE env",
    }

    with open(ORACLE) as oracle_file:
        golden = [json.loads(line) for line in oracle_file if line.strip()]
    if args.sample:
        random.seed(1234)
        golden = random.sample(golden, min(args.sample, len(golden)))

    items = []
    missing = 0
    for g in golden:
        f = g.get("smt2") or resolve(g["instance"])
        if f and os.path.exists(f):
            items.append((f, f, g["verdict"]))
        else:
            missing += 1

    confirmed = regressed = 0
    flips = []
    records = []
    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(run_one, args.binary, f, args.timeout,
                          plan.memlimit_mb, child_env): (inst, f, exp)
                for inst, f, exp in items}
        for fut in cf.as_completed(futs):
            inst, path, exp = futs[fut]
            result = fut.result()
            got = result["status"]
            records.append({"instance": inst, "path": path, "expected": exp,
                            **result})
            if got == exp:
                confirmed += 1
            elif got in ("sat", "unsat") and exp in ("sat", "unsat") and got != exp:
                flips.append((inst, exp, got))
            else:
                regressed += 1

    print(f"binary={args.binary}")
    print(f"oracle={len(golden)} resolved={len(items)} missing={missing} "
          f"timeout/jobs={args.timeout}s/{args.jobs} "
          f"--memory={plan.memlimit_mb} MiB/child NBCORE={plan.nbcore}")
    print(f"  confirmed={confirmed}  regressed(def->unknown)={regressed}  FLIPS(soundness)={len(flips)}")
    for inst, exp, got in flips:
        print(f"  *** FLIP {os.path.basename(inst)}: golden={exp} got={got} ***")
    payload = {
        "binary": args.binary,
        "oracle": ORACLE,
        "timeout_s": args.timeout,
        "resource_plan": resource_plan,
        "counts": {"oracle": len(golden), "resolved": len(items),
                   "missing": missing, "confirmed": confirmed,
                   "regressed": regressed, "flips": len(flips)},
        "results": sorted(records, key=lambda record: record["instance"]),
    }
    out_dir = os.path.dirname(os.path.abspath(args.out))
    os.makedirs(out_dir, exist_ok=True)
    with open(args.out, "w") as fh:
        json.dump(payload, fh, indent=2)
        fh.write("\n")
    print(f"wrote {args.out}")
    if flips:
        sys.exit(2)


if __name__ == "__main__":
    main()
