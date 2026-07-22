#!/usr/bin/env python3
# ay-script: chccomp-track-sweep
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Stratified-sample standings sweep across CHC-COMP tracks.

For each track, runs AY on a deterministic stratified sample (by family) at a
short budget, scores against the corpus expected_verdict, and projects the
full-track solve count. Fast reconnaissance to find which golds are reachable.

Usage:
  python scripts/chccomp_track_sweep.py --year 2025 --sample 120 --timeout 60 \
      --jobs 8 --tracks LIA-Lin,LIA,LRA-Lin,ADT-LIA,LIA-Lin-Arrays
"""
from __future__ import annotations
import argparse, json, os, sys, time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import chccomp_harness as H  # noqa: E402
from _oom_guard import (  # noqa: E402
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)

REPO = Path(__file__).resolve().parent.parent


def run_one(task, timeout_s, ay_bin, memlimit_mb=0, nbcore=1,
            resource_envelope=None):
    if memlimit_mb <= 0 or nbcore <= 0:
        raise ValueError("track sweep requires positive memory and core budgets")
    argv = [ay_bin, "--chc", "--competition", "--timeout", str(timeout_s * 1000)]
    if memlimit_mb:
        argv += ["--memory", str(memlimit_mb)]
    argv.append(task.smt2)
    child_env = dict(os.environ, NBCORE=str(max(1, nbcore)))
    if memlimit_mb:
        child_env["MEMLIMIT"] = str(memlimit_mb)
    t0 = time.monotonic()
    status = "error"
    exit_code = None
    memout = False
    timed_out = False
    output_truncated = False
    try:
        result = run_captured(
            argv,
            memlimit_mb,
            timeout_s=timeout_s + 15,
            label="chccomp_track_sweep.py",
            env=child_env,
        )
        exit_code = result.returncode
        memout = result.memout
        timed_out = result.timed_out
        output_truncated = result.output_truncated
        if memout:
            status = "memout"
        elif timed_out:
            status = "timeout"
        elif output_truncated:
            status = "error"
        else:
            status = H.parse_status(result.stdout)
            if status == "no-status":
                status = "unknown"
    except (OSError, RuntimeError, ValueError):
        status = "error"
    correct = None
    if status in ("sat", "unsat") and task.verdict is not None:
        correct = status == task.verdict
    # The exact positive envelope is recorded per row so sweeps taken under
    # different limits are never silently compared.
    return {"inst": task.rel_id, "status": status, "correct": correct,
            "verdict": task.verdict, "wall": round(time.monotonic() - t0, 1),
            "timeout_sec": timeout_s, "memlimit_mb": memlimit_mb,
            "nbcore": nbcore, "resource_envelope": resource_envelope,
            "exit_code": exit_code, "memout": memout,
            "timed_out": timed_out, "output_truncated": output_truncated}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--year", type=int, default=2025)
    ap.add_argument("--tracks", required=True)
    ap.add_argument("--sample", type=int, default=120)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--ay-bin", default=os.environ.get("AY_BIN", str(REPO / "target_lever/release/ay.exe")))
    ap.add_argument("--tag", default="sweep")
    ap.add_argument("--mem-headroom-mb", type=int, default=None,
                    help="RAM headroom (MiB) the resource planner reserves "
                         "(default: max(16 GiB, RAM/3); lower it to widen the "
                         "per-child --memory envelope)")
    args = ap.parse_args()

    # OOM guard (scripts/_oom_guard.py): N parallel ay children each default to
    # an 85%-of-RAM memory
    # limit, sibling-blind — cap jobs and pass each child an explicit --memory.
    warn_concurrent_build()
    requested_jobs = args.jobs
    plan = plan_solver_resources(requested_jobs, headroom_mb=args.mem_headroom_mb,
                                 label="chccomp_track_sweep.py")
    args.jobs = plan.jobs
    # Always print the plan (mirrors wind_tunnel.py): the per-child --memory
    # envelope decides which memory-hungry instances survive, so sweeps run
    # under different envelopes are not comparable and the envelope must be
    # visible in the log as well as in each JSONL record.
    print(f"track sweep: resource plan: jobs={plan.jobs}, "
          f"--memory={plan.memlimit_mb} MiB/child, NBCORE={plan.nbcore}, "
          f"headroom={plan.headroom_mb} MiB", flush=True)
    resource_envelope = {
        "requested_jobs": requested_jobs,
        "jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "enforcement": "exec-stopped + rss-watchdog-zero-grace; ay --memory; "
                       "MEMLIMIT/NBCORE environment; bounded 1MiB/stream capture",
    }

    for track in args.tracks.split(","):
        H._CURRENT_TRACK = track
        tasks = H.load_track(args.year, track)
        gt_tasks = [t for t in tasks if t.verdict is not None]
        sample = H.stratified_sample(gt_tasks, args.sample)
        outdir = REPO / f"evals/results/chccomp-harness/{args.year}/{track}/{args.tag}"
        outdir.mkdir(parents=True, exist_ok=True)
        outp = outdir / "ay_sample.jsonl"
        (outdir / "resource-envelope.json").write_text(
            json.dumps(resource_envelope, indent=2) + "\n"
        )
        recs = []
        t0 = time.time()
        with outp.open("w") as fh, ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futs = [pool.submit(run_one, t, args.timeout, args.ay_bin,
                                plan.memlimit_mb, plan.nbcore,
                                resource_envelope) for t in sample]
            done = 0
            for f in as_completed(futs):
                r = f.result()
                recs.append(r)
                fh.write(json.dumps(r) + "\n")
                fh.flush()
                done += 1
                if done % 25 == 0:
                    print(f"  [{track}] {done}/{len(sample)}", flush=True)
        correct = sum(1 for r in recs if r["correct"] is True)
        wrong = sum(1 for r in recs if r["correct"] is False)
        n = len(recs)
        full_gt = len(gt_tasks)
        proj = round(correct / n * full_gt) if n else 0
        print(f"=== {args.year}/{track}: sample {correct}/{n} correct ({wrong} wrong) "
              f"-> PROJECTED {proj}/{full_gt} gt "
              f"[{time.time()-t0:.0f}s]", flush=True)
        if wrong:
            print("   WRONG:", [r["inst"] for r in recs if r["correct"] is False][:10], flush=True)


if __name__ == "__main__":
    main()
