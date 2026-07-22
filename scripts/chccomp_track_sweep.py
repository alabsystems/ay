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
import argparse, json, os, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import chccomp_harness as H  # noqa: E402
from _oom_guard import plan_solver_resources, warn_concurrent_build  # noqa: E402

REPO = Path(__file__).resolve().parent.parent


def run_one(task, timeout_s, ay_bin, memlimit_mb=0):
    argv = [ay_bin, "--chc", "--competition", "--timeout", str(timeout_s * 1000)]
    if memlimit_mb:
        argv += ["--memory", str(memlimit_mb)]
    argv.append(task.smt2)
    t0 = time.time()
    status = "error"
    try:
        popen_kwargs = {}
        if os.name == "nt":
            popen_kwargs["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP
        else:
            popen_kwargs["start_new_session"] = True
        p = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True, encoding="utf-8", errors="replace", **popen_kwargs)
        try:
            out, _ = p.communicate(timeout=timeout_s + 15)
            status = H.parse_status(out)
            if status == "no-status":
                status = "unknown"
        except subprocess.TimeoutExpired:
            if os.name == "nt":
                subprocess.run(["taskkill", "/F", "/T", "/PID", str(p.pid)], capture_output=True)
            else:
                import signal as sig
                os.killpg(os.getpgid(p.pid), sig.SIGKILL)
            p.communicate()
            status = "timeout"
    except OSError:
        pass
    correct = None
    if status in ("sat", "unsat") and task.verdict is not None:
        correct = status == task.verdict
    # memlimit_mb (0 = solver default) is recorded per record so sweep files
    # taken under different --memory envelopes are never silently compared.
    return {"inst": task.rel_id, "status": status, "correct": correct,
            "verdict": task.verdict, "wall": round(time.time() - t0, 1),
            "memlimit_mb": memlimit_mb}


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
    plan = plan_solver_resources(args.jobs, headroom_mb=args.mem_headroom_mb,
                                 label="chccomp_track_sweep.py")
    args.jobs = plan.jobs
    # Always print the plan (mirrors wind_tunnel.py): the per-child --memory
    # envelope decides which memory-hungry instances survive, so sweeps run
    # under different envelopes are not comparable and the envelope must be
    # visible in the log as well as in each JSONL record.
    print(f"track sweep: resource plan: jobs={plan.jobs}, "
          f"--memory={plan.memlimit_mb or 'default'} MiB/child, "
          f"headroom={plan.headroom_mb} MiB", flush=True)

    for track in args.tracks.split(","):
        H._CURRENT_TRACK = track
        tasks = H.load_track(args.year, track)
        gt_tasks = [t for t in tasks if t.verdict is not None]
        sample = H.stratified_sample(gt_tasks, args.sample)
        outdir = REPO / f"evals/results/chccomp-harness/{args.year}/{track}/{args.tag}"
        outdir.mkdir(parents=True, exist_ok=True)
        outp = outdir / "ay_sample.jsonl"
        recs = []
        t0 = time.time()
        with outp.open("w") as fh, ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futs = [pool.submit(run_one, t, args.timeout, args.ay_bin,
                                plan.memlimit_mb) for t in sample]
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
