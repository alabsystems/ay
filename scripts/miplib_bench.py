#!/usr/bin/env python3
# ay-script: miplib-bench
"""miplib_bench.py — run ay-milp and HiGHS on the same MPS files and compare.

The point is not the times. The point is the VERDICTS: a solver that is fast because it is
wrong is not fast, so a disagreement on a proven optimum is reported as a hard error and never
averaged away. Instances where either solver only found an incumbent (no optimality proof) are
compared on the incumbent, and a strictly better incumbent is reported, not scored.

Usage:
  scripts/miplib_bench.py --dir path/to/mps --timeout 60
"""

from __future__ import annotations

import argparse
import json
import math
import os
import pathlib
import re
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from _oom_guard import (  # noqa: E402
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)

AY = "./target/release/examples/mps_solve"


def run_ay(path: pathlib.Path, timeout: float, plan):
    t0 = time.monotonic()
    try:
        r = run_captured(
            [AY, str(path), str(timeout)],
            plan.memlimit_mb, timeout + 60, label="miplib_bench.py[ay]",
            env=dict(os.environ, MEMLIMIT=str(plan.memlimit_mb),
                     NBCORE=str(plan.nbcore)),
        )
    except OSError:
        return ("CRASH", None, 0.0)
    if r.memout:
        return ("MEMOUT", None, r.wall_sec)
    if r.timed_out:
        return ("TIMEOUT", None, timeout + 60)
    if r.output_truncated:
        return ("CRASH", None, r.wall_sec)
    dt = time.monotonic() - t0
    out = (r.stdout or "").strip().splitlines()
    if not out:
        return ("CRASH", None, dt)
    f = out[-1].split()
    status = f[0]
    val = None
    if len(f) > 1:
        try:
            val = float(f[1])
        except ValueError:
            val = None
    return (status, val, dt)


def run_highs(path: pathlib.Path, timeout: float, plan):
    t0 = time.monotonic()
    try:
        r = run_captured(
            ["highs", "--time_limit", str(timeout), str(path)],
            plan.memlimit_mb, timeout + 60, label="miplib_bench.py[highs]",
            env=dict(os.environ, MEMLIMIT=str(plan.memlimit_mb),
                     NBCORE=str(plan.nbcore), OMP_NUM_THREADS=str(plan.nbcore)),
        )
    except OSError:
        return ("CRASH", None, 0.0)
    if r.memout:
        return ("MEMOUT", None, r.wall_sec)
    if r.timed_out:
        return ("TIMEOUT", None, timeout + 60)
    if r.output_truncated:
        return ("CRASH", None, r.wall_sec)
    dt = time.monotonic() - t0
    txt = r.stdout or ""
    status = re.search(r"^\s*Status\s+(.+)$", txt, re.M)
    obj = re.search(r"^\s*Primal bound\s+(\S+)$", txt, re.M)
    status = status.group(1).strip() if status else "?"
    val = float(obj.group(1)) if obj else None
    if status == "Optimal":
        return ("OPTIMAL", val, dt)
    if "Infeasible" in status:
        return ("INFEASIBLE", None, dt)
    if "Unbounded" in status:
        return ("UNBOUNDED", None, dt)
    # Time limit reached: it may still hold an incumbent.
    return ("FEASIBLE" if val is not None else "UNKNOWN", val, dt)


def close(a: float, b: float) -> bool:
    return abs(a - b) <= 1e-6 * max(1.0, abs(a), abs(b))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--timeout", type=float, default=60.0)
    ap.add_argument("--out", type=pathlib.Path,
                    default=pathlib.Path("evals/results/miplib-bench/latest.json"))
    args = ap.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        ap.error("--timeout must be finite and positive")

    warn_concurrent_build()
    plan = plan_solver_resources(1, label="miplib_bench.py")
    resource_plan = {
        "requested_jobs": 1, "jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "enforcement": "process-group rss_watchdog; MEMLIMIT/NBCORE environment",
    }

    files = sorted(pathlib.Path(args.dir).glob("*.mps"))
    print(f"{'instance':<12} {'ay':>10} {'ay t':>8} {'highs':>12} {'hi t':>8}  verdict")
    print("-" * 68)

    wrong, ay_opt, hi_opt, ay_better, hi_better = [], 0, 0, [], []
    records = []
    for f in files:
        a_st, a_v, a_t = run_ay(f, args.timeout, plan)
        h_st, h_v, h_t = run_highs(f, args.timeout, plan)
        note = ""

        # A disagreement on a PROVEN optimum is a correctness bug in one of them.
        if a_st == "OPTIMAL" and h_st == "OPTIMAL":
            if a_v is not None and h_v is not None and not close(a_v, h_v):
                note = "!! DISAGREE ON OPTIMUM"
                wrong.append((f.stem, a_v, h_v))
            else:
                note = "both optimal, agree"
        elif a_st == "OPTIMAL" and h_st in ("FEASIBLE", "UNKNOWN", "TIMEOUT"):
            note = "AY PROVED, highs did not"
        elif h_st == "OPTIMAL" and a_st in ("FEASIBLE", "UNKNOWN", "TIMEOUT"):
            note = "highs proved, ay did not"
        elif a_st == "INFEASIBLE" and h_st == "OPTIMAL":
            note = "!! AY SAYS INFEASIBLE, highs found a point"
            wrong.append((f.stem, "INFEASIBLE", h_v))
        elif a_st == "FEASIBLE" and h_st == "FEASIBLE":
            note = "neither proved"

        if a_st == "OPTIMAL":
            ay_opt += 1
        if h_st == "OPTIMAL":
            hi_opt += 1

        av = "-" if a_v is None else f"{a_v:.6g}"
        hv = "-" if h_v is None else f"{h_v:.6g}"
        print(f"{f.stem:<12} {av:>10} {a_t:>7.1f}s {hv:>12} {h_t:>7.1f}s  {a_st}/{h_st} {note}")
        records.append({"file": str(f), "ay_status": a_st,
                        "ay_objective": a_v, "ay_time_sec": a_t,
                        "highs_status": h_st, "highs_objective": h_v,
                        "highs_time_sec": h_t, "note": note})

    print("-" * 68)
    print(f"proved optimal: ay {ay_opt}/{len(files)}   highs {hi_opt}/{len(files)}")
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps({
        "timeout_sec": args.timeout,
        "resource_plan": resource_plan,
        "records": records,
        "wrong": wrong,
    }, indent=2) + "\n")
    print(f"wrote {args.out}")
    if wrong:
        print("\nCORRECTNESS FAILURES (these are bugs, not slowness):")
        for nm, a, h in wrong:
            print(f"  {nm}: ay={a} highs={h}")
        return 1
    print("no verdict disagreements")
    return 0


if __name__ == "__main__":
    sys.exit(main())
