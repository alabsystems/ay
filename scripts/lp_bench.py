#!/usr/bin/env python3
# ay-script: lp-bench
"""lp_bench.py — time LP/MILP solvers on a corpus and compare verdicts.

The G1 gate of the development design notes is a *measured*
claim ("geomean <= HiGHS", "the two spike benchmarks from 30s-timeout to <=
Z3's time"), and until now nothing in the tree could measure it: the spike
instances were not on disk and HiGHS was not installed. This is the harness the
gate is scored with.

Verdict disagreement is reported as a hard error, never averaged away — a solver
that is fast because it is wrong is not fast. Timeouts are recorded as the wall
limit and excluded from the geomean (which is taken over instances every solver
decided), so the geomean can never be flattered by the instances a solver failed.

Usage:
  scripts/lp_bench.py --corpus benchmarks/smtcomp/QF_LRA --solvers z3,ay \
      --timeout 30 --limit 50
  scripts/lp_bench.py --files a.smt2 b.smt2 --solvers z3,ay --timeout 30
"""

from __future__ import annotations

import argparse
import json
import math
import os
import pathlib
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from _oom_guard import (  # noqa: E402
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)

# How each solver is invoked, and how its verdict is read off stdout.
SOLVERS: dict[str, list[str]] = {
    "z3": ["z3"],
    "ay": ["target/release/ay"],
    "highs": ["highs"],
}

VERDICTS = ("unsat", "sat", "unknown", "infeasible", "optimal")


def read_verdict(out: str) -> str:
    """First recognizable verdict line. `unsat` is checked before `sat` because
    `sat` is a substring of it."""
    for line in out.splitlines():
        t = line.strip().lower()
        if t.startswith("unsat"):
            return "unsat"
        if t.startswith("sat"):
            return "sat"
        if t.startswith("unknown"):
            return "unknown"
        # HiGHS
        if "model status" in t:
            return t.split(":")[-1].strip()
    return "none"


def run(solver: str, path: pathlib.Path, timeout: float, plan) -> tuple[str, float, bool]:
    """Returns (verdict, seconds, timed_out)."""
    cmd = list(SOLVERS[solver])
    if solver == "ay":
        cmd += ["--memory", str(plan.memlimit_mb)]
    cmd.append(str(path))
    t0 = time.monotonic()
    try:
        p = run_captured(
            cmd, plan.memlimit_mb, timeout, label=f"lp_bench.py[{solver}]",
            env=dict(os.environ, MEMLIMIT=str(plan.memlimit_mb),
                     NBCORE=str(plan.nbcore)),
        )
    except OSError:
        return ("error", 0.0, False)
    if p.memout:
        return ("memout", p.wall_sec, False)
    if p.timed_out:
        return ("timeout", timeout, True)
    if p.output_truncated:
        return ("error", p.wall_sec, False)
    dt = time.monotonic() - t0
    return (read_verdict(p.stdout), dt, False)


def geomean(xs: list[float]) -> float:
    xs = [x for x in xs if x > 0]
    if not xs:
        return float("nan")
    return math.exp(sum(math.log(x) for x in xs) / len(xs))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", type=pathlib.Path)
    ap.add_argument("--files", nargs="*", type=pathlib.Path, default=[])
    ap.add_argument("--solvers", default="z3,ay")
    ap.add_argument("--timeout", type=float, default=30.0)
    ap.add_argument("--limit", type=int, default=0, help="0 = no limit")
    ap.add_argument("--out", type=pathlib.Path,
                    default=pathlib.Path("evals/results/lp-bench/latest.json"))
    args = ap.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        ap.error("--timeout must be finite and positive")

    warn_concurrent_build()
    plan = plan_solver_resources(1, label="lp_bench.py")
    resource_plan = {
        "requested_jobs": 1,
        "jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "enforcement": "process-group rss_watchdog; ay --memory; MEMLIMIT/NBCORE environment",
    }

    files = list(args.files)
    if args.corpus:
        files += sorted(args.corpus.glob("*.smt2"))
    if args.limit:
        files = files[: args.limit]
    if not files:
        print("no instances", file=sys.stderr)
        return 2

    solvers = args.solvers.split(",")
    for s in solvers:
        if s not in SOLVERS:
            print(f"unknown solver {s!r} (known: {', '.join(SOLVERS)})", file=sys.stderr)
            return 2

    times: dict[str, list[float]] = {s: [] for s in solvers}
    solved: dict[str, int] = {s: 0 for s in solvers}
    disagreements: list[str] = []
    # Only instances EVERY solver decided feed the geomean.
    common: dict[str, list[float]] = {s: [] for s in solvers}
    records = []

    print(f"{'instance':<44} " + " ".join(f"{s:>16}" for s in solvers))
    print("-" * (44 + 17 * len(solvers)))
    for f in files:
        row, verdicts, all_decided = [], {}, True
        per: dict[str, float] = {}
        for s in solvers:
            v, dt, to = run(s, f, args.timeout, plan)
            per[s] = dt
            if to or v in ("unknown", "none", "memout", "error"):
                all_decided = False
            else:
                solved[s] += 1
                verdicts[s] = v
            times[s].append(dt)
            row.append(f"{v[:8]:>8}{dt:>8.2f}")
            records.append({"file": str(f), "solver": s, "verdict": v,
                            "time_sec": dt, "timed_out": to})

        decided = {s: v for s, v in verdicts.items() if v in ("sat", "unsat")}
        if len(set(decided.values())) > 1:
            disagreements.append(f"{f.name}: {decided}")
        if all_decided:
            for s in solvers:
                common[s].append(per[s])

        print(f"{f.name[:44]:<44} " + " ".join(row))

    print()
    n_common = len(next(iter(common.values()))) if common else 0
    print(f"instances: {len(files)}   decided by all: {n_common}")
    for s in solvers:
        print(
            f"  {s:<8} solved={solved[s]:<4} "
            f"geomean(all-decided)={geomean(common[s]):>8.3f}s  "
            f"total={sum(times[s]):>9.1f}s"
        )

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps({
        "timeout_sec": args.timeout,
        "resource_plan": resource_plan,
        "solvers": solvers,
        "instances": [str(path) for path in files],
        "records": records,
        "disagreements": disagreements,
    }, indent=2) + "\n")
    print(f"wrote {args.out}")

    if disagreements:
        print("\n*** VERDICT DISAGREEMENTS (a fast wrong answer is not a win) ***")
        for d in disagreements:
            print(f"  {d}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
