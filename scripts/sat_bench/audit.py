#!/usr/bin/env python3
# ay-script: sat-bve-audit
"""Soundness audit for BVE-enabled builds on known-verdict SAT instances.

Wrong answers are critical failures. Unknown, timeout, and memory-limit results
are retained as completeness evidence rather than silently discarded.
"""

from __future__ import annotations

import argparse
import glob
import json
import math
import os
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts"))
from _oom_guard import (  # noqa: E402
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)


def run_ay(ay_bin: str, cnf: str, timeout: float, plan):
    """Return ``(verdict, wall_seconds, returncode)`` under the exact plan."""
    try:
        result = run_captured(
            [
                ay_bin,
                "--memory",
                str(plan.memlimit_mb),
                "--no-proof",
                "-t",
                str(int(timeout * 1000)),
                cnf,
            ],
            plan.memlimit_mb,
            timeout + 20,
            label="sat_bench/audit.py",
            env=dict(
                os.environ,
                MEMLIMIT=str(plan.memlimit_mb),
                NBCORE=str(plan.nbcore),
            ),
        )
    except OSError:
        return "ERROR", 0.0, None
    if result.memout:
        return "MEMOUT", result.wall_sec, result.returncode
    if result.timed_out:
        return "TIMEOUT", result.wall_sec, result.returncode
    if result.output_truncated:
        return "ERROR", result.wall_sec, result.returncode
    for line in result.stdout.splitlines():
        if line.startswith("s "):
            if "UNSATISFIABLE" in line:
                return "UNSAT", result.wall_sec, result.returncode
            if "SATISFIABLE" in line:
                return "SAT", result.wall_sec, result.returncode
    return (
        "UNKNOWN" if result.returncode == 0 else "ERROR",
        result.wall_sec,
        result.returncode,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--ay-bin",
        default=os.environ.get("AY_BIN", str(REPO / "target/release/ay")),
        help="ay binary to audit (env: AY_BIN)",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO / "evals/results/sat-bve-audit/latest.json",
        help="JSON evidence output (includes the enforced resource envelope)",
    )
    args = parser.parse_args()

    warn_concurrent_build()
    plan = plan_solver_resources(1, label="sat_bench/audit.py")
    envelope = {
        "requested_jobs": 1,
        "jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "enforcement": (
            "ay --memory; process-group rss_watchdog; MEMLIMIT/NBCORE environment"
        ),
    }
    print(f"resource plan: {json.dumps(envelope, sort_keys=True)}")

    braun = sorted(glob.glob(str(REPO / "benchmarks/sat/eq_atree_braun/*.unsat.cnf")))
    groups = [
        (
            "braun(UNSAT)",
            "UNSAT",
            [
                "/tmp/satcampaign/reg_" + os.path.basename(path)
                if os.path.exists("/tmp/satcampaign/reg_" + os.path.basename(path))
                else path
                for path in braun
            ],
            60,
        ),
        ("barrel6(UNSAT)", "UNSAT", ["/tmp/satcampaign/reg_cmu-bmc-barrel6.cnf"], 60),
        ("crn(UNSAT)", "UNSAT", ["/tmp/satcampaign/reg_crn_11_99_u.cnf"], 60),
        (
            "uf250(SAT,model-recon)",
            "SAT",
            sorted(glob.glob("/tmp/satlib_clean/uf250/*.cnf"))[:25],
            30,
        ),
        (
            "uuf250(UNSAT)",
            "UNSAT",
            sorted(glob.glob("/tmp/satlib_clean/uuf250/*.cnf"))[:15],
            30,
        ),
    ]

    wrong = []
    totals = {}
    records = []
    missing = 0
    for label, expected, files, timeout in groups:
        count = correct = incomplete = 0
        for path in files:
            if not os.path.exists(path):
                missing += 1
                continue
            verdict, wall, returncode = run_ay(args.ay_bin, path, timeout, plan)
            count += 1
            record = {
                "group": label,
                "path": path,
                "expected": expected,
                "verdict": verdict,
                "wall_seconds": wall,
                "returncode": returncode,
                "timeout_seconds": timeout,
            }
            records.append(record)
            if verdict == expected:
                correct += 1
            elif verdict in ("UNKNOWN", "TIMEOUT", "MEMOUT", "ERROR"):
                incomplete += 1
            else:
                wrong.append(record)
                print(
                    f"  !!! WRONG: {os.path.basename(path)} expected {expected} got {verdict}"
                )
        totals[label] = {"count": count, "correct": correct, "incomplete": incomplete}
        print(
            f"{label:26} n={count:3} correct={correct:3} "
            f"incomplete={incomplete:3} (expected {expected})"
        )

    total = sum(item["count"] for item in totals.values())
    correct = sum(item["correct"] for item in totals.values())
    incomplete = sum(item["incomplete"] for item in totals.values())
    vacuous = total == 0
    verdict = "UNSOUND" if wrong else ("INCOMPLETE" if vacuous else "SOUND")
    evidence = {
        "schema": "ay-sat-bve-audit-v1",
        "binary": args.ay_bin,
        "resource_plan": envelope,
        "groups": totals,
        "records": records,
        "wrong": wrong,
        "missing_inputs": missing,
        "total": total,
        "correct": correct,
        "incomplete": incomplete,
        "verdict": verdict,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(evidence, indent=2) + "\n", encoding="utf-8")

    print("\n===== AUDIT SUMMARY =====")
    print(f"WRONG ANSWERS (CRITICAL): {len(wrong)}")
    print(f"correct {correct}/{total}, incomplete {incomplete}/{total}, missing {missing}")
    print(f"VERDICT: {verdict}")
    print(f"evidence: {args.out}")
    if wrong:
        return 1
    if vacuous:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
