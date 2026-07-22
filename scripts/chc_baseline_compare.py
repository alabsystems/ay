#!/usr/bin/env python3
# ay-script: chc-baseline-compare
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Compare current AY CHC results against a checked baseline snapshot."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import platform
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _oom_guard import (  # noqa: E402
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)

SOLVED = {"sat", "unsat"}
STATUS_ORDER = ("sat", "unsat", "unknown")


def sha256_file(path: Path) -> str | None:
    if not path.is_file():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def first_status(stdout: str) -> str:
    for raw in stdout.splitlines():
        line = raw.strip()
        if line in STATUS_ORDER:
            return line
        if line == "s SATISFIABLE":
            return "sat"
        if line == "s UNSATISFIABLE":
            return "unsat"
        if line == "s UNKNOWN":
            return "unknown"
    return "no-status"


def run_text(args: list[str], cwd: Path, timeout: float = 10.0) -> str:
    with tempfile.TemporaryFile(mode="w+b") as output:
        try:
            subprocess.run(
                args,
                cwd=cwd,
                stdout=output,
                stderr=subprocess.STDOUT,
                timeout=timeout,
                check=False,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            return f"unavailable: {exc}"
        output.seek(0)
        captured = output.read(1024 * 1024 + 1)
    if len(captured) > 1024 * 1024:
        return "unavailable: metadata output exceeded 1 MiB"
    return captured.decode("utf-8", errors="replace").strip()


def resolve_bench_dir(root: Path, baseline_path: Path, baseline: dict[str, Any], override: str | None) -> Path:
    raw = override or baseline.get("benchmarks_dir")
    if not raw:
        raise SystemExit("baseline is missing benchmarks_dir; pass --bench-dir")
    path = Path(raw)
    if path.is_absolute():
        return path
    candidates = [root / path, baseline_path.parent / path]
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return candidates[0]


def run_case(ay: Path, bench_file: Path, timeout_sec: int, plan) -> dict[str, Any]:
    start = time.monotonic()
    timeout_ms = str(max(timeout_sec, 0) * 1000)
    args = [str(ay), "--chc", "--memory", str(plan.memlimit_mb),
            "--timeout", timeout_ms, str(bench_file)]
    try:
        proc = run_captured(
            args,
            plan.memlimit_mb,
            max(timeout_sec, 0) + 4,
            label="chc_baseline_compare.py",
            env=dict(os.environ, MEMLIMIT=str(plan.memlimit_mb),
                     NBCORE=str(plan.nbcore)),
        )
        elapsed_ms = int(round((time.monotonic() - start) * 1000))
        if proc.memout:
            status = "memout"
        elif proc.timed_out:
            status = "timeout"
        elif proc.output_truncated:
            status = "error"
        else:
            status = first_status(proc.stdout)
        if proc.returncode == 124 and status in {"no-status", "unknown"}:
            status = "timeout"
        return {
            "status": status,
            "elapsed_ms": elapsed_ms,
            "exit_code": proc.returncode,
            "stdout": proc.stdout[-4096:],
            "stderr": proc.stderr[-4096:],
        }
    except (OSError, RuntimeError, ValueError) as exc:
        elapsed_ms = int(round((time.monotonic() - start) * 1000))
        return {
            "status": "error",
            "elapsed_ms": elapsed_ms,
            "exit_code": None,
            "stdout": "",
            "stderr": str(exc),
        }


def compare(args: argparse.Namespace) -> int:
    root = Path.cwd()
    baseline_path = Path(args.baseline)
    ay = Path(args.ay)
    baseline = json.loads(baseline_path.read_text())
    timeout_sec = int(args.timeout if args.timeout is not None else baseline.get("timeout_sec", 15))
    bench_dir = resolve_bench_dir(root, baseline_path, baseline, args.bench_dir)

    if not bench_dir.exists():
        raise SystemExit(f"benchmark directory not found: {bench_dir}")
    if not ay.is_file():
        raise SystemExit(f"ay binary not found: {ay}")

    warn_concurrent_build()
    plan = plan_solver_resources(1, label="chc_baseline_compare.py")
    resource_plan = {
        "requested_jobs": 1,
        "jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "enforcement": "ay --memory + process-group rss_watchdog; MEMLIMIT/NBCORE environment",
    }

    profile = args.profile or ("fast-proxy" if args.timeout is not None else "same-timeout")
    run_type = "fast-proxy-warning-only" if profile == "fast-proxy" else "same-timeout-gate"
    timeout_relation = "shorter-than-baseline" if args.timeout is not None else "same-as-baseline"
    if args.timeout is not None and args.timeout >= int(baseline.get("timeout_sec", timeout_sec)):
        timeout_relation = "not-shorter-than-baseline"

    try:
        version_run = run_captured(
            [str(ay), "--version"], plan.memlimit_mb, 10,
            label="chc_baseline_compare.py[version]",
            env=dict(os.environ, MEMLIMIT=str(plan.memlimit_mb),
                     NBCORE=str(plan.nbcore)),
        )
        if (
            version_run.memout
            or version_run.timed_out
            or version_run.cancelled
            or version_run.output_truncated
            or version_run.returncode != 0
        ):
            version = "unavailable: guarded version probe failed"
        else:
            version = (version_run.stdout or version_run.stderr).strip()
            if not version:
                version = "unavailable: empty version output"
    except (OSError, RuntimeError, ValueError) as exc:
        version = f"unavailable: {exc}"
    rows: list[dict[str, Any]] = []
    summary = {
        "checked": 0,
        "baseline_solved_checked": 0,
        "current_solved_checked": 0,
        "direct_regressions": 0,
        "proxy_regressions": 0,
        "wrong_answers": 0,
        "invalid_answers": 0,
        "missing_benchmarks": 0,
        "non_comparable_baseline": 0,
        "current_status_counts": {},
    }

    baseline_plan = baseline.get("resource_plan")
    comparable_fields = ("jobs", "memlimit_mb_per_child", "nbcore_per_child",
                         "headroom_mb", "enforcement")
    baseline_comparable = isinstance(baseline_plan, dict) and all(
        baseline_plan.get(field) == resource_plan[field]
        for field in comparable_fields
    )
    if not baseline_comparable:
        summary["non_comparable_baseline"] = 1

    for case in baseline.get("benchmarks", []):
        rel = str(case.get("file", ""))
        if not rel:
            continue
        expected = case.get("expected_status")
        baseline_status = str(case.get("status", "unknown"))
        bench_file = bench_dir / rel
        summary["checked"] += 1
        if baseline_status in SOLVED:
            summary["baseline_solved_checked"] += 1
        if not bench_file.is_file():
            result = {
                "status": "missing",
                "elapsed_ms": 0,
                "exit_code": None,
                "stdout": "",
                "stderr": f"missing benchmark: {bench_file}",
            }
            summary["missing_benchmarks"] += 1
        else:
            result = run_case(ay, bench_file, timeout_sec, plan)

        current = result["status"]
        if current in SOLVED:
            summary["current_solved_checked"] += 1
        summary["current_status_counts"][current] = summary["current_status_counts"].get(current, 0) + 1

        direct_regression = baseline_status in SOLVED and current != baseline_status
        proxy_regression = baseline_status in SOLVED and current not in SOLVED
        wrong_answer = expected in SOLVED and current in SOLVED and current != expected
        invalid_answer = current in {"no-status", "error", "missing"} or (
            result["exit_code"] not in (0, 124, None) and current not in SOLVED | {"unknown", "timeout"}
        )
        if direct_regression:
            summary["direct_regressions"] += 1
        if proxy_regression:
            summary["proxy_regressions"] += 1
        if wrong_answer:
            summary["wrong_answers"] += 1
        if invalid_answer:
            summary["invalid_answers"] += 1

        rows.append(
            {
                "file": rel,
                "baseline_status": baseline_status,
                "current_status": current,
                "expected_status": expected,
                "baseline_elapsed_ms": case.get("elapsed_ms"),
                "current_elapsed_ms": result["elapsed_ms"],
                "exit_code": result["exit_code"],
                "direct_regression": direct_regression,
                "proxy_regression": proxy_regression,
                "wrong_answer": wrong_answer,
                "invalid_answer": invalid_answer,
                "stderr_tail": result["stderr"],
            }
        )

    payload = {
        "schema": "ay.chc-baseline-compare/v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "baseline": {
            "path": str(baseline_path),
            "suite": baseline.get("suite"),
            "baseline_commit": baseline.get("baseline_commit"),
            "baseline_date": baseline.get("baseline_date"),
            "timeout_sec": baseline.get("timeout_sec"),
            "solved_total": baseline.get("solved_total"),
            "benchmarks_total": baseline.get("benchmarks_total"),
        },
        "run_classification": {
            "profile": profile,
            "run_type": run_type,
            "timeout_relation": timeout_relation,
            "timeout_sec": timeout_sec,
        },
        "resource_plan": resource_plan,
        "baseline_resource_plan": baseline_plan,
        "baseline_comparable": baseline_comparable,
        "provenance": {
            "ay": str(ay),
            "ay_sha256": sha256_file(ay),
            "ay_version": version,
            "benchmark_dir": str(bench_dir),
            "host": platform.platform(),
            "python": sys.version.split()[0],
            "cwd": str(root),
            "git_head": run_text(["git", "rev-parse", "HEAD"], root),
            "git_status_porcelain": run_text(["git", "status", "--porcelain=v1"], root),
        },
        "summary": summary,
        "cases": rows,
    }

    json_out = Path(args.json_out)
    csv_out = Path(args.csv_out)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    csv_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    with csv_out.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()) if rows else ["file"])
        writer.writeheader()
        writer.writerows(rows)

    fail = (
        profile == "same-timeout"
        and (
            summary["direct_regressions"] > 0
            or summary["wrong_answers"] > 0
            or summary["invalid_answers"] > 0
            or summary["missing_benchmarks"] > 0
            or not baseline_comparable
        )
    )
    return 1 if fail else 0


def main() -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    cmp_parser = sub.add_parser("compare")
    cmp_parser.add_argument("--baseline", required=True)
    cmp_parser.add_argument("--ay", required=True)
    cmp_parser.add_argument("--bench-dir")
    cmp_parser.add_argument("--run-all", action="store_true")
    cmp_parser.add_argument("--json-out", required=True)
    cmp_parser.add_argument("--csv-out", required=True)
    cmp_parser.add_argument("--timeout", type=int)
    cmp_parser.add_argument("--profile", choices=["same-timeout", "fast-proxy"], default=os.environ.get("AY_CHC_BASELINE_PROFILE"))
    args = parser.parse_args()
    if args.command == "compare":
        return compare(args)
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())
