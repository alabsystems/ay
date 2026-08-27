#!/usr/bin/env python3
# ay-script: nra-oracle-shards
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Run a bounded, auditable sharded ay-nra-oracle fuzz campaign.

Each oracle process is isolated behind the shared process-group RSS watchdog.
The shared planner is called exactly once, so its host lease remains held from
the reference probe until every shard has exited.  Shards that do not finish
normally are persisted as abandoned ranges and never count as executed work.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import re
import signal
import struct
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _oom_guard import (
    CAPTURE_LIMIT_BYTES,
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)
from nra_oracle_campaign import CampaignControl, run_campaign
from nra_oracle_shards_lib import (
    MAX_IN_FLIGHT,
    MAX_SHARDS,
    atomic_write_json,
    captured_record,
    failed_record,
    sha256_file,
    shard_count,
    summarize,
)


U64_MAX = (1 << 64) - 1
USIZE_MAX = (1 << (8 * struct.calcsize("P"))) - 1
REFERENCE_VERSION = re.compile(r"^reference libz3: .* \(([^()]*)\)$", re.MULTILINE)


def positive_int(raw: str) -> int:
    value = int(raw)
    if value <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return value


def nonnegative_int(raw: str) -> int:
    value = int(raw)
    if value < 0:
        raise argparse.ArgumentTypeError("must be non-negative")
    return value


def positive_finite(raw: str) -> float:
    value = float(raw)
    if not math.isfinite(value) or value <= 0:
        raise argparse.ArgumentTypeError("must be finite and positive")
    return value


def parse_args(argv=None):
    parser = argparse.ArgumentParser(
        description="Run resource-enveloped ay-nra-oracle fuzz shards."
    )
    parser.add_argument(
        "--binary", type=Path, required=True, help="prebuilt ay-nra-oracle executable"
    )
    parser.add_argument(
        "--z3",
        type=Path,
        required=True,
        help="trusted ABI-compatible libz3 shared library",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        required=True,
        help="fresh directory for envelope and shard JSON",
    )
    parser.add_argument("--seed", type=nonnegative_int, default=1)
    parser.add_argument("--start", type=nonnegative_int, default=0)
    parser.add_argument(
        "--cases",
        type=positive_int,
        required=True,
        help="total number of case indices to cover",
    )
    parser.add_argument(
        "--shard-cases",
        type=positive_int,
        default=2000,
        help="maximum cases in one child (default: 2000)",
    )
    parser.add_argument(
        "--jobs",
        type=positive_int,
        default=1,
        help="requested concurrent children (default: 1)",
    )
    parser.add_argument(
        "--mem-floor-mb",
        type=positive_int,
        default=1024,
        help="minimum admitted MiB per child (default: 1024)",
    )
    parser.add_argument(
        "--timeout",
        type=positive_finite,
        default=1200.0,
        help="wall seconds per oracle child (default: 1200)",
    )
    parser.add_argument(
        "--progress",
        type=nonnegative_int,
        default=0,
        help="oracle progress interval inside each shard",
    )
    parser.add_argument(
        "--max-cost",
        type=nonnegative_int,
        default=420,
        help="oracle work-cost bound; 0 means unbounded",
    )
    args = parser.parse_args(argv)
    if args.seed > U64_MAX or args.start > U64_MAX:
        parser.error("--seed and --start must fit u64")
    if args.progress > U64_MAX or args.cases > U64_MAX:
        parser.error("--progress and --cases must fit u64")
    if args.max_cost > USIZE_MAX:
        parser.error("--max-cost must fit the oracle binary's usize")
    if args.start + args.cases > U64_MAX:
        parser.error("the requested half-open case range exceeds u64")
    if shard_count(args.cases, args.shard_cases) > MAX_SHARDS:
        parser.error(
            f"campaign needs more than the fixed {MAX_SHARDS}-shard evidence cap; "
            "increase --shard-cases"
        )
    return args


def resolved_file(path: Path, label: str, executable: bool = False) -> Path:
    try:
        resolved = path.expanduser().resolve(strict=True)
    except OSError as error:
        raise ValueError(f"{label} does not exist: {path}: {error}") from error
    if not resolved.is_file():
        raise ValueError(f"{label} is not a regular file: {resolved}")
    if executable and not os.access(resolved, os.X_OK):
        raise ValueError(f"{label} is not executable: {resolved}")
    return resolved


def prepare_output_dir(path: Path) -> Path:
    output = path.expanduser().resolve()
    output.mkdir(parents=True, exist_ok=True)
    if not output.is_dir():
        raise ValueError(f"output path is not a directory: {output}")
    if any(output.iterdir()):
        raise ValueError(f"output directory must be empty: {output}")
    return output


def child_environment(plan) -> dict[str, str]:
    environment = dict(os.environ)
    environment["MEMLIMIT"] = str(plan.memlimit_mb)
    environment["NBCORE"] = str(plan.nbcore)
    return environment


def resource_envelope(
    args, plan, binary: Path, z3_path: Path, effective_jobs: int
) -> dict:
    oom_guard = Path(__file__).resolve().with_name("_oom_guard.py")
    return {
        "schema": "ay.nra-oracle-resource-envelope/v1",
        "requested_jobs": args.jobs,
        "user_requested_jobs": args.jobs,
        "effective_planner_jobs": effective_jobs,
        "admitted_jobs": plan.jobs,
        "max_in_flight_children": MAX_IN_FLIGHT,
        "planned_shards": shard_count(args.cases, args.shard_cases),
        "max_shards": MAX_SHARDS,
        "requested_mem_floor_mb": args.mem_floor_mb,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "planner": "scripts/_oom_guard.py::plan_solver_resources",
        "planner_sha256": sha256_file(oom_guard),
        "enforcement": "run_captured process-group rss_watchdog (zero grace)",
        "rss_watchdog_grace_mb": 0,
        "capture_limit_bytes_per_stream": CAPTURE_LIMIT_BYTES,
        "capture_streams_per_child": 2,
        "max_in_flight_capture_bytes": plan.jobs * 2 * CAPTURE_LIMIT_BYTES,
        "solver_environment": {
            "MEMLIMIT": str(plan.memlimit_mb),
            "NBCORE": str(plan.nbcore),
        },
        "timeout_seconds_per_child": args.timeout,
        "timeout_enforcement": "run_captured process-group wall clock",
        "oracle_binary_path": str(binary),
        "oracle_binary_sha256": sha256_file(binary),
        "trusted_z3_path": str(z3_path),
        "trusted_z3_sha256": sha256_file(z3_path),
        "trusted_z3_version": None,
        "trusted_z3_probe_status": "pending",
    }


def run_probe(
    binary: Path, z3_path: Path, plan, timeout: float, environment: dict[str, str]
) -> tuple[dict, str | None]:
    command = [str(binary), "probe", "--z3", str(z3_path)]
    try:
        captured = run_captured(
            command,
            plan.memlimit_mb,
            timeout,
            label="nra_oracle_shards.py[probe]",
            env=environment,
        )
        record = captured_record("probe", command, captured, frozenset((0,)))
    except Exception as error:  # Persist harness failures as evidence too.
        record = failed_record("probe", command, "harness-abort", repr(error))
        record["harness_abort"] = {
            "source": "run_captured",
            "detail": repr(error),
        }
    match = REFERENCE_VERSION.search(record["stdout"])
    version = match.group(1) if match else None
    if version is None and not record["abandoned"]:
        record["status"] = "abandoned"
        record["abandoned"] = True
        record["abandon_reason"] = "missing-reference-version"
    return record, version


def install_cancel_handlers(control: CampaignControl):
    previous = {}

    def request_cancel(signum, _frame):
        control.request_user_cancel()
        print(
            f"cancelling oracle shards after signal {signum}",
            file=sys.stderr,
            flush=True,
        )

    for signum in (signal.SIGINT, signal.SIGTERM):
        previous[signum] = signal.getsignal(signum)
        signal.signal(signum, request_cancel)
    return previous


def persist_json(path: Path, payload, context: str) -> bool:
    try:
        atomic_write_json(path, payload)
    except Exception as error:
        print(
            f"error: harness abort during {context} persistence: {error!r}",
            file=sys.stderr,
        )
        return False
    return True


def admit_resources(args):
    warn_concurrent_build()
    planned_shards = shard_count(args.cases, args.shard_cases)
    effective_jobs = min(args.jobs, planned_shards, MAX_IN_FLIGHT)
    plan = plan_solver_resources(
        effective_jobs,
        mem_floor_mb=args.mem_floor_mb,
        label="nra_oracle_shards.py",
    )
    if plan.jobs <= 0 or plan.jobs > effective_jobs:
        raise RuntimeError(
            f"planner admitted {plan.jobs} jobs outside effective cap {effective_jobs}"
        )
    return plan, effective_jobs


def main(argv=None) -> int:
    args = parse_args(argv)
    try:
        binary = resolved_file(args.binary, "oracle binary", executable=True)
        z3_path = resolved_file(args.z3, "trusted libz3")
        output = prepare_output_dir(args.out_dir)
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    try:
        # This is the sole planning call. _oom_guard retains its process-scoped
        # host lease until this harness and every guarded child have exited.
        plan, effective_jobs = admit_resources(args)
    except (OSError, RuntimeError, ValueError) as error:
        print(f"error: resource admission failed: {error}", file=sys.stderr)
        return 2
    envelope = resource_envelope(args, plan, binary, z3_path, effective_jobs)
    envelope_path = output / "resource-envelope.json"
    if not persist_json(envelope_path, envelope, "resource-envelope"):
        return 2
    environment = child_environment(plan)

    probe, version = run_probe(binary, z3_path, plan, args.timeout, environment)
    if not persist_json(output / "reference-probe.json", probe, "reference-probe"):
        return 2
    envelope["trusted_z3_version"] = version
    envelope["trusted_z3_probe_status"] = probe["status"]
    if not persist_json(envelope_path, envelope, "resource-envelope"):
        return 2
    if probe["abandoned"]:
        print(
            f"reference probe abandoned: {probe['abandon_reason']}; no shards started",
            file=sys.stderr,
        )
        return 130 if probe["cancelled"] else 2

    control = CampaignControl()
    previous_handlers = install_cancel_handlers(control)
    try:
        records = run_campaign(
            args,
            binary,
            z3_path,
            output,
            plan,
            environment,
            envelope,
            control,
        )
    except Exception as error:
        control.request_harness_abort("campaign", repr(error))
        records = []
    finally:
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)

    summary = summarize(records)
    campaign = {
        "schema": "ay.nra-oracle-shards/v1",
        "configuration": {
            "seed": args.seed,
            "start": args.start,
            "cases": args.cases,
            "shard_cases": args.shard_cases,
            "progress": args.progress,
            "max_cost": args.max_cost,
        },
        "resource_envelope": envelope,
        "termination": {
            "kind": (
                "harness-abort"
                if control.harness_aborted.is_set()
                else "user-signal"
                if control.user_cancelled.is_set()
                else "complete"
            ),
            "harness_abort_events": control.abort_events(),
        },
        "summary": summary,
        "results": records,
    }
    if not persist_json(output / "results.json", campaign, "aggregate-results"):
        return 2
    print(json.dumps(summary, sort_keys=True), flush=True)
    if control.harness_aborted.is_set():
        return 2
    if control.user_cancelled.is_set():
        return 130
    if summary["abandoned_shards"]:
        return 2
    return 1 if summary["divergence_shards"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
