# ay-script: nra-oracle-campaign
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Bounded execution and abort coordination for NRA oracle shards."""

from __future__ import annotations

import threading
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from dataclasses import asdict
from pathlib import Path

from _oom_guard import run_captured
from nra_oracle_shards_lib import (
    ACCEPTED_FUZZ_RETURN_CODES,
    Shard,
    atomic_write_json,
    captured_record,
    failed_record,
    iter_shards,
    shard_count,
    validate_fuzz_record,
)


class CampaignControl:
    """Separate user cancellation from a campaign-fatal harness abort."""

    def __init__(self):
        self.stop_event = threading.Event()
        self.user_cancelled = threading.Event()
        self.harness_aborted = threading.Event()
        self._abort_events = []
        self._lock = threading.Lock()

    def request_user_cancel(self) -> None:
        self.user_cancelled.set()
        self.stop_event.set()

    def request_harness_abort(
        self, source: str, detail: str, shard: Shard | None = None
    ) -> None:
        event = {"source": source, "detail": detail}
        if shard is not None:
            event["shard_ordinal"] = shard.ordinal
            event["shard_start"] = shard.start
        with self._lock:
            self._abort_events.append(event)
        self.harness_aborted.set()
        self.stop_event.set()

    def abort_events(self) -> list[dict]:
        with self._lock:
            return list(self._abort_events)

    def before_start_reason(self) -> str:
        if self.harness_aborted.is_set():
            return "harness-abort-before-start"
        return "cancelled-before-start"


def shard_paths(output: Path, shard: Shard) -> tuple[Path, Path]:
    stem = f"shard-{shard.ordinal:06d}-{shard.start}-{shard.end}"
    return output / f"{stem}.json", output / f"{stem}-divergences"


def shard_command(
    args, binary: Path, z3_path: Path, shard: Shard, dump_dir: Path
) -> list[str]:
    return [
        str(binary),
        "fuzz",
        "--z3",
        str(z3_path),
        "--seed",
        str(args.seed),
        "--start",
        str(shard.start),
        "--cases",
        str(shard.cases),
        "--progress",
        str(args.progress),
        "--max-cost",
        str(args.max_cost),
        "--dump",
        str(dump_dir),
    ]


def aggregate_index(record: dict, result_path: Path, persisted: bool = True) -> dict:
    """Keep only bounded metadata; full streams live in ``result_path``."""
    keys = (
        "status",
        "abandoned",
        "abandon_reason",
        "returncode",
        "timed_out",
        "memout",
        "cancelled",
        "wall_seconds",
        "stdout_truncated",
        "stderr_truncated",
        "oracle_outcome",
        "oracle_counts",
        "harness_abort",
    )
    index = {key: record[key] for key in keys if key in record}
    index["shard"] = record["shard"]
    index["persisted"] = persisted
    index["result_json"] = result_path.name if persisted else None
    return index


def attach_shard(record: dict, shard: Shard, envelope: dict) -> None:
    record["shard"] = asdict(shard) | {"end_exclusive": shard.end}
    record["resource_envelope"] = envelope


def persist_record(
    result_path: Path, record: dict, control: CampaignControl, shard: Shard
) -> None:
    try:
        atomic_write_json(result_path, record)
    except Exception as error:
        control.request_harness_abort("persistence", repr(error), shard)
        raise


def run_shard(
    args,
    binary: Path,
    z3_path: Path,
    output: Path,
    shard: Shard,
    plan,
    environment: dict[str, str],
    envelope: dict,
    control: CampaignControl,
) -> dict:
    result_path, dump_dir = shard_paths(output, shard)
    command = shard_command(args, binary, z3_path, shard, dump_dir)
    if control.stop_event.is_set():
        record = failed_record("fuzz", command, control.before_start_reason(), "")
    else:
        try:
            captured = run_captured(
                command,
                plan.memlimit_mb,
                args.timeout,
                label=f"nra_oracle_shards.py[shard-{shard.ordinal}]",
                env=environment,
                cancel_event=control.stop_event,
            )
        except Exception as error:
            control.request_harness_abort("run_captured", repr(error), shard)
            record = failed_record("fuzz", command, "harness-abort", repr(error))
            record["harness_abort"] = control.abort_events()
        else:
            record = captured_record(
                "fuzz", command, captured, ACCEPTED_FUZZ_RETURN_CODES
            )
            validate_fuzz_record(record, shard.cases)
            if captured.cancelled and control.harness_aborted.is_set():
                record["abandon_reason"] = "harness-abort-cancelled"
                record["harness_abort"] = control.abort_events()
    attach_shard(record, shard, envelope)
    persist_record(result_path, record, control, shard)
    return aggregate_index(record, result_path)


def abandoned_index(
    args,
    binary: Path,
    z3_path: Path,
    output: Path,
    shard: Shard,
    envelope: dict,
    control: CampaignControl,
) -> dict:
    result_path, dump_dir = shard_paths(output, shard)
    command = shard_command(args, binary, z3_path, shard, dump_dir)
    record = failed_record("fuzz", command, control.before_start_reason(), "")
    if control.harness_aborted.is_set():
        record["harness_abort"] = control.abort_events()
    attach_shard(record, shard, envelope)
    try:
        persist_record(result_path, record, control, shard)
    except Exception as error:
        index = aggregate_index(record, result_path, persisted=False)
        index["persistence_error"] = repr(error)
        return index
    return aggregate_index(record, result_path)


def future_index(
    future,
    shard: Shard,
    args,
    binary: Path,
    z3_path: Path,
    output: Path,
    envelope: dict,
    control: CampaignControl,
) -> dict:
    try:
        return future.result()
    except Exception as error:
        control.request_harness_abort("future", repr(error), shard)
        return abandoned_index(args, binary, z3_path, output, shard, envelope, control)


def persist_remaining(
    shards,
    args,
    binary: Path,
    z3_path: Path,
    output: Path,
    envelope: dict,
    control: CampaignControl,
) -> list[dict]:
    records = []
    persistence_working = True
    for shard in shards:
        if persistence_working:
            index = abandoned_index(
                args, binary, z3_path, output, shard, envelope, control
            )
            persistence_working = index["persisted"]
        else:
            result_path, _ = shard_paths(output, shard)
            record = failed_record(
                "fuzz", [], control.before_start_reason(), "persistence unavailable"
            )
            attach_shard(record, shard, envelope)
            index = aggregate_index(record, result_path, persisted=False)
        records.append(index)
    return records


def fill_slots(
    pool,
    pending: dict,
    shards,
    records: list[dict],
    args,
    binary: Path,
    z3_path: Path,
    output: Path,
    plan,
    environment: dict[str, str],
    envelope: dict,
    control: CampaignControl,
) -> None:
    while len(pending) < plan.jobs and not control.stop_event.is_set():
        try:
            shard = next(shards)
        except StopIteration:
            return
        try:
            future = pool.submit(
                run_shard,
                args,
                binary,
                z3_path,
                output,
                shard,
                plan,
                environment,
                envelope,
                control,
            )
            pending[future] = shard
        except Exception as error:
            control.request_harness_abort("future-submit", repr(error), shard)
            records.append(
                abandoned_index(args, binary, z3_path, output, shard, envelope, control)
            )
            return


def run_campaign(
    args,
    binary: Path,
    z3_path: Path,
    output: Path,
    plan,
    environment: dict[str, str],
    envelope: dict,
    control: CampaignControl,
) -> list[dict]:
    total = shard_count(args.cases, args.shard_cases)
    shards = iter(iter_shards(args.start, args.cases, args.shard_cases))
    records = []
    pending = {}
    try:
        with ThreadPoolExecutor(max_workers=plan.jobs) as pool:
            fill_slots(
                pool,
                pending,
                shards,
                records,
                args,
                binary,
                z3_path,
                output,
                plan,
                environment,
                envelope,
                control,
            )
            while pending:
                assert len(pending) <= plan.jobs
                try:
                    done, _ = wait(pending, return_when=FIRST_COMPLETED)
                except KeyboardInterrupt:
                    control.request_user_cancel()
                    continue
                except Exception as error:
                    control.request_harness_abort("future-wait", repr(error))
                    done = set(pending)
                for future in done:
                    shard = pending.pop(future)
                    records.append(
                        future_index(
                            future,
                            shard,
                            args,
                            binary,
                            z3_path,
                            output,
                            envelope,
                            control,
                        )
                    )
                    print(
                        f"[{len(records)}/{total}] {records[-1]['status']} "
                        f"shard {shard.start}:{shard.end}",
                        flush=True,
                    )
                fill_slots(
                    pool,
                    pending,
                    shards,
                    records,
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
        control.request_harness_abort("executor", repr(error))
    if control.stop_event.is_set():
        records.extend(
            persist_remaining(shards, args, binary, z3_path, output, envelope, control)
        )
    return sorted(records, key=lambda record: record["shard"]["ordinal"])
