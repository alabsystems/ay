# ay-script: nra-oracle-shards-lib
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Bounded persistence primitives for :mod:`nra_oracle_shards`."""

from __future__ import annotations

import collections
import hashlib
import json
import os
import re
from dataclasses import dataclass
from pathlib import Path


ACCEPTED_FUZZ_RETURN_CODES = frozenset((0, 1))
# Bounds both queued-work metadata and the aggregate result index. Full output
# remains in one JSON file per shard and is never duplicated into the index.
MAX_SHARDS = 10_000
# Captured stdout and stderr are each bounded at 1 MiB by `_oom_guard`.
# Sixty-four in-flight children therefore cap retained capture buffers at
# 128 MiB before ordinary Python/executor overhead.
MAX_IN_FLIGHT = 64
ORACLE_COUNT_KEYS = (
    "cases_executed",
    "differential_asserts",
    "reference_comparisons",
    "reference_failures",
    "divergences",
)
ORACLE_SUMMARY_PATTERNS = {
    "cases_executed": re.compile(
        r"^cases executed[ \t]+([0-9]+)[ \t]*\r?$", re.MULTILINE
    ),
    "differential_asserts": re.compile(
        r"^differential asserts[ \t]+([0-9]+)[ \t]*\r?$", re.MULTILINE
    ),
    "reference_comparisons": re.compile(
        r"^reference comparisons[ \t]+([0-9]+)[ \t]*\r?$", re.MULTILINE
    ),
    "reference_failures": re.compile(
        r"^reference failures[ \t]+([0-9]+)[ \t]*\r?$", re.MULTILINE
    ),
    "divergences": re.compile(r"^DIVERGENCES[ \t]+([0-9]+)[ \t]*\r?$", re.MULTILINE),
}


@dataclass(frozen=True)
class Shard:
    """One half-open oracle case range."""

    ordinal: int
    start: int
    cases: int

    @property
    def end(self) -> int:
        return self.start + self.cases


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def atomic_write_json(path: Path, payload) -> None:
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    with temporary.open("w", encoding="utf-8") as output:
        json.dump(payload, output, indent=2, sort_keys=True)
        output.write("\n")
        output.flush()
        os.fsync(output.fileno())
    os.replace(temporary, path)


def shard_count(cases: int, shard_cases: int) -> int:
    return (cases + shard_cases - 1) // shard_cases


def iter_shards(start: int, cases: int, shard_cases: int):
    cursor = start
    remaining = cases
    ordinal = 0
    while remaining:
        count = min(remaining, shard_cases)
        yield Shard(ordinal, cursor, count)
        cursor += count
        remaining -= count
        ordinal += 1


def abandonment_reason(captured, accepted_returncodes) -> str | None:
    if captured.memout:
        return "memout"
    if captured.timed_out:
        return "timeout"
    if captured.cancelled:
        return "cancelled"
    if captured.output_truncated:
        return "output-truncated"
    if captured.returncode not in accepted_returncodes:
        return f"nonaccepted-returncode-{captured.returncode}"
    return None


def parse_oracle_summary(stdout: str, expected_cases: int, returncode: int) -> dict:
    values = {
        key: [int(value) for value in pattern.findall(stdout)]
        for key, pattern in ORACLE_SUMMARY_PATTERNS.items()
    }
    occurrences = {key: len(found) for key, found in values.items()}
    counts = {
        key: found[0] if len(found) == 1 else None for key, found in values.items()
    }
    errors = [
        f"{key}: expected exactly one field, found {occurrences[key]}"
        for key in ORACLE_COUNT_KEYS
        if occurrences[key] != 1
    ]
    if all(counts[key] is not None for key in ORACLE_COUNT_KEYS):
        if counts["cases_executed"] != expected_cases:
            errors.append(
                f"cases_executed: expected {expected_cases}, got "
                f"{counts['cases_executed']}"
            )
        if counts["differential_asserts"] <= 0:
            errors.append("differential_asserts: expected a positive count")
        if counts["reference_comparisons"] <= 0:
            errors.append("reference_comparisons: expected a positive count")
        if counts["reference_failures"] != 0:
            errors.append("reference_failures: expected zero")
        divergences = counts["divergences"]
        if returncode == 0 and divergences != 0:
            errors.append("returncode 0 requires zero divergences")
        elif returncode == 1 and divergences <= 0:
            errors.append("returncode 1 requires positive divergences")
        elif returncode not in ACCEPTED_FUZZ_RETURN_CODES:
            errors.append(f"nonaccepted returncode {returncode}")
    return {
        "valid": not errors,
        "counts": counts,
        "occurrences": occurrences,
        "parsed_values": values,
        "errors": errors,
    }


def validate_fuzz_record(record: dict, expected_cases: int) -> None:
    summary = parse_oracle_summary(
        record["stdout"], expected_cases, record["returncode"]
    )
    record["oracle_summary"] = summary
    record["oracle_counts"] = summary["counts"]
    if record["abandoned"] or summary["valid"]:
        return
    record["status"] = "abandoned"
    record["abandoned"] = True
    record["abandon_reason"] = "invalid-oracle-summary"
    record.pop("oracle_outcome", None)


def captured_record(
    kind: str, command: list[str], captured, accepted_returncodes
) -> dict:
    reason = abandonment_reason(captured, accepted_returncodes)
    record = {
        "kind": kind,
        "status": "abandoned" if reason else "completed",
        "abandoned": reason is not None,
        "abandon_reason": reason,
        "command": command,
        "returncode": captured.returncode,
        "timed_out": captured.timed_out,
        "memout": captured.memout,
        "cancelled": captured.cancelled,
        "wall_seconds": captured.wall_sec,
        "stdout_truncated": captured.stdout_truncated,
        "stderr_truncated": captured.stderr_truncated,
        "stdout": captured.stdout,
        "stderr": captured.stderr,
    }
    if kind == "fuzz" and reason is None:
        record["oracle_outcome"] = (
            "clean" if captured.returncode == 0 else "divergences"
        )
    return record


def failed_record(kind: str, command: list[str], reason: str, error: str) -> dict:
    return {
        "kind": kind,
        "status": "abandoned",
        "abandoned": True,
        "abandon_reason": reason,
        "command": command,
        "returncode": None,
        "timed_out": False,
        "memout": False,
        "cancelled": reason.startswith("cancelled"),
        "wall_seconds": None,
        "stdout_truncated": False,
        "stderr_truncated": False,
        "stdout": "",
        "stderr": error,
    }


def summarize(records: list[dict]) -> dict:
    reasons = collections.Counter(
        record["abandon_reason"] for record in records if record["abandoned"]
    )
    accepted = [record for record in records if not record["abandoned"]]
    oracle_totals = {
        key: sum(record.get("oracle_counts", {}).get(key, 0) for record in accepted)
        for key in ORACLE_COUNT_KEYS
    }
    return {
        "shards": len(records),
        "completed_shards": sum(not record["abandoned"] for record in records),
        "abandoned_shards": sum(record["abandoned"] for record in records),
        "completed_cases": sum(
            record["shard"]["cases"] for record in records if not record["abandoned"]
        ),
        "abandoned_cases": sum(
            record["shard"]["cases"] for record in records if record["abandoned"]
        ),
        "divergence_shards": sum(
            record.get("oracle_outcome") == "divergences" for record in records
        ),
        "oracle_totals": oracle_totals,
        "abandon_reasons": dict(sorted(reasons.items())),
    }
