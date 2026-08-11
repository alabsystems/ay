#!/usr/bin/env python3
# ay-script: ufbv-fixpoint-audit
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Reproducible two-lane audit of the exact 121-file UFBV fixpoint family.

Each benchmark is run in a fresh process in two modes:

* ``default``: the production solve path;
* ``self_check``: a fresh process with the fail-closed ``--self-check`` policy.

Both lanes suppress persistent proof output with ``--no-proof`` and request
canonical human statistics with ``-st``.  The ``self_check`` lane is fresh
reproducibility/check-policy evidence, not an implementation-independent
checker.  For every SAT result, closure also requires the emitted
``model_validation.checked_projection_certificate=1`` statistic, confirming
that the checked-projection path ran in that process.

The campaign is deliberately serial.  ``scripts/_oom_guard.py`` acquires the
host-wide harness lease, plans one explicit child envelope, passes ``MEMLIMIT``
and ``NBCORE``, and backstops every ``ay --memory`` child with the exact
process-group RSS watchdog.  A 50 ms build monitor cancels and discards a child
if Cargo/Targo/rustc/compiler_consumer appears.  Confirmed lane results are checkpointed
after every process and can be resumed only under byte-identical provenance
after their exact bounded stdout/stderr are rehashed and every output claim is
recomputed.  The repository must be clean, and
``ay --version`` must self-report the current HEAD.  That report is an
attestation, while the binary SHA-256 identifies the artifact; neither is
presented as proof that the binary was built from HEAD.  The version preflight
has a fixed 120-second cold-launch allowance because a freshly linked 93 MiB
macOS binary with no quarantine marker has been observed to need about 82
seconds on its first launch.

Examples:

  python3 scripts/ufbv_fixpoint_audit.py /tmp/ufbv-fixpoint-audit.json
  python3 scripts/ufbv_fixpoint_audit.py OUT.json \
      --binary target/release/ay --default-timeout-seconds 15 \
      --self-check-timeout-seconds 15
  python3 scripts/ufbv_fixpoint_audit.py --self-test
  python3 scripts/ufbv_fixpoint_audit.py \
      --verify-report OUT.json --expect-head FULL_GIT_SHA

The first two forms execute 242 solver processes (121 files x two lanes).
``--verify-report`` is read-only and never solves a formula; it requires the
reported binary (or an explicit byte-identical ``--binary`` relocation) and
re-runs only its ``--version`` attestation.  ``--self-test`` is pure and never
opens the corpus or executes the solver.
"""

from __future__ import annotations

import argparse
import collections
import datetime as dt
import hashlib
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import threading
import time
from types import SimpleNamespace


REPO = Path(__file__).resolve().parent.parent
SCRIPTS = REPO / "scripts"
OOM_GUARD = SCRIPTS / "_oom_guard.py"
sys.path.insert(0, str(SCRIPTS))
from _oom_guard import (  # noqa: E402
    CAPTURE_LIMIT_BYTES,
    count_active_rustc,
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)


DEFAULT_BINARY = REPO / "target" / "release" / "ay"
DEFAULT_CORPUS = REPO / "benchmarks" / "smtlib-all" / "UFBV"
FAMILY_GLOB = (
    "non-incremental__UFBV__wintersteiger__fmsd13__fixpoint__*.smt2"
)
EXPECTED_FILE_COUNT = 121
EXPECTED_STATUS_COUNTS = {"sat": 26, "unsat": 74, "unknown": 21}
EXPECTED_FAMILY_SHA256 = (
    "ef9912b78e493410189a3bfa733987a873a1e7ca5d36a529f42426f312391dd9"
)
LANES = ("default", "self_check")
DECISIVE = frozenset(("sat", "unsat"))
OBSERVED_VERDICTS = frozenset(
    (
        "sat",
        "unsat",
        "unknown",
        "timeout",
        "memout",
        "output-truncated",
        "error",
        "invalid-output",
    )
)
VERDICT_RE = re.compile(r"^(sat|unsat|unknown)$", re.ASCII)
SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.ASCII)
STATUS_RE = re.compile(
    r"^[ \t]*\(set-info[ \t]+:status[ \t]+"
    r"(sat|unsat|unknown)[ \t]*\)[ \t]*(?:;.*)?$",
    re.MULTILINE,
)
STATISTICS_HEADER = "c --- AY statistics ---"
STATISTICS_MODE_RE = re.compile(r"^c ay\.mode:[ \t]+([a-z][a-z-]*)[ \t]*$", re.ASCII)
STATISTICS_RESULT_RE = re.compile(
    r"^c ay\.result:[ \t]+([a-z][a-z-]*)[ \t]*$", re.ASCII
)
STATISTICS_WALL_TIME_RE = re.compile(
    r"^c ay\.wall_time_ms:[ \t]+(0|[1-9][0-9]{0,19})[ \t]*$", re.ASCII
)
STATISTICS_BUILD_STAMP_RE = re.compile(r"^c ay\.build\.stamp: ([^\r\n]+)$", re.ASCII)
STATISTICS_COUNTER_RE = re.compile(
    r"^c ([A-Za-z0-9_.-]+):[ \t]+(0|[1-9][0-9]{0,19})[ \t]*$", re.ASCII
)
RESERVED_STATISTICS_KEYS = frozenset(
    ("ay.mode", "ay.result", "ay.wall_time_ms", "ay.build.stamp")
)
PROJECTION_CERTIFICATE_KEY = "model_validation.checked_projection_certificate"
PROJECTION_CERTIFICATE_RE = re.compile(
    rf"^c {re.escape(PROJECTION_CERTIFICATE_KEY)}:[ \t]+"
    r"(0|[1-9][0-9]{0,19})[ \t]*$",
    re.ASCII,
)
STATISTICS_PARSER_DESCRIPTION = (
    "exact retained stderr reparsed into one ordered canonical SMT -st block "
    "for every clean token-only verdict; terminal/error/truncated records reject "
    "complete blocks; SAT confirmation additionally requires exactly "
    f"{PROJECTION_CERTIFICATE_KEY}=1"
)
RAW_OUTPUT_POLICY_DESCRIPTION = (
    "exact run_captured stdout/stderr text retained at the shared "
    f"{CAPTURE_LIMIT_BYTES}-byte per-stream cap; hashes, verdict evidence, "
    "diagnostics, statistics, and certificate claims are recomputed from it"
)
DIAGNOSTIC_LIMIT_CHARS = 2000
UNEXPECTED_STDOUT_SAMPLE_LIMIT = 20
U64_MAX = (1 << 64) - 1
DEFAULT_TIMEOUT_SECONDS = 15.0
DEFAULT_QUIET_SECONDS = 15.0
VERSION_PREFLIGHT_TIMEOUT_SECONDS = 120.0
BUILD_POLL_SECONDS = 0.05
CAMPAIGN_LABEL = "ufbv-fixpoint-audit-v3"
CHECKPOINT_SCHEMA = "ay.ufbv-fixpoint-audit-checkpoint.v3"
REPORT_SCHEMA = "ay.ufbv-fixpoint-audit.v3"
REPORT_INTEGRITY_SCHEMA = "ay.ufbv-fixpoint-audit-integrity.v1"
SOLVER_ENV_SCHEMA = "ay.ufbv-fixpoint-solver-environment.v1"
SOLVER_ENV_FIXED = {
    "LANG": "C",
    "LC_ALL": "C",
    "TMPDIR": "/tmp",
    "TZ": "UTC",
}
CHECKPOINT_SCOPE_DESCRIPTION = (
    "trusted-local resume state; provenance and retained outputs are structurally "
    "revalidated, but this JSON is not signed execution-authenticity evidence"
)
VERIFICATION_SCOPE = {
    "integrity": (
        "canonical JSON SHA-256 provides structural consistency only; it is not "
        "a signature or proof of execution authenticity"
    ),
    "trusted_local_inputs": (
        "verification trusts the current local harness, OOM guard, canonical "
        "corpus, and byte-verified executable available in the workspace"
    ),
    "expected_head": (
        "--expect-head is a historical assertion checked against report and "
        "binary self-attestation; it does not prove Git object availability or ancestry"
    ),
    "toctou": (
        "identity and hash rechecks narrow but do not eliminate filesystem races; "
        "the workspace and report/checkpoint storage are trusted-local inputs"
    ),
    "raw_output": RAW_OUTPUT_POLICY_DESCRIPTION,
}


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def bytes_sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def json_exact_equal(left: object, right: object) -> bool:
    """JSON-value equality that does not equate booleans with numbers."""

    try:
        options = {"sort_keys": True, "separators": (",", ":"), "allow_nan": False}
        return json.dumps(left, **options) == json.dumps(right, **options)
    except (TypeError, ValueError):
        return False


def report_integrity(payload_without_integrity: dict[str, object]) -> dict[str, str]:
    if "integrity" in payload_without_integrity:
        raise ValueError("report integrity payload must exclude the integrity field")
    canonical = json.dumps(
        payload_without_integrity,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    return {
        "schema": REPORT_INTEGRITY_SCHEMA,
        "canonical_json_sha256": bytes_sha256(canonical),
        "scope": "all report fields except integrity; structural checksum, not a signature",
    }


def sha256(path: Path, cancel_event: threading.Event | None = None) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            if cancel_event is not None and cancel_event.is_set():
                raise RuntimeError("build appeared while hashing campaign inputs")
            digest.update(chunk)
    return digest.hexdigest()


def sanitized_solver_environment(
    _ambient_environment: object,
    memlimit_mb: int,
    nbcore: int,
) -> dict[str, str]:
    """Return the complete environment visible to every solver process.

    No ambient variables are inherited.  In particular, AY/TRUST/Rust logging
    and allocator knobs cannot silently change a campaign.  The two resource
    variables are always replaced with the values from the OOM-guard plan.
    """

    if memlimit_mb <= 0 or nbcore <= 0:
        raise ValueError("solver resource environment must be positive")
    environment = dict(SOLVER_ENV_FIXED)
    environment["MEMLIMIT"] = str(memlimit_mb)
    environment["NBCORE"] = str(nbcore)
    return dict(sorted(environment.items()))


def solver_environment_provenance(environment: dict[str, str]) -> dict[str, object]:
    return {
        "schema": SOLVER_ENV_SCHEMA,
        "effective": dict(sorted(environment.items())),
        "fixed": dict(sorted(SOLVER_ENV_FIXED.items())),
        "planner_overrides": ["MEMLIMIT", "NBCORE"],
        "inherited_allowlist": [],
        "ambient_policy": (
            "all inherited variables are removed, including AY_*, TRUST_*, "
            "RUST_*, allocator tuning, and inherited MEMLIMIT/NBCORE"
        ),
    }


def binary_identity(path: Path) -> tuple[int, int, int, int]:
    stat = path.stat()
    return (stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns)


def atomic_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp.{os.getpid()}")
    try:
        temporary.write_text(
            json.dumps(value, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        os.replace(temporary, path)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def git_output(*args: str) -> bytes:
    return subprocess.run(
        ["git", *args],
        cwd=REPO,
        capture_output=True,
        timeout=30,
        check=True,
    ).stdout


def source_identity() -> dict[str, object]:
    head = git_output("rev-parse", "HEAD").decode("utf-8").strip()
    status = git_output(
        "status",
        "--porcelain=v1",
        "-z",
        "--untracked-files=all",
    )
    return {
        "head": head,
        "dirty": bool(status),
        "status_porcelain_sha256": bytes_sha256(status),
    }


def binary_self_attested_commit(version_output: str) -> str:
    prefix = "build.commit="
    commits = [
        line[len(prefix) :]
        for line in version_output.splitlines()
        if line.startswith(prefix)
    ]
    if len(commits) != 1 or not commits[0]:
        raise RuntimeError(
            "ay --version did not report exactly one nonempty build.commit"
        )
    return commits[0]


def binary_self_attested_build_stamp(version_output: str) -> str:
    prefix = "build.stamp="
    stamps = [
        line[len(prefix) :]
        for line in version_output.splitlines()
        if line.startswith(prefix)
    ]
    if len(stamps) != 1 or not stamps[0]:
        raise RuntimeError(
            "ay --version did not report exactly one nonempty build.stamp"
        )
    return stamps[0]


def parse_declared_status(text: str, label: str) -> str:
    matches = STATUS_RE.findall(text)
    if len(matches) != 1:
        raise RuntimeError(
            f"expected one anchored (set-info :status ...) in {label}, "
            f"found {len(matches)}"
        )
    return matches[0]


def collect_family(
    corpus: Path,
    cancel_event: threading.Event | None = None,
) -> tuple[list[Path], list[dict[str, object]], str]:
    files = sorted(corpus.glob(FAMILY_GLOB))
    if len(files) != EXPECTED_FILE_COUNT:
        raise RuntimeError(
            f"expected exact {EXPECTED_FILE_COUNT}-file family, found "
            f"{len(files)} under {corpus}"
        )

    entries: list[dict[str, object]] = []
    statuses: collections.Counter[str] = collections.Counter()
    manifest_digest = hashlib.sha256()
    for path in files:
        if cancel_event is not None and cancel_event.is_set():
            raise RuntimeError("build appeared while inventorying the corpus")
        manifest_digest.update(path.name.encode("utf-8"))
        manifest_digest.update(b"\0")
        contents = bytearray()
        file_digest = hashlib.sha256()
        with path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                if cancel_event is not None and cancel_event.is_set():
                    raise RuntimeError(
                        "build appeared while inventorying the corpus"
                    )
                contents.extend(chunk)
                file_digest.update(chunk)
                manifest_digest.update(chunk)
        manifest_digest.update(b"\0")
        declared = parse_declared_status(
            contents.decode("utf-8", errors="replace"), str(path)
        )
        entry = {
            "name": path.name,
            "bytes": len(contents),
            "sha256": file_digest.hexdigest(),
            "declared": declared,
        }
        entries.append(entry)
        statuses[declared] += 1

    if dict(statuses) != EXPECTED_STATUS_COUNTS:
        raise RuntimeError(
            "the 121-file family has the wrong declared-status distribution: "
            f"expected {EXPECTED_STATUS_COUNTS}, found {dict(statuses)}"
        )
    family_hash = manifest_digest.hexdigest()
    if family_hash != EXPECTED_FAMILY_SHA256:
        raise RuntimeError(
            "the exact family has the wrong canonical manifest SHA-256: "
            f"expected {EXPECTED_FAMILY_SHA256}, found {family_hash}"
        )
    return files, entries, family_hash


def wait_for_sustained_build_quiescence(quiet_seconds: float) -> None:
    quiet_since: float | None = None
    last_notice = 0.0
    while True:
        active = count_active_rustc()
        now = time.monotonic()
        if active:
            quiet_since = None
        elif quiet_since is None:
            quiet_since = now
        quiet_for = 0.0 if quiet_since is None else now - quiet_since
        if quiet_for >= quiet_seconds:
            return
        if now - last_notice >= 15.0:
            print(
                f"[preflight] active_builds={active} "
                f"quiet_for={quiet_for:.0f}s/{quiet_seconds:.0f}s",
                file=sys.stderr,
                flush=True,
            )
            last_notice = now
        time.sleep(1.0)


class BuildMonitor:
    """Continuously detect builds and provide a run_captured cancel event."""

    def __init__(self) -> None:
        self.build_seen = threading.Event()
        self._stop = threading.Event()
        self._ready = threading.Event()
        self._error: BaseException | None = None
        self._thread = threading.Thread(
            target=self._run,
            name="ufbv-fixpoint-build-monitor",
            daemon=True,
        )
        self._thread.start()
        if not self._ready.wait(timeout=35):
            self._stop.set()
            self._thread.join(timeout=35)
            raise RuntimeError("concurrent-build monitor did not start")
        self.check("starting campaign monitor")

    def _run(self) -> None:
        try:
            while not self._stop.is_set():
                active = count_active_rustc()
                self._ready.set()
                if active:
                    self.build_seen.set()
                    return
                self._stop.wait(BUILD_POLL_SECONDS)
        except BaseException as error:  # fail closed if process inspection dies
            self._error = error
            self.build_seen.set()
            self._ready.set()

    def check(self, context: str) -> None:
        if self._error is not None:
            raise RuntimeError(
                f"cannot inspect concurrent builds while {context}: {self._error}"
            ) from self._error
        if self.build_seen.is_set():
            raise RuntimeError(
                f"a Cargo/Targo/rustc/compiler_consumer build appeared while {context}; "
                "the active child, if any, was cancelled and its result was discarded"
            )

    def stop(self) -> None:
        self._stop.set()
        self._thread.join(timeout=35)
        if self._thread.is_alive():
            raise RuntimeError("concurrent-build monitor did not stop")


def lane_command(binary: Path, path: Path, memlimit_mb: int, lane: str) -> list[str]:
    if lane not in LANES:
        raise ValueError(f"unknown lane: {lane}")
    command = [
        str(binary),
        "solve",
        "--quiet",
        "--no-proof",
        "--no-verify-proof",
        "-st",
        "--memory",
        str(memlimit_mb),
    ]
    if lane == "self_check":
        command.append("--self-check")
    command.append(str(path))
    return command


def classify_run(run: object) -> tuple[str, list[str], list[str], str | None]:
    stdout = str(run.stdout)
    nonempty = [line.strip() for line in stdout.splitlines() if line.strip()]
    tokens = [
        match.group(1)
        for line in nonempty
        if (match := VERDICT_RE.fullmatch(line)) is not None
    ]
    unexpected = [line for line in nonempty if VERDICT_RE.fullmatch(line) is None]

    if run.output_truncated:
        return "output-truncated", tokens, unexpected, "captured output exceeded 1 MiB"
    if run.memout:
        return "memout", tokens, unexpected, None
    if run.timed_out:
        return "timeout", tokens, unexpected, None
    if run.returncode != 0:
        return "error", tokens, unexpected, f"nonzero exit status {run.returncode}"
    if len(tokens) != 1 or unexpected:
        detail = (
            f"expected exactly one token-only verdict line; found "
            f"tokens={tokens!r}, unexpected_lines={len(unexpected)}"
        )
        return "invalid-output", tokens, unexpected, detail
    return tokens[0], tokens, unexpected, None


def validate_captured_text(value: object, label: str) -> str:
    """Validate text retained by ``run_captured`` at its shared byte cap."""

    if type(value) is not str:
        raise RuntimeError(f"record {label} has non-string captured output")
    # run_captured decodes its at-most-CAPTURE_LIMIT_BYTES byte prefix with
    # replacement. Re-encoding replacement characters can be larger than the
    # captured bytes, while the decoded scalar count cannot be larger.
    if len(value) > CAPTURE_LIMIT_BYTES:
        raise RuntimeError(
            f"record {label} exceeds the shared {CAPTURE_LIMIT_BYTES}-byte "
            "capture limit"
        )
    return value


def derive_record_output_fields(
    *,
    declared: str,
    stdout: str,
    stderr: str,
    returncode: int,
    timed_out: bool,
    memout: bool,
    stdout_truncated: bool,
    stderr_truncated: bool,
) -> dict[str, object]:
    """Derive every output claim from the exact retained stream text."""

    run = SimpleNamespace(
        stdout=stdout,
        stderr=stderr,
        returncode=returncode,
        timed_out=timed_out,
        memout=memout,
        output_truncated=stdout_truncated or stderr_truncated,
    )
    observed, tokens, unexpected, invalid_reason = classify_run(run)
    statistics_evidence = parse_human_statistics(stderr)
    stderr_lines = stderr.splitlines()
    statistics_emitted_sat = any(
        (match := STATISTICS_RESULT_RE.fullmatch(line)) is not None
        and match.group(1) == "sat"
        for line in stderr_lines
    )
    certificate_emitted_sat = any(
        (match := PROJECTION_CERTIFICATE_RE.fullmatch(line)) is not None
        and int(match.group(1)) == 1
        for line in stderr_lines
    )
    derived: dict[str, object] = {
        "observed": observed,
        "tokens": tokens,
        "unexpected_stdout_count": len(unexpected),
        "stdout_sha256": bytes_sha256(stdout.encode("utf-8")),
        "stderr_sha256": bytes_sha256(stderr.encode("utf-8")),
        "statistics_evidence": statistics_evidence,
        "unsafe_emitted_sat": (
            declared in ("unsat", "unknown")
            and (
                "sat" in tokens
                or statistics_emitted_sat
                or certificate_emitted_sat
            )
        ),
        "checked_projection_certificate": (
            checked_projection_certificate_confirmed(
                statistics_evidence, observed
            )
        ),
    }
    if unexpected:
        derived["unexpected_stdout"] = [
            line[:DIAGNOSTIC_LIMIT_CHARS]
            for line in unexpected[:UNEXPECTED_STDOUT_SAMPLE_LIMIT]
        ]
    diagnostic = invalid_reason
    if diagnostic is None and observed not in DECISIVE:
        diagnostic = (stderr or stdout).strip() or None
    if diagnostic is not None:
        derived["diagnostic"] = diagnostic[:DIAGNOSTIC_LIMIT_CHARS]
    return derived


def parse_human_statistics(stderr: str) -> dict[str, object]:
    """Extract complete ``-st`` blocks and mark strict producer canonicality."""

    lines = stderr.splitlines()
    header_count = sum(line == STATISTICS_HEADER for line in lines)
    blocks: list[dict[str, object]] = []
    normalized_block_text: list[str] = []
    for index, line in enumerate(lines):
        if line != STATISTICS_HEADER:
            continue
        # RunStatistics::print_to_stderr brackets every block with exact `c`
        # lines. A diagnostic containing a lookalike statistic is not evidence.
        if index == 0 or lines[index - 1] != "c":
            continue
        end = index + 1
        while end < len(lines) and lines[end] != "c":
            end += 1
        if end == len(lines):
            continue
        # This is a normalized parser excerpt. Only the retained full stderr
        # preserves the exact captured text (splitlines intentionally does not).
        block_text = "\n".join(lines[index - 1 : end + 1]) + "\n"
        modes: list[str] = []
        results: list[str] = []
        wall_times: list[int] = []
        build_stamps: list[str] = []
        certificates: list[int] = []
        numeric_values_valid = True
        body = lines[index + 1 : end]
        canonical = len(body) >= 4
        required_patterns = (
            STATISTICS_MODE_RE,
            STATISTICS_RESULT_RE,
            STATISTICS_WALL_TIME_RE,
            STATISTICS_BUILD_STAMP_RE,
        )
        if canonical:
            canonical = all(
                pattern.fullmatch(body[position]) is not None
                for position, pattern in enumerate(required_patterns)
            )

        counter_keys: list[str] = []
        for statistic_line in body:
            if match := STATISTICS_MODE_RE.fullmatch(statistic_line):
                modes.append(match.group(1))
            if match := STATISTICS_RESULT_RE.fullmatch(statistic_line):
                results.append(match.group(1))
            if match := STATISTICS_WALL_TIME_RE.fullmatch(statistic_line):
                value = int(match.group(1))
                numeric_values_valid = numeric_values_valid and value <= U64_MAX
                wall_times.append(value)
            if match := STATISTICS_BUILD_STAMP_RE.fullmatch(statistic_line):
                build_stamps.append(match.group(1))
            if match := PROJECTION_CERTIFICATE_RE.fullmatch(statistic_line):
                value = int(match.group(1))
                numeric_values_valid = numeric_values_valid and value <= U64_MAX
                certificates.append(value)
        for statistic_line in body[4:]:
            counter = STATISTICS_COUNTER_RE.fullmatch(statistic_line)
            if counter is None or counter.group(1) in RESERVED_STATISTICS_KEYS:
                canonical = False
                continue
            if int(counter.group(2)) > U64_MAX:
                canonical = False
            counter_keys.append(counter.group(1))
        if (
            len(modes) != 1
            or len(results) != 1
            or len(wall_times) != 1
            or len(build_stamps) != 1
            or len(counter_keys) != len(set(counter_keys))
            or counter_keys != sorted(counter_keys)
            or not numeric_values_valid
        ):
            canonical = False
        blocks.append(
            {
                "canonical": canonical,
                "mode_values": modes,
                "result_values": results,
                "wall_time_ms_values": wall_times,
                "build_stamp_values": build_stamps,
                "checked_projection_certificate_values": certificates,
            }
        )
        normalized_block_text.append(block_text)
    return {
        "header_count": header_count,
        "normalized_block_text": normalized_block_text,
        "blocks": blocks,
    }


def normalize_statistics_evidence(
    evidence: object, label: str
) -> dict[str, object]:
    if not isinstance(evidence, dict) or set(evidence) != {
        "header_count",
        "normalized_block_text",
        "blocks",
    }:
        raise RuntimeError(f"record {label} has invalid statistics evidence")
    header_count = evidence["header_count"]
    normalized_block_text = evidence["normalized_block_text"]
    blocks = evidence["blocks"]
    if (
        type(header_count) is not int
        or header_count < 0
        or header_count > CAPTURE_LIMIT_BYTES
    ):
        raise RuntimeError(f"record {label} has invalid statistics header count")
    if (
        not isinstance(normalized_block_text, list)
        or any(
            type(block_text) is not str
            or len(block_text.encode("utf-8")) > CAPTURE_LIMIT_BYTES
            for block_text in normalized_block_text
        )
        or not isinstance(blocks, list)
        or len(blocks) != len(normalized_block_text)
        or len(blocks) > header_count
        or len(blocks) > CAPTURE_LIMIT_BYTES
    ):
        raise RuntimeError(f"record {label} has invalid statistics blocks")

    normalized_blocks: list[dict[str, object]] = []
    for index, block in enumerate(blocks):
        if not isinstance(block, dict) or set(block) != {
            "canonical",
            "mode_values",
            "result_values",
            "wall_time_ms_values",
            "build_stamp_values",
            "checked_projection_certificate_values",
        }:
            raise RuntimeError(f"record {label} has malformed statistics block")
        modes = block["mode_values"]
        results = block["result_values"]
        wall_times = block["wall_time_ms_values"]
        build_stamps = block["build_stamp_values"]
        certificates = block["checked_projection_certificate_values"]
        if type(block["canonical"]) is not bool:
            raise RuntimeError(f"record {label} has invalid statistics grammar flag")
        if (
            not isinstance(modes, list)
            or len(modes) > CAPTURE_LIMIT_BYTES
            or any(
                type(value) is not str
                or len(value.encode("utf-8")) > CAPTURE_LIMIT_BYTES
                for value in modes
            )
        ):
            raise RuntimeError(f"record {label} has invalid statistics modes")
        if (
            not isinstance(results, list)
            or len(results) > CAPTURE_LIMIT_BYTES
            or any(
                type(value) is not str
                or len(value.encode("utf-8")) > CAPTURE_LIMIT_BYTES
                for value in results
            )
        ):
            raise RuntimeError(f"record {label} has invalid statistics results")
        if (
            not isinstance(wall_times, list)
            or len(wall_times) > CAPTURE_LIMIT_BYTES
            or any(
                type(value) is not int or value < 0 or value > U64_MAX
                for value in wall_times
            )
        ):
            raise RuntimeError(f"record {label} has invalid statistics wall times")
        if (
            not isinstance(build_stamps, list)
            or len(build_stamps) > CAPTURE_LIMIT_BYTES
            or any(
                type(value) is not str
                or not value
                or len(value.encode("utf-8")) > CAPTURE_LIMIT_BYTES
                for value in build_stamps
            )
        ):
            raise RuntimeError(f"record {label} has invalid statistics build stamps")
        if (
            not isinstance(certificates, list)
            or len(certificates) > CAPTURE_LIMIT_BYTES
            or any(
                type(value) is not int or value < 0 or value > U64_MAX
                for value in certificates
            )
        ):
            raise RuntimeError(
                f"record {label} has invalid projection certificate statistics"
            )
        reparsed = parse_human_statistics(normalized_block_text[index])
        reparsed_block_text = reparsed["normalized_block_text"]
        reparsed_blocks = reparsed["blocks"]
        if (
            reparsed["header_count"] != 1
            or reparsed_block_text != [normalized_block_text[index]]
            or not isinstance(reparsed_blocks, list)
            or len(reparsed_blocks) != 1
        ):
            raise RuntimeError(
                f"record {label} has invalid normalized statistics block text"
            )
        normalized_blocks.append(reparsed_blocks[0])
    normalized = {
        "header_count": header_count,
        "normalized_block_text": list(normalized_block_text),
        "blocks": normalized_blocks,
    }
    if not json_exact_equal(evidence, normalized):
        raise RuntimeError(
            f"record {label} has stored statistics fields that differ from "
            "its normalized block text"
        )
    return normalized


def checked_projection_certificate_confirmed(
    evidence: dict[str, object], observed: str
) -> bool:
    blocks = evidence["blocks"]
    if evidence["header_count"] != 1 or not isinstance(blocks, list):
        return False
    if observed != "sat" or len(blocks) != 1 or not isinstance(blocks[0], dict):
        return False
    block = blocks[0]
    return (
        block.get("canonical") is True
        and block.get("mode_values") == ["smt"]
        and block.get("result_values") == ["sat"]
        and len(block.get("wall_time_ms_values", [])) == 1
        and len(block.get("build_stamp_values", [])) == 1
        and block.get("checked_projection_certificate_values") == [1]
    )


def require_statistics_build_stamp(
    record: dict[str, object], expected_build_stamp: str, label: str
) -> None:
    """Require every complete retained statistics block to name this binary."""

    evidence = record["statistics_evidence"]
    if not isinstance(evidence, dict):
        raise RuntimeError(f"record {label} has invalid statistics evidence")
    blocks = evidence["blocks"]
    if not isinstance(blocks, list):
        raise RuntimeError(f"record {label} has invalid statistics blocks")
    for block in blocks:
        if not isinstance(block, dict) or block.get("build_stamp_values") != [
            expected_build_stamp
        ]:
            raise RuntimeError(
                f"record {label} statistics do not match the attested binary "
                "build stamp"
            )


def require_statistics_consistency(
    evidence: dict[str, object],
    observed: str,
    tokens: list[str],
    label: str,
) -> None:
    """Reject malformed/contradictory complete statistics envelopes."""

    blocks = evidence["blocks"]
    header_count = evidence["header_count"]
    if not isinstance(blocks, list) or type(header_count) is not int:
        raise RuntimeError(f"record {label} has invalid statistics evidence")
    if header_count > 1 or len(blocks) > 1:
        raise RuntimeError(f"record {label} has multiple statistics envelopes")
    if observed in ("sat", "unsat", "unknown") and len(blocks) != 1:
        raise RuntimeError(
            f"record {label} has no complete statistics envelope for its verdict"
        )
    if observed not in ("sat", "unsat", "unknown") and blocks:
        raise RuntimeError(
            f"record {label} has a complete statistics envelope despite a "
            "terminal/error/truncated outcome"
        )
    for block in blocks:
        if (
            not isinstance(block, dict)
            or block.get("canonical") is not True
            or block.get("mode_values") != ["smt"]
        ):
            raise RuntimeError(
                f"record {label} has a non-canonical or non-SMT statistics envelope"
            )
        results = block.get("result_values")
        if (
            not isinstance(results, list)
            or len(results) != 1
            or results[0] not in ("sat", "unsat", "unknown")
        ):
            raise RuntimeError(
                f"record {label} has invalid statistics result evidence"
            )
        statistic_result = str(results[0])
        certificates = block.get("checked_projection_certificate_values")
        if statistic_result != "sat" and certificates != []:
            raise RuntimeError(
                f"record {label} has checked-projection SAT certificate "
                f"evidence on a {statistic_result} statistics result"
            )
        if tokens and any(token != statistic_result for token in tokens):
            raise RuntimeError(
                f"record {label} statistics result contradicts retained stdout"
            )
        if observed in ("sat", "unsat", "unknown") and statistic_result != observed:
            raise RuntimeError(
                f"record {label} statistics result contradicts derived verdict"
            )


def truth_classification(declared: str, observed: str) -> str:
    if observed in ("error", "invalid-output", "output-truncated"):
        return "invalid"
    if declared == "unknown":
        return "unscored-declared-unknown"
    if observed == declared:
        return "correct"
    if observed in DECISIVE:
        return "wrong"
    return "unresolved"


def self_check_policy_outcome(observed: str) -> str:
    if observed == "sat":
        return "reported-sat"
    if observed == "unsat":
        return "reported-unsat"
    if observed == "unknown":
        return "declined-unknown"
    if observed in ("timeout", "memout"):
        return f"unavailable-{observed}"
    return "invalid"


def cross_lane_alignment(default: str, self_check: str) -> str:
    if default not in DECISIVE:
        return "not-applicable-default-nondecision"
    if self_check == default:
        return "reproduced"
    if self_check == "unknown":
        return "not-reproduced-unknown"
    if self_check in DECISIVE:
        return "conflicting-decision"
    if self_check in ("timeout", "memout"):
        return "unavailable"
    return "invalid"


def validate_and_normalize_record(
    record: object,
    *,
    expected_file: str,
    expected_lane: str,
    expected_declared: str,
) -> dict[str, object]:
    """Validate raw streams/runtime facts and recompute every output claim."""

    label = f"{expected_file}:{expected_lane}"
    if not isinstance(record, dict):
        raise RuntimeError(f"record {label} is not a JSON object")
    required = {
        "file",
        "lane",
        "declared",
        "stdout",
        "stderr",
        "observed",
        "tokens",
        "unexpected_stdout_count",
        "returncode",
        "wall_seconds",
        "timed_out",
        "memout",
        "cancelled",
        "stdout_truncated",
        "stderr_truncated",
        "stdout_sha256",
        "stderr_sha256",
        "statistics_evidence",
        "unsafe_emitted_sat",
        "checked_projection_certificate",
    }
    optional = {
        "unexpected_stdout",
        "diagnostic",
        # These semantic values are accepted but always overwritten below.
        "truth_classification",
        "check_policy_outcome",
    }
    keys = set(record)
    missing = sorted(required - keys)
    extra = sorted(keys - required - optional)
    if missing:
        raise RuntimeError(f"record {label} lacks required fields: {missing}")
    if extra:
        raise RuntimeError(f"record {label} has unsupported fields: {extra}")
    for field in ("truth_classification", "check_policy_outcome"):
        if field in record and (
            type(record[field]) is not str or len(record[field]) > 100
        ):
            raise RuntimeError(f"record {label} has invalid {field}")

    for field, expected in (
        ("file", expected_file),
        ("lane", expected_lane),
        ("declared", expected_declared),
    ):
        value = record[field]
        if type(value) is not str or value != expected:
            raise RuntimeError(
                f"record {label} has {field}={value!r}; expected {expected!r}"
            )
    if expected_lane not in LANES or expected_declared not in EXPECTED_STATUS_COUNTS:
        raise RuntimeError(f"record {label} has an invalid expected task identity")

    stdout = validate_captured_text(record["stdout"], f"{label}:stdout")
    stderr = validate_captured_text(record["stderr"], f"{label}:stderr")

    observed = record["observed"]
    if type(observed) is not str or observed not in OBSERVED_VERDICTS:
        raise RuntimeError(f"record {label} has invalid observed verdict {observed!r}")
    tokens = record["tokens"]
    if (
        not isinstance(tokens, list)
        or len(tokens) > CAPTURE_LIMIT_BYTES
        or any(
            type(token) is not str or VERDICT_RE.fullmatch(token) is None
            for token in tokens
        )
    ):
        raise RuntimeError(f"record {label} has invalid token evidence")

    unexpected_count = record["unexpected_stdout_count"]
    if (
        type(unexpected_count) is not int
        or unexpected_count < 0
        or unexpected_count > CAPTURE_LIMIT_BYTES
    ):
        raise RuntimeError(
            f"record {label} has invalid unexpected stdout count"
        )
    unexpected = record.get("unexpected_stdout", [])
    if (
        not isinstance(unexpected, list)
        or len(unexpected) > UNEXPECTED_STDOUT_SAMPLE_LIMIT
        or any(
            type(line) is not str or len(line) > DIAGNOSTIC_LIMIT_CHARS
            for line in unexpected
        )
    ):
        raise RuntimeError(f"record {label} has invalid unexpected stdout samples")
    if len(unexpected) != min(
        unexpected_count, UNEXPECTED_STDOUT_SAMPLE_LIMIT
    ):
        raise RuntimeError(
            f"record {label} has inconsistent unexpected stdout evidence"
        )

    returncode = record["returncode"]
    if type(returncode) is not int:
        raise RuntimeError(f"record {label} has a non-integer return code")
    wall_seconds = record["wall_seconds"]
    if (
        isinstance(wall_seconds, bool)
        or not isinstance(wall_seconds, (int, float))
        or not math.isfinite(wall_seconds)
        or wall_seconds < 0
    ):
        raise RuntimeError(f"record {label} has invalid wall time")
    for field in (
        "timed_out",
        "memout",
        "cancelled",
        "stdout_truncated",
        "stderr_truncated",
    ):
        if type(record[field]) is not bool:
            raise RuntimeError(f"record {label} has non-boolean {field}")
    if sum(bool(record[field]) for field in ("timed_out", "memout", "cancelled")) > 1:
        raise RuntimeError(f"record {label} has multiple terminal causes")
    if record["cancelled"]:
        raise RuntimeError(f"record {label} retains a cancelled solver result")
    for field in ("stdout_sha256", "stderr_sha256"):
        value = record[field]
        if type(value) is not str or SHA256_RE.fullmatch(value) is None:
            raise RuntimeError(f"record {label} has invalid {field}")
    diagnostic = record.get("diagnostic")
    if diagnostic is not None and (
        type(diagnostic) is not str
        or len(diagnostic) > DIAGNOSTIC_LIMIT_CHARS
    ):
        raise RuntimeError(f"record {label} has invalid diagnostic")
    if type(record["checked_projection_certificate"]) is not bool:
        raise RuntimeError(
            f"record {label} has non-boolean projection certificate claim"
        )
    if type(record["unsafe_emitted_sat"]) is not bool:
        raise RuntimeError(
            f"record {label} has non-boolean unsafe-emitted-SAT claim"
        )
    statistics_evidence = normalize_statistics_evidence(
        record["statistics_evidence"], label
    )

    derived_output = derive_record_output_fields(
        declared=expected_declared,
        stdout=stdout,
        stderr=stderr,
        returncode=returncode,
        timed_out=record["timed_out"],
        memout=record["memout"],
        stdout_truncated=record["stdout_truncated"],
        stderr_truncated=record["stderr_truncated"],
    )
    derived_tokens = derived_output["tokens"]
    assert isinstance(derived_tokens, list)
    require_statistics_consistency(
        derived_output["statistics_evidence"],
        str(derived_output["observed"]),
        derived_tokens,
        label,
    )
    # A checkpoint/report may not substitute a digest, extracted block, token,
    # verdict, sample, or diagnostic for what the retained streams actually say.
    for field in (
        "observed",
        "tokens",
        "unexpected_stdout_count",
        "stdout_sha256",
        "stderr_sha256",
        "statistics_evidence",
        "unsafe_emitted_sat",
        "checked_projection_certificate",
    ):
        stored = statistics_evidence if field == "statistics_evidence" else record[field]
        if not json_exact_equal(stored, derived_output[field]):
            raise RuntimeError(
                f"record {label} stored {field} differs from retained output"
            )
    for field in ("unexpected_stdout", "diagnostic"):
        if (field in record) != (field in derived_output) or (
            field in record
            and not json_exact_equal(record[field], derived_output[field])
        ):
            raise RuntimeError(
                f"record {label} stored {field} differs from retained output"
            )

    derived_observed = str(derived_output["observed"])

    normalized = dict(record)
    normalized.update(derived_output)
    normalized["wall_seconds"] = float(wall_seconds)
    for field in ("unexpected_stdout", "diagnostic"):
        if field not in derived_output:
            normalized.pop(field, None)
    normalized["truth_classification"] = truth_classification(
        expected_declared, derived_observed
    )
    if expected_lane == "self_check":
        normalized["check_policy_outcome"] = self_check_policy_outcome(
            derived_observed
        )
    else:
        normalized.pop("check_policy_outcome", None)
    return normalized


def task_sequence(files: list[Path]) -> list[tuple[str, str]]:
    return [(path.name, lane) for path in files for lane in LANES]


def default_checkpoint(output: Path) -> Path:
    identity = bytes_sha256(str(output).encode("utf-8"))[:16]
    return Path(tempfile.gettempdir()) / (
        f"ay-ufbv-fixpoint-audit-{identity}.checkpoint.json"
    )


def path_is_within(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


def validate_paths(output: Path, checkpoint: Path, binary: Path, corpus: Path) -> None:
    if output.suffix.lower() != ".json":
        raise RuntimeError("output path must use a .json extension")
    if output.exists():
        raise RuntimeError(
            f"refusing to overwrite existing output; choose a new path: {output}"
        )
    if output == checkpoint:
        raise RuntimeError("output path must differ from the campaign checkpoint")
    protected = {binary, Path(__file__).resolve(), OOM_GUARD.resolve()}
    if output in protected or checkpoint in protected:
        raise RuntimeError(
            "output/checkpoint path must not alias the solver binary or harness code"
        )
    if path_is_within(output, corpus) or path_is_within(checkpoint, corpus):
        raise RuntimeError("output/checkpoint path must be outside the corpus")
    if path_is_within(checkpoint, REPO):
        raise RuntimeError(
            "checkpoint must be outside the repository so checkpoint writes do "
            "not change the pinned source identity"
        )
    if not binary.is_file() or not os.access(binary, os.X_OK):
        raise RuntimeError(f"missing executable production binary: {binary}")
    if not corpus.is_dir():
        raise RuntimeError(f"missing UFBV corpus directory: {corpus}")


def run_record(
    *,
    binary: Path,
    path: Path,
    declared: str,
    lane: str,
    timeout_seconds: float,
    memlimit_mb: int,
    env: dict[str, str],
    monitor: BuildMonitor,
) -> dict[str, object]:
    command = lane_command(binary, path, memlimit_mb, lane)
    run = run_captured(
        command,
        memlimit_mb,
        timeout_s=timeout_seconds,
        label=f"ufbv-fixpoint:{lane}:{path.name}",
        env=env,
        cancel_event=monitor.build_seen,
        cwd=REPO,
    )
    monitor.check(f"running {lane} on {path.name}")
    if run.cancelled:
        raise RuntimeError(
            f"{lane} child for {path.name} was cancelled; result discarded"
        )

    result: dict[str, object] = {
        "file": path.name,
        "lane": lane,
        "declared": declared,
        "stdout": run.stdout,
        "stderr": run.stderr,
        "returncode": run.returncode,
        "wall_seconds": round(run.wall_sec, 6),
        "timed_out": run.timed_out,
        "memout": run.memout,
        "cancelled": run.cancelled,
        "stdout_truncated": run.stdout_truncated,
        "stderr_truncated": run.stderr_truncated,
    }
    derived_output = derive_record_output_fields(
        declared=declared,
        stdout=run.stdout,
        stderr=run.stderr,
        returncode=run.returncode,
        timed_out=run.timed_out,
        memout=run.memout,
        stdout_truncated=run.stdout_truncated,
        stderr_truncated=run.stderr_truncated,
    )
    result.update(derived_output)
    observed = str(derived_output["observed"])
    result["truth_classification"] = truth_classification(declared, observed)
    if lane == "self_check":
        result["check_policy_outcome"] = self_check_policy_outcome(observed)
    return result


def summarize(
    files: list[Path],
    runs: list[dict[str, object]],
    metadata: dict[str, dict[str, object]],
) -> tuple[list[dict[str, object]], dict[str, object]]:
    by_key = {(str(run["file"]), str(run["lane"])): run for run in runs}
    results: list[dict[str, object]] = []
    lane_counts: dict[str, collections.Counter[str]] = {
        lane: collections.Counter() for lane in LANES
    }
    truth_counts: dict[str, collections.Counter[str]] = {
        lane: collections.Counter() for lane in LANES
    }
    policy_counts: collections.Counter[str] = collections.Counter()
    certificate_counts: collections.Counter[str] = collections.Counter()
    unsafe_emitted_sat_counts: collections.Counter[str] = collections.Counter()
    alignment_counts: collections.Counter[str] = collections.Counter()

    for path in files:
        declared = str(metadata[path.name]["declared"])
        normalized_lanes = {
            lane: validate_and_normalize_record(
                by_key[(path.name, lane)],
                expected_file=path.name,
                expected_lane=lane,
                expected_declared=declared,
            )
            for lane in LANES
        }
        default = normalized_lanes["default"]
        checked = normalized_lanes["self_check"]
        for lane, run in (("default", default), ("self_check", checked)):
            lane_counts[lane][f"{run['declared']}->{run['observed']}"] += 1
            truth_counts[lane][str(run["truth_classification"])] += 1
            if (
                run["declared"] == "sat"
                and run["checked_projection_certificate"]
            ):
                certificate_counts[lane] += 1
            if run["unsafe_emitted_sat"]:
                unsafe_emitted_sat_counts[lane] += 1
        checked["check_policy_outcome"] = self_check_policy_outcome(
            str(checked["observed"])
        )
        default.pop("check_policy_outcome", None)
        policy_counts[str(checked["check_policy_outcome"])] += 1
        alignment = cross_lane_alignment(
            str(default["observed"]), str(checked["observed"])
        )
        alignment_counts[alignment] += 1
        results.append(
            {
                "file": path.name,
                "bytes": metadata[path.name]["bytes"],
                "declared": default["declared"],
                "lanes": {"default": default, "self_check": checked},
                "self_check_alignment": alignment,
            }
        )

    summary = {
        "wrong": {
            lane: truth_counts[lane].get("wrong", 0) for lane in LANES
        },
        "invalid": {
            lane: truth_counts[lane].get("invalid", 0) for lane in LANES
        },
        "correct_known": {
            lane: truth_counts[lane].get("correct", 0) for lane in LANES
        },
        "unresolved_known": {
            lane: truth_counts[lane].get("unresolved", 0) for lane in LANES
        },
        "lane_counts": {
            lane: dict(sorted(lane_counts[lane].items())) for lane in LANES
        },
        "truth_classification_counts": {
            lane: dict(sorted(truth_counts[lane].items())) for lane in LANES
        },
        "declared_sat_checked_projection_certificates": {
            lane: certificate_counts[lane] for lane in LANES
        },
        "unsafe_emitted_sat": {
            lane: unsafe_emitted_sat_counts[lane] for lane in LANES
        },
        "self_check_policy_outcomes": dict(sorted(policy_counts.items())),
        "self_check_alignment": dict(sorted(alignment_counts.items())),
        "default_decisions_not_reproduced_by_self_check": sum(
            count
            for verdict, count in alignment_counts.items()
            if verdict not in (
                "reproduced",
                "not-applicable-default-nondecision",
            )
        ),
    }
    return results, summary


def audit_gate_failures(summary: dict[str, object]) -> list[str]:
    """Return every reason the exact-family closure contract did not hold."""

    failures: list[str] = []
    lane_counts = summary["lane_counts"]
    wrong = summary["wrong"]
    invalid = summary["invalid"]
    certificate_counts = summary[
        "declared_sat_checked_projection_certificates"
    ]
    unsafe_emitted_sat = summary["unsafe_emitted_sat"]
    assert isinstance(lane_counts, dict)
    assert isinstance(wrong, dict)
    assert isinstance(invalid, dict)
    assert isinstance(certificate_counts, dict)
    assert isinstance(unsafe_emitted_sat, dict)
    for lane in LANES:
        counts = lane_counts[lane]
        assert isinstance(counts, dict)
        total = sum(int(count) for count in counts.values())
        if total != EXPECTED_FILE_COUNT:
            failures.append(
                f"{lane} has {total} results; expected {EXPECTED_FILE_COUNT}"
            )
        declared_sat_total = sum(
            int(count)
            for transition, count in counts.items()
            if str(transition).startswith("sat->")
        )
        expected_sat = EXPECTED_STATUS_COUNTS["sat"]
        sat_to_sat = int(counts.get("sat->sat", 0))
        if declared_sat_total != expected_sat or sat_to_sat != expected_sat:
            failures.append(
                f"{lane} returned sat on {sat_to_sat}/{expected_sat} "
                "declared-SAT cases"
            )
        confirmed_certificates = int(certificate_counts[lane])
        if confirmed_certificates != expected_sat:
            failures.append(
                f"{lane} confirmed checked-projection certificates on "
                f"{confirmed_certificates}/{expected_sat} declared-SAT cases"
            )
        for declared in ("unsat", "unknown"):
            unsafe_sat = int(counts.get(f"{declared}->sat", 0))
            if unsafe_sat:
                failures.append(
                    f"{lane} returned sat on {unsafe_sat} declared-{declared.upper()} "
                    "case(s)"
                )
        if int(wrong[lane]):
            failures.append(f"{lane} has {int(wrong[lane])} wrong result(s)")
        if int(invalid[lane]):
            failures.append(f"{lane} has {int(invalid[lane])} invalid result(s)")
        unsafe_count = int(unsafe_emitted_sat[lane])
        if unsafe_count:
            failures.append(
                f"{lane} has {unsafe_count} declared-UNSAT/unknown case(s) "
                "with emitted SAT evidence"
            )

    not_reproduced = int(
        summary["default_decisions_not_reproduced_by_self_check"]
    )
    if not_reproduced:
        failures.append(
            "self-check did not reproduce "
            f"{not_reproduced} default decisive result(s)"
        )
    return failures


def validate_measured_source(source: object, expected_head: str) -> None:
    expected = {
        "head": expected_head,
        "dirty": False,
        "status_porcelain_sha256": bytes_sha256(b""),
    }
    if not isinstance(source, dict) or set(source) != {"at_start", "at_finish"}:
        raise RuntimeError("report has invalid source provenance")
    if not json_exact_equal(source["at_start"], expected) or not json_exact_equal(
        source["at_finish"], expected
    ):
        raise RuntimeError(
            "report source was not clean at the expected measured head at "
            "both campaign boundaries"
        )


def recompute_report_outcomes(
    reported_results: object,
    files: list[Path],
    metadata: dict[str, dict[str, object]],
    expected_build_stamp: str | None = None,
) -> tuple[list[dict[str, object]], dict[str, object]]:
    """Validate every reported raw lane record and rebuild derived outcomes."""

    if not isinstance(reported_results, list) or len(reported_results) != len(files):
        raise RuntimeError("report result membership does not match the exact family")
    runs: list[dict[str, object]] = []
    for index, path in enumerate(files):
        reported = reported_results[index]
        if not isinstance(reported, dict) or set(reported) != {
            "file",
            "bytes",
            "declared",
            "lanes",
            "self_check_alignment",
        }:
            raise RuntimeError(f"report result {index + 1} has invalid structure")
        entry = metadata[path.name]
        if (
            reported["file"] != path.name
            or reported["bytes"] != entry["bytes"]
            or reported["declared"] != entry["declared"]
        ):
            raise RuntimeError(
                f"report result {index + 1} does not match canonical member "
                f"{path.name}"
            )
        lanes = reported["lanes"]
        if not isinstance(lanes, dict) or set(lanes) != set(LANES):
            raise RuntimeError(f"report result {path.name} has invalid lanes")
        for lane in LANES:
            normalized = validate_and_normalize_record(
                lanes[lane],
                expected_file=path.name,
                expected_lane=lane,
                expected_declared=str(entry["declared"]),
            )
            if expected_build_stamp is not None:
                require_statistics_build_stamp(
                    normalized, expected_build_stamp, f"{path.name}:{lane}"
                )
            runs.append(normalized)

    recomputed_results, summary = summarize(files, runs, metadata)
    if not json_exact_equal(reported_results, recomputed_results):
        raise RuntimeError(
            "report results differ from raw-record recomputation"
        )
    closure_failures = audit_gate_failures(summary)
    summary["closure_passed"] = not closure_failures
    summary["closure_failures"] = closure_failures
    return recomputed_results, summary


def parse_utc_timestamp(value: object, label: str) -> dt.datetime:
    if type(value) is not str or not value.endswith("Z"):
        raise RuntimeError(f"report has invalid {label}")
    try:
        parsed = dt.datetime.fromisoformat(value[:-1] + "+00:00")
    except ValueError as error:
        raise RuntimeError(f"report has invalid {label}") from error
    if parsed.tzinfo != dt.timezone.utc:
        raise RuntimeError(f"report has non-UTC {label}")
    return parsed


def expected_head_value(value: str) -> str:
    if re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", value) is None:
        raise argparse.ArgumentTypeError(
            "must be a full lowercase 40- or 64-hex Git commit ID"
        )
    return value


def verify_binary_artifact(
    *,
    reported_path: str,
    reported_sha256: str,
    reported_bytes: int,
    binary_override: Path | None,
) -> tuple[Path, bool]:
    """Resolve a mandatory original/relocated binary and verify its bytes."""

    relocated = binary_override is not None
    candidate = (
        binary_override.expanduser().resolve()
        if binary_override is not None
        else Path(reported_path).expanduser().resolve()
    )
    if not candidate.is_file():
        if relocated:
            raise RuntimeError(
                f"specified verification binary is missing: {candidate}"
            )
        raise RuntimeError(
            f"reported binary is missing: {candidate}; provide its byte-identical "
            "relocated copy with --binary"
        )
    if not os.access(candidate, os.X_OK):
        raise RuntimeError(f"verification binary is not executable: {candidate}")
    if candidate.stat().st_size != reported_bytes:
        raise RuntimeError(
            f"verification binary size differs from report: {candidate}"
        )
    if sha256(candidate) != reported_sha256:
        raise RuntimeError(
            f"verification binary SHA-256 differs from report: {candidate}"
        )
    return candidate, relocated


def rerun_binary_version_attestation(
    *,
    binary: Path,
    environment: dict[str, str],
    reported_output: str,
    reported_sha256: str,
    expected_head: str,
    expected_build_stamp: str,
) -> None:
    """Re-run the byte-verified artifact's exact ``--version`` attestation."""

    identity_before = binary_identity(binary)
    completed = subprocess.run(
        [str(binary), "--version"],
        cwd=REPO,
        text=True,
        capture_output=True,
        timeout=VERSION_PREFLIGHT_TIMEOUT_SECONDS,
        check=True,
        env=environment,
    )
    if completed.stdout != reported_output:
        raise RuntimeError(
            "verified binary --version output differs exactly from the report"
        )
    if binary_self_attested_commit(completed.stdout) != expected_head:
        raise RuntimeError(
            "verified binary --version build.commit differs from expected head"
        )
    if (
        binary_self_attested_build_stamp(completed.stdout)
        != expected_build_stamp
    ):
        raise RuntimeError(
            "verified binary --version build.stamp differs from the report"
        )
    if binary_identity(binary) != identity_before or sha256(binary) != reported_sha256:
        raise RuntimeError("verification binary changed during --version preflight")


def positive_float(value: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed) or parsed <= 0:
        raise argparse.ArgumentTypeError("must be a finite positive number")
    return parsed


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Run production and --self-check lanes over the exact 121-file "
            "UFBV fixpoint family, or independently verify a v3 report."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "The report scores only declared sat/unsat files as known truth.\n"
            "Declared unknown files remain unscored but are included in lane-\n"
            "agreement accounting. Exit status 2 means the exact-family closure\n"
            "contract was not met; see summary.closure_failures in the report."
        ),
    )
    parser.add_argument(
        "output",
        nargs="?",
        type=Path,
        help="final JSON report (required in campaign mode)",
    )
    parser.add_argument(
        "--binary",
        type=Path,
        help=(
            f"production ay binary (campaign default: {DEFAULT_BINARY}); in "
            "verify mode, a byte-identical relocated binary (required when "
            "the report's original binary path is unavailable)"
        ),
    )
    parser.add_argument(
        "--corpus",
        type=Path,
        default=DEFAULT_CORPUS,
        help=f"directory containing the exact family (default: {DEFAULT_CORPUS})",
    )
    parser.add_argument(
        "--checkpoint",
        type=Path,
        help=(
            "resume checkpoint outside the repo (default: a stable temp path "
            "derived from OUTPUT)"
        ),
    )
    parser.add_argument(
        "--default-timeout-seconds",
        type=positive_float,
        default=DEFAULT_TIMEOUT_SECONDS,
        help="wall timeout for each production run (default: 15)",
    )
    parser.add_argument(
        "--self-check-timeout-seconds",
        type=positive_float,
        default=DEFAULT_TIMEOUT_SECONDS,
        help="wall timeout for each --self-check run (default: 15)",
    )
    parser.add_argument(
        "--build-quiescence-seconds",
        type=positive_float,
        default=DEFAULT_QUIET_SECONDS,
        help="required sustained no-build window before the campaign (default: 15)",
    )
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument(
        "--self-test",
        action="store_true",
        help="run pure parser/classifier tests; do not inspect corpus or execute ay",
    )
    modes.add_argument(
        "--verify-report",
        type=Path,
        metavar="REPORT",
        help=(
            "verify a completed v3 report without solving; requires "
            "--expect-head and a hash/size-matching executable at the reported "
            "path or via --binary, then re-runs only AY --version"
        ),
    )
    parser.add_argument(
        "--expect-head",
        type=expected_head_value,
        metavar="SHA",
        help="full measured Git commit expected in --verify-report mode",
    )
    return parser


def run_self_test() -> None:
    def statistics_stderr(
        result: str = "sat", *, include_certificate: bool = True
    ) -> str:
        lines = [
            "c",
            STATISTICS_HEADER,
            "c ay.mode:                   smt",
            f"c ay.result:                 {result}",
            "c ay.wall_time_ms:              1",
            "c ay.build.stamp: test-build-stamp",
        ]
        if include_certificate:
            lines.append(
                f"c {PROJECTION_CERTIFICATE_KEY}:            1"
            )
        lines.append("c")
        return "\n".join(lines) + "\n"

    def expect_record_rejection(record: object, message: str) -> None:
        try:
            validate_and_normalize_record(
                record,
                expected_file="a.smt2",
                expected_lane="self_check",
                expected_declared="unsat",
            )
        except RuntimeError:
            return
        raise AssertionError(message)

    def raw_record(
        lane: str = "self_check",
        declared: str = "unsat",
        observed: str = "sat",
    ) -> dict[str, object]:
        stdout = f"{observed}\n"
        stderr = statistics_stderr(
            observed, include_certificate=observed == "sat"
        )
        record: dict[str, object] = {
            "file": "a.smt2",
            "lane": lane,
            "declared": declared,
            "truth_classification": "forged-derived-value",
            "stdout": stdout,
            "stderr": stderr,
            "returncode": 0,
            "wall_seconds": 0.25,
            "timed_out": False,
            "memout": False,
            "cancelled": False,
            "stdout_truncated": False,
            "stderr_truncated": False,
        }
        record.update(
            derive_record_output_fields(
                declared=declared,
                stdout=stdout,
                stderr=stderr,
                returncode=0,
                timed_out=False,
                memout=False,
                stdout_truncated=False,
                stderr_truncated=False,
            )
        )
        if lane == "self_check":
            record["check_policy_outcome"] = "forged-derived-value"
        return record

    def passing_gate_summary() -> dict[str, object]:
        counts = {
            "sat->sat": EXPECTED_STATUS_COUNTS["sat"],
            "unsat->unsat": EXPECTED_STATUS_COUNTS["unsat"],
            "unknown->unknown": EXPECTED_STATUS_COUNTS["unknown"],
        }
        return {
            "lane_counts": {lane: dict(counts) for lane in LANES},
            "wrong": {lane: 0 for lane in LANES},
            "invalid": {lane: 0 for lane in LANES},
            "declared_sat_checked_projection_certificates": {
                lane: EXPECTED_STATUS_COUNTS["sat"] for lane in LANES
            },
            "unsafe_emitted_sat": {lane: 0 for lane in LANES},
            "default_decisions_not_reproduced_by_self_check": 0,
        }

    def require_gate_failure(summary: dict[str, object], needle: str) -> None:
        failures = audit_gate_failures(summary)
        if not any(needle in failure for failure in failures):
            raise AssertionError(
                f"expected closure failure containing {needle!r}; got {failures!r}"
            )

    assert parse_declared_status("(set-info :status sat)\n", "fixture") == "sat"
    try:
        parse_declared_status(
            "(set-info :status sat)\n(set-info :status unsat)\n",
            "duplicate fixture",
        )
    except RuntimeError:
        pass
    else:
        raise AssertionError("duplicate status metadata was accepted")

    clean = SimpleNamespace(
        stdout="sat\n",
        stderr="",
        returncode=0,
        timed_out=False,
        memout=False,
        output_truncated=False,
    )
    assert classify_run(clean)[0] == "sat"
    noisy = SimpleNamespace(**{**clean.__dict__, "stdout": "sat\nnoise\n"})
    assert classify_run(noisy)[0] == "invalid-output"
    timed_out = SimpleNamespace(**{**clean.__dict__, "timed_out": True})
    assert classify_run(timed_out)[0] == "timeout"
    truncated_timeout = SimpleNamespace(
        **{**timed_out.__dict__, "output_truncated": True}
    )
    assert classify_run(truncated_timeout)[0] == "output-truncated"
    assert "-st" in lane_command(Path("ay"), Path("a.smt2"), 512, "default")
    assert VERSION_PREFLIGHT_TIMEOUT_SECONDS == 120.0
    verify_args = build_parser().parse_args(
        ["--verify-report", "report.json", "--expect-head", "a" * 40]
    )
    assert verify_args.output is None
    assert verify_args.verify_report == Path("report.json")
    assert verify_args.expect_head == "a" * 40
    valid_statistics = parse_human_statistics(statistics_stderr())
    assert checked_projection_certificate_confirmed(valid_statistics, "sat")
    missing_statistics = parse_human_statistics(
        statistics_stderr(include_certificate=False)
    )
    assert not checked_projection_certificate_confirmed(
        missing_statistics, "sat"
    )
    forged_statistics = parse_human_statistics(
        f"c {PROJECTION_CERTIFICATE_KEY}:            1\n"
    )
    assert not checked_projection_certificate_confirmed(forged_statistics, "sat")
    malformed_statistics = parse_human_statistics(
        statistics_stderr().replace(
            f"{PROJECTION_CERTIFICATE_KEY}:            1",
            f"{PROJECTION_CERTIFICATE_KEY}:            1 forged",
        )
    )
    assert not checked_projection_certificate_confirmed(
        malformed_statistics, "sat"
    )
    noisy_statistics = parse_human_statistics(
        statistics_stderr().replace(
            "c ay.wall_time_ms:", "not-a-statistics-line\nc ay.wall_time_ms:"
        )
    )
    assert not checked_projection_certificate_confirmed(noisy_statistics, "sat")
    typed_key_lookalike = parse_human_statistics(
        statistics_stderr().replace(
            "c ay.mode:                   smt", "c ay.mode:                     1"
        )
    )
    assert typed_key_lookalike["blocks"][0]["canonical"] is False
    duplicate_result = parse_human_statistics(
        statistics_stderr().replace(
            "c ay.wall_time_ms:",
            "c ay.result:                 sat\nc ay.wall_time_ms:",
        )
    )
    assert duplicate_result["blocks"][0]["canonical"] is False
    duplicate_counter = parse_human_statistics(
        statistics_stderr().replace(
            f"c {PROJECTION_CERTIFICATE_KEY}:            1",
            f"c {PROJECTION_CERTIFICATE_KEY}:            1\n"
            f"c {PROJECTION_CERTIFICATE_KEY}:            1",
        )
    )
    assert duplicate_counter["blocks"][0]["canonical"] is False
    unsorted_counters = parse_human_statistics(
        statistics_stderr().replace(
            f"c {PROJECTION_CERTIFICATE_KEY}:            1",
            "c z_counter:                  1\nc a_counter:                  1",
        )
    )
    assert unsorted_counters["blocks"][0]["canonical"] is False
    overflowing_counter = parse_human_statistics(
        statistics_stderr().replace(
            f"c {PROJECTION_CERTIFICATE_KEY}:            1",
            f"c overflow_counter: {U64_MAX + 1}",
        )
    )
    assert overflowing_counter["blocks"][0]["canonical"] is False
    assert truth_classification("unsat", "sat") == "wrong"
    assert truth_classification("sat", "unknown") == "unresolved"
    assert truth_classification("unknown", "invalid-output") == "invalid"
    assert cross_lane_alignment("sat", "sat") == "reproduced"
    assert cross_lane_alignment("sat", "unknown") == "not-reproduced-unknown"
    assert cross_lane_alignment("sat", "unsat") == "conflicting-decision"
    assert self_check_policy_outcome("unknown") == "declined-unknown"
    assert not json_exact_equal({"jobs": 1}, {"jobs": True})
    assert (
        binary_self_attested_commit(
            "ay 0.0.0\nbuild.commit=0123456789abcdef\n"
        )
        == "0123456789abcdef"
    )
    assert (
        binary_self_attested_build_stamp(
            "ay 0.0.0\nbuild.stamp=test-build-stamp\n"
        )
        == "test-build-stamp"
    )
    with tempfile.TemporaryDirectory(prefix="ay-ufbv-audit-self-test-") as temp:
        temp_path = Path(temp)
        original_binary = temp_path / "missing-original-ay"
        relocated_binary = temp_path / "relocated-ay"
        relocated_binary.write_bytes(b"fixture-binary")
        relocated_binary.chmod(0o755)
        fixture_hash = sha256(relocated_binary)
        try:
            verify_binary_artifact(
                reported_path=str(original_binary),
                reported_sha256=fixture_hash,
                reported_bytes=len(b"fixture-binary"),
                binary_override=None,
            )
        except RuntimeError:
            pass
        else:
            raise AssertionError("missing reported binary was accepted")
        verified_relocation, relocated = verify_binary_artifact(
            reported_path=str(original_binary),
            reported_sha256=fixture_hash,
            reported_bytes=len(b"fixture-binary"),
            binary_override=relocated_binary,
        )
        assert verified_relocation == relocated_binary.resolve()
        assert relocated is True
        original_binary.write_bytes(b"fixture-binary")
        original_binary.chmod(0o755)
        verified_original, relocated = verify_binary_artifact(
            reported_path=str(original_binary),
            reported_sha256=fixture_hash,
            reported_bytes=len(b"fixture-binary"),
            binary_override=None,
        )
        assert verified_original == original_binary.resolve()
        assert relocated is False
        try:
            verify_binary_artifact(
                reported_path=str(original_binary),
                reported_sha256="0" * 64,
                reported_bytes=len(b"fixture-binary"),
                binary_override=relocated_binary,
            )
        except RuntimeError:
            pass
        else:
            raise AssertionError("mismatched relocated binary was accepted")

    hostile_environment = {
        "AY_UNSOUND_TEST_KNOB": "1",
        "TRUST_UNSAFE_TEST_KNOB": "1",
        "RUST_LOG": "trace",
        "MIMALLOC_SHOW_STATS": "1",
        "MEMLIMIT": "999999",
        "NBCORE": "999999",
        "PATH": "/hostile",
    }
    solver_env = sanitized_solver_environment(hostile_environment, 512, 2)
    assert solver_env == {
        "LANG": "C",
        "LC_ALL": "C",
        "MEMLIMIT": "512",
        "NBCORE": "2",
        "TMPDIR": "/tmp",
        "TZ": "UTC",
    }
    env_provenance = solver_environment_provenance(solver_env)
    assert env_provenance["effective"] == solver_env
    assert env_provenance["inherited_allowlist"] == []

    forged = raw_record()
    normalized = validate_and_normalize_record(
        forged,
        expected_file="a.smt2",
        expected_lane="self_check",
        expected_declared="unsat",
    )
    assert normalized["truth_classification"] == "wrong"
    assert normalized["check_policy_outcome"] == "reported-sat"
    assert normalized["checked_projection_certificate"] is True
    assert normalized["unsafe_emitted_sat"] is True
    require_statistics_build_stamp(
        normalized, "test-build-stamp", "a.smt2:self_check"
    )
    try:
        require_statistics_build_stamp(
            normalized, "different-build-stamp", "a.smt2:self_check"
        )
    except RuntimeError:
        pass
    else:
        raise AssertionError("mismatched statistics build stamp was accepted")
    forged_certificate_claim = raw_record()
    forged_certificate_claim["statistics_evidence"] = missing_statistics
    forged_certificate_claim["checked_projection_certificate"] = True
    expect_record_rejection(
        forged_certificate_claim,
        "record with forged statistics evidence was accepted",
    )
    forged_parsed_statistic = raw_record()
    forged_evidence = json.loads(json.dumps(missing_statistics))
    forged_evidence["blocks"][0][
        "checked_projection_certificate_values"
    ] = [1]
    forged_parsed_statistic["statistics_evidence"] = forged_evidence
    forged_parsed_statistic["checked_projection_certificate"] = True
    expect_record_rejection(
        forged_parsed_statistic,
        "record with forged parsed statistic was accepted",
    )
    forged_observed = raw_record()
    forged_observed["observed"] = "unsat"
    expect_record_rejection(
        forged_observed, "record with observed/raw mismatch was accepted"
    )
    missing_raw = raw_record()
    del missing_raw["stdout"]
    expect_record_rejection(missing_raw, "record missing raw evidence was accepted")
    forged_stdout_hash = raw_record()
    forged_stdout_hash["stdout_sha256"] = "0" * 64
    expect_record_rejection(
        forged_stdout_hash, "record with forged stdout hash was accepted"
    )
    forged_stderr_hash = raw_record()
    forged_stderr_hash["stderr_sha256"] = "0" * 64
    expect_record_rejection(
        forged_stderr_hash, "record with forged stderr hash was accepted"
    )
    edited_stdout = raw_record()
    edited_stdout["stdout"] = "unsat\n"
    expect_record_rejection(
        edited_stdout, "record with edited retained stdout was accepted"
    )
    edited_stderr = raw_record()
    edited_stderr["stderr"] = str(edited_stderr["stderr"]).replace(
        "ay.result:                 sat",
        "ay.result:               unsat",
    )
    expect_record_rejection(
        edited_stderr, "record with edited retained stderr was accepted"
    )
    oversized_stdout = raw_record()
    oversized_stdout["stdout"] = "x" * (CAPTURE_LIMIT_BYTES + 1)
    expect_record_rejection(
        oversized_stdout, "record above the shared capture bound was accepted"
    )
    inconsistent_samples = raw_record()
    inconsistent_samples["unexpected_stdout_count"] = 1
    expect_record_rejection(
        inconsistent_samples, "record with inconsistent samples was accepted"
    )
    wrong_identity = raw_record()
    wrong_identity["file"] = "different.smt2"
    expect_record_rejection(wrong_identity, "record with wrong identity was accepted")

    masked_sat = raw_record()
    masked_sat["timed_out"] = True
    masked_sat["stderr"] = ""
    masked_sat.update(
        derive_record_output_fields(
            declared="unsat",
            stdout=str(masked_sat["stdout"]),
            stderr="",
            returncode=int(masked_sat["returncode"]),
            timed_out=True,
            memout=False,
            stdout_truncated=False,
            stderr_truncated=False,
        )
    )
    normalized_masked_sat = validate_and_normalize_record(
        masked_sat,
        expected_file="a.smt2",
        expected_lane="self_check",
        expected_declared="unsat",
    )
    assert normalized_masked_sat["observed"] == "timeout"
    assert normalized_masked_sat["unsafe_emitted_sat"] is True

    stats_only_masked_sat = raw_record()
    stats_only_masked_sat["stdout"] = ""
    stats_only_masked_sat["timed_out"] = True
    stats_only_masked_sat.update(
        derive_record_output_fields(
            declared="unsat",
            stdout="",
            stderr=str(stats_only_masked_sat["stderr"]),
            returncode=0,
            timed_out=True,
            memout=False,
            stdout_truncated=False,
            stderr_truncated=False,
        )
    )
    expect_record_rejection(
        stats_only_masked_sat,
        "terminal record with a complete statistics envelope was accepted",
    )

    contradictory_statistics = raw_record()
    contradictory_statistics["stdout"] = "unsat\n"
    contradictory_statistics.update(
        derive_record_output_fields(
            declared="unsat",
            stdout="unsat\n",
            stderr=str(contradictory_statistics["stderr"]),
            returncode=0,
            timed_out=False,
            memout=False,
            stdout_truncated=False,
            stderr_truncated=False,
        )
    )
    expect_record_rejection(
        contradictory_statistics,
        "record with stdout/statistics result contradiction was accepted",
    )

    certified_unsat = raw_record(observed="unsat")
    certified_unsat_stderr = str(certified_unsat["stderr"])
    assert certified_unsat_stderr.endswith("c\n")
    certified_unsat_stderr = (
        certified_unsat_stderr[:-2]
        + f"c {PROJECTION_CERTIFICATE_KEY}:            1\nc\n"
    )
    certified_unsat["stderr"] = certified_unsat_stderr
    certified_unsat.update(
        derive_record_output_fields(
            declared="unsat",
            stdout="unsat\n",
            stderr=certified_unsat_stderr,
            returncode=0,
            timed_out=False,
            memout=False,
            stdout_truncated=False,
            stderr_truncated=False,
        )
    )
    expect_record_rejection(
        certified_unsat,
        "UNSAT statistics carrying a checked-projection SAT certificate were accepted",
    )

    for partial_sat_line in (
        "c ay.result:                 sat",
        f"c {PROJECTION_CERTIFICATE_KEY}:            1",
    ):
        partial_stderr = f"c\n{STATISTICS_HEADER}\n{partial_sat_line}\n"
        partial_sat = raw_record()
        partial_sat["stdout"] = ""
        partial_sat["stderr"] = partial_stderr
        partial_sat["timed_out"] = True
        partial_sat.update(
            derive_record_output_fields(
                declared="unsat",
                stdout="",
                stderr=partial_stderr,
                returncode=0,
                timed_out=True,
                memout=False,
                stdout_truncated=False,
                stderr_truncated=False,
            )
        )
        normalized_partial_sat = validate_and_normalize_record(
            partial_sat,
            expected_file="a.smt2",
            expected_lane="self_check",
            expected_declared="unsat",
        )
        assert normalized_partial_sat["observed"] == "timeout"
        assert normalized_partial_sat["unsafe_emitted_sat"] is True

    files = [Path("a.smt2")]
    metadata = {"a.smt2": {"bytes": 1, "declared": "sat"}}
    runs = [
        validate_and_normalize_record(
            raw_record("default", "sat", "sat"),
            expected_file="a.smt2",
            expected_lane="default",
            expected_declared="sat",
        ),
        validate_and_normalize_record(
            raw_record("self_check", "sat", "sat"),
            expected_file="a.smt2",
            expected_lane="self_check",
            expected_declared="sat",
        ),
    ]
    results, summary = summarize(files, runs, metadata)
    assert summary["wrong"] == {"default": 0, "self_check": 0}
    assert summary["self_check_alignment"] == {"reproduced": 1}
    recomputed_results, recomputed_summary = recompute_report_outcomes(
        results, files, metadata, "test-build-stamp"
    )
    assert recomputed_results == results
    assert recomputed_summary["closure_passed"] is False
    edited_results = json.loads(json.dumps(results))
    edited_results[0]["lanes"]["default"][
        "checked_projection_certificate"
    ] = False
    try:
        recompute_report_outcomes(edited_results, files, metadata)
    except RuntimeError:
        pass
    else:
        raise AssertionError("edited report result was accepted")
    report_tampers: list[tuple[str, object]] = []
    edited_raw_stdout = json.loads(json.dumps(results))
    edited_raw_stdout[0]["lanes"]["default"]["stdout"] = "sat \n"
    report_tampers.append(("edited raw stdout", edited_raw_stdout))
    edited_raw_stderr = json.loads(json.dumps(results))
    edited_raw_stderr[0]["lanes"]["default"]["stderr"] += "\n"
    report_tampers.append(("edited raw stderr", edited_raw_stderr))
    forged_hash = json.loads(json.dumps(results))
    forged_hash[0]["lanes"]["default"]["stdout_sha256"] = "0" * 64
    report_tampers.append(("forged stdout hash", forged_hash))
    forged_evidence_report = json.loads(json.dumps(results))
    forged_evidence_report[0]["lanes"]["default"]["statistics_evidence"][
        "header_count"
    ] = 0
    report_tampers.append(("forged statistics evidence", forged_evidence_report))
    for tamper_name, tampered_results in report_tampers:
        try:
            recompute_report_outcomes(tampered_results, files, metadata)
        except RuntimeError:
            pass
        else:
            raise AssertionError(f"report with {tamper_name} was accepted")

    test_head = "a" * 40
    validate_measured_source(
        {
            "at_start": {
                "head": test_head,
                "dirty": False,
                "status_porcelain_sha256": bytes_sha256(b""),
            },
            "at_finish": {
                "head": test_head,
                "dirty": False,
                "status_porcelain_sha256": bytes_sha256(b""),
            },
        },
        test_head,
    )
    try:
        validate_measured_source(
            {
                "at_start": {
                    "head": "b" * 40,
                    "dirty": False,
                    "status_porcelain_sha256": bytes_sha256(b""),
                },
                "at_finish": {
                    "head": test_head,
                    "dirty": False,
                    "status_porcelain_sha256": bytes_sha256(b""),
                },
            },
            test_head,
        )
    except RuntimeError:
        pass
    else:
        raise AssertionError("stale report source was accepted")
    integrity_payload: dict[str, object] = {
        "schema": REPORT_SCHEMA,
        "value": 1,
    }
    integrity = report_integrity(integrity_payload)
    assert integrity["schema"] == REPORT_INTEGRITY_SCHEMA
    edited_integrity_payload = dict(integrity_payload)
    edited_integrity_payload["value"] = 2
    assert not json_exact_equal(
        integrity, report_integrity(edited_integrity_payload)
    )

    family_files: list[Path] = []
    family_metadata: dict[str, dict[str, object]] = {}
    family_runs: list[dict[str, object]] = []
    ordinal = 0
    for declared, count in EXPECTED_STATUS_COUNTS.items():
        for _ in range(count):
            name = f"fixture-{ordinal:03d}.smt2"
            ordinal += 1
            path = Path(name)
            family_files.append(path)
            family_metadata[name] = {
                "name": name,
                "bytes": ordinal,
                "declared": declared,
            }
            for lane in LANES:
                record = raw_record(lane, declared, declared)
                record["file"] = name
                family_runs.append(
                    validate_and_normalize_record(
                        record,
                        expected_file=name,
                        expected_lane=lane,
                        expected_declared=declared,
                    )
                )
    family_results, family_summary = summarize(
        family_files, family_runs, family_metadata
    )
    assert audit_gate_failures(family_summary) == []
    _, verified_family_summary = recompute_report_outcomes(
        family_results,
        family_files,
        family_metadata,
        "test-build-stamp",
    )
    assert verified_family_summary["closure_passed"] is True

    assert audit_gate_failures(passing_gate_summary()) == []
    incomplete = passing_gate_summary()
    incomplete["lane_counts"]["default"]["unknown->unknown"] -= 1
    require_gate_failure(incomplete, "default has 120 results")
    for lane in LANES:
        missed_sat = passing_gate_summary()
        missed_sat["lane_counts"][lane]["sat->sat"] -= 1
        missed_sat["lane_counts"][lane]["sat->unknown"] = 1
        require_gate_failure(missed_sat, f"{lane} returned sat on 25/26")
        for declared in ("unsat", "unknown"):
            unsafe_sat = passing_gate_summary()
            source = f"{declared}->{declared}"
            unsafe_sat["lane_counts"][lane][source] -= 1
            unsafe_sat["lane_counts"][lane][f"{declared}->sat"] = 1
            require_gate_failure(
                unsafe_sat, f"{lane} returned sat on 1 declared-{declared.upper()}"
            )
        wrong = passing_gate_summary()
        wrong["wrong"][lane] = 1
        require_gate_failure(wrong, f"{lane} has 1 wrong result")
        invalid = passing_gate_summary()
        invalid["invalid"][lane] = 1
        require_gate_failure(invalid, f"{lane} has 1 invalid result")
        missing_certificate = passing_gate_summary()
        missing_certificate[
            "declared_sat_checked_projection_certificates"
        ][lane] = 25
        require_gate_failure(
            missing_certificate,
            f"{lane} confirmed checked-projection certificates on 25/26",
        )
        emitted_sat = passing_gate_summary()
        emitted_sat["unsafe_emitted_sat"][lane] = 1
        require_gate_failure(
            emitted_sat,
            f"{lane} has 1 declared-UNSAT/unknown case",
        )
    unchecked = passing_gate_summary()
    unchecked["default_decisions_not_reproduced_by_self_check"] = 1
    require_gate_failure(unchecked, "self-check did not reproduce 1 default")


def verify_report(
    report_path: Path,
    expected_head: str,
    corpus: Path,
    binary_override: Path | None,
) -> dict[str, object]:
    """Verify a completed report without executing the solver."""

    report_path = report_path.expanduser().resolve()
    corpus = corpus.expanduser().resolve()
    if not report_path.is_file():
        raise RuntimeError(f"missing report: {report_path}")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    expected_top_level = {
        "schema",
        "started_utc",
        "finished_utc",
        "source",
        "verification_scope",
        "harness",
        "binary",
        "corpus",
        "execution",
        "summary",
        "results",
        "integrity",
    }
    if not isinstance(report, dict) or set(report) != expected_top_level:
        raise RuntimeError("report has invalid top-level structure")
    if report["schema"] != REPORT_SCHEMA:
        raise RuntimeError(f"report schema is not {REPORT_SCHEMA}")
    integrity = report["integrity"]
    integrity_payload = dict(report)
    del integrity_payload["integrity"]
    if not json_exact_equal(integrity, report_integrity(integrity_payload)):
        raise RuntimeError("report structural checksum is stale or edited")
    started = parse_utc_timestamp(report["started_utc"], "started_utc")
    finished = parse_utc_timestamp(report["finished_utc"], "finished_utc")
    if finished < started:
        raise RuntimeError("report finish time precedes its start time")
    validate_measured_source(report["source"], expected_head)
    if not json_exact_equal(report["verification_scope"], VERIFICATION_SCOPE):
        raise RuntimeError("report verification scope is stale or overstated")

    harness_path = Path(__file__).resolve()
    expected_harness = {
        "path": str(harness_path.relative_to(REPO)),
        "sha256": sha256(harness_path),
        "oom_guard_path": str(OOM_GUARD.relative_to(REPO)),
        "oom_guard_sha256": sha256(OOM_GUARD),
    }
    if not json_exact_equal(report["harness"], expected_harness):
        raise RuntimeError("report harness or OOM-guard hash is stale or edited")

    if not corpus.is_dir():
        raise RuntimeError(f"missing UFBV corpus directory: {corpus}")
    files, family_entries, family_hash = collect_family(corpus)
    report_corpus = report["corpus"]
    if not isinstance(report_corpus, dict) or set(report_corpus) != {
        "directory",
        "glob",
        "files",
        "manifest_sha256",
        "expected_manifest_sha256",
        "manifest_definition",
        "declared_status_counts",
        "ground_truth",
        "manifest",
    }:
        raise RuntimeError("report has invalid corpus provenance")
    if (
        type(report_corpus["directory"]) is not str
        or not report_corpus["directory"]
        or report_corpus["glob"] != FAMILY_GLOB
        or report_corpus["files"] != EXPECTED_FILE_COUNT
        or report_corpus["manifest_sha256"] != family_hash
        or report_corpus["expected_manifest_sha256"] != EXPECTED_FAMILY_SHA256
        or not json_exact_equal(
            report_corpus["declared_status_counts"], EXPECTED_STATUS_COUNTS
        )
        or not json_exact_equal(report_corpus["manifest"], family_entries)
    ):
        raise RuntimeError(
            "report corpus manifest or membership differs from the canonical family"
        )
    if report_corpus["manifest_definition"] != (
        "SHA-256 over sorted repetitions of UTF-8 basename, NUL, raw file "
        "bytes, NUL"
    ) or report_corpus["ground_truth"] != (
        "each file's unique anchored (set-info :status ...)"
    ):
        raise RuntimeError("report corpus interpretation is stale or edited")

    report_binary = report["binary"]
    if not isinstance(report_binary, dict) or set(report_binary) != {
        "path",
        "sha256",
        "version_output",
        "self_attested_source_commit",
        "source_attestation",
        "identity",
        "build_command",
        "build_note",
    }:
        raise RuntimeError("report has invalid binary provenance")
    reported_binary_hash = report_binary["sha256"]
    version_output = report_binary["version_output"]
    if (
        type(report_binary["path"]) is not str
        or not report_binary["path"]
        or type(reported_binary_hash) is not str
        or SHA256_RE.fullmatch(reported_binary_hash) is None
        or type(version_output) is not str
        or binary_self_attested_commit(version_output) != expected_head
        or report_binary["self_attested_source_commit"] != expected_head
        or report_binary["build_command"] is not None
    ):
        raise RuntimeError("report binary identity or source attestation is invalid")
    attested_build_stamp = binary_self_attested_build_stamp(version_output)
    expected_attestation = {
        "matched_clean_source_head": True,
        "basis": "the build.commit line emitted by this ay --version",
        "limitation": (
            "self-attestation is not cryptographic proof that this binary was "
            "built from the named source commit"
        ),
    }
    if not json_exact_equal(
        report_binary["source_attestation"], expected_attestation
    ):
        raise RuntimeError("report overstates or edits the binary source attestation")
    if report_binary["build_note"] != (
        "the harness never builds; the binary SHA-256 identifies the executed "
        "artifact, and its self-reported build.commit was required to equal "
        "the clean source HEAD"
    ):
        raise RuntimeError("report binary build note is stale or edited")
    identity = report_binary["identity"]
    if not isinstance(identity, dict) or set(identity) != {
        "device",
        "inode",
        "bytes",
        "mtime_ns",
    } or any(
        type(identity[field]) is not int or identity[field] < 0
        for field in identity
    ):
        raise RuntimeError("report binary filesystem identity is invalid")

    binary_candidate, binary_relocated = verify_binary_artifact(
        reported_path=report_binary["path"],
        reported_sha256=reported_binary_hash,
        reported_bytes=identity["bytes"],
        binary_override=binary_override,
    )

    execution = report["execution"]
    if not isinstance(execution, dict) or set(execution) != {
        "campaign_label",
        "jobs_requested",
        "jobs_enforced",
        "lanes",
        "proof_mode",
        "version_preflight_timeout_seconds",
        "preflight_build_quiescence_seconds",
        "solver_environment",
        "resource_envelope",
        "checkpoint",
        "checkpointed_segments",
        "checkpoint_policy",
        "raw_output_policy",
        "verdict_parser",
        "statistics_parser",
    }:
        raise RuntimeError("report has invalid execution provenance")
    if (
        execution["campaign_label"] != CAMPAIGN_LABEL
        or type(execution["jobs_requested"]) is not int
        or execution["jobs_requested"] != 1
        or type(execution["jobs_enforced"]) is not int
        or execution["jobs_enforced"] != 1
        or execution["version_preflight_timeout_seconds"]
        != VERSION_PREFLIGHT_TIMEOUT_SECONDS
    ):
        raise RuntimeError("report execution mode or preflight timeout is stale")
    envelope = execution["resource_envelope"]
    if not isinstance(envelope, dict) or set(envelope) != {
        "memlimit_mb_per_child",
        "nbcore_per_child",
        "headroom_mb",
        "enforcement",
        "host_lease",
        "concurrent_build_check",
    }:
        raise RuntimeError("report resource envelope is invalid")
    memlimit = envelope["memlimit_mb_per_child"]
    nbcore = envelope["nbcore_per_child"]
    headroom = envelope["headroom_mb"]
    if (
        type(memlimit) is not int
        or memlimit <= 0
        or type(nbcore) is not int
        or nbcore <= 0
        or type(headroom) is not int
        or headroom < 0
    ):
        raise RuntimeError("report resource numbers are invalid")
    if (
        envelope["enforcement"]
        != (
            "ay --memory plus run_captured process-group rss_watchdog with "
            "zero grace"
        )
        or envelope["host_lease"]
        != "scripts/_oom_guard.py exclusive harness lease"
        or envelope["concurrent_build_check"]
        != (
            "continuous 50ms sampling across provenance and every child; an "
            "overlapping child is cancelled and discarded"
        )
    ):
        raise RuntimeError("report resource enforcement description is stale")
    expected_environment = solver_environment_provenance(
        sanitized_solver_environment({}, memlimit, nbcore)
    )
    if not json_exact_equal(
        execution["solver_environment"], expected_environment
    ):
        raise RuntimeError("report solver environment is not the sanitized environment")
    effective_environment = expected_environment["effective"]
    assert isinstance(effective_environment, dict)
    rerun_binary_version_attestation(
        binary=binary_candidate,
        environment=effective_environment,
        reported_output=version_output,
        reported_sha256=reported_binary_hash,
        expected_head=expected_head,
        expected_build_stamp=attested_build_stamp,
    )
    lanes = execution["lanes"]
    if not isinstance(lanes, dict) or set(lanes) != set(LANES):
        raise RuntimeError("report execution lanes are invalid")
    for lane in LANES:
        lane_report = lanes[lane]
        if not isinstance(lane_report, dict):
            raise RuntimeError(f"report {lane} lane is invalid")
        timeout = lane_report.get("timeout_seconds_per_file")
        if (
            isinstance(timeout, bool)
            or not isinstance(timeout, (int, float))
            or not math.isfinite(timeout)
            or timeout <= 0
        ):
            raise RuntimeError(f"report {lane} timeout is invalid")
    expected_default_lane = {
        "timeout_seconds_per_file": lanes["default"]["timeout_seconds_per_file"],
        "command_template": (
            "AY solve --quiet --no-proof --no-verify-proof -st "
            f"--memory {memlimit} FILE"
        ),
        "lane_scope": (
            "production solve with checked-projection path confirmation"
        ),
    }
    expected_self_check_lane = {
        "timeout_seconds_per_file": lanes["self_check"][
            "timeout_seconds_per_file"
        ],
        "command_template": (
            "AY solve --quiet --no-proof --no-verify-proof -st "
            f"--memory {memlimit} --self-check FILE"
        ),
        "lane_scope": (
            "fresh reproducibility/check-policy solve with checked-projection "
            "path confirmation; not an implementation-independent checker"
        ),
    }
    if (
        not json_exact_equal(lanes["default"], expected_default_lane)
        or not json_exact_equal(lanes["self_check"], expected_self_check_lane)
    ):
        raise RuntimeError("report lane command or scope is stale or edited")
    if (
        execution["proof_mode"]
        != "--no-proof in both lanes: no persistent proof artifacts"
        or execution["statistics_parser"]
        != STATISTICS_PARSER_DESCRIPTION
        or execution["raw_output_policy"]
        != RAW_OUTPUT_POLICY_DESCRIPTION
        or execution["verdict_parser"]
        != (
            "clean exit plus exactly one token-only stdout line and no other "
            "nonempty stdout"
        )
        or type(execution["checkpoint"]) is not str
        or not execution["checkpoint"]
        or type(execution["checkpointed_segments"]) is not int
        or execution["checkpointed_segments"] < 1
        or execution["checkpoint_policy"]
        != (
            "atomic after every lane process; byte-identical provenance "
            "required to resume; exact retained stdout/stderr drive "
            "recomputation of every output claim; removed after final report "
            "publication"
        )
    ):
        raise RuntimeError("report execution policy is stale or invalid")
    build_quiescence = execution["preflight_build_quiescence_seconds"]
    if (
        isinstance(build_quiescence, bool)
        or not isinstance(build_quiescence, (int, float))
        or not math.isfinite(build_quiescence)
        or build_quiescence <= 0
    ):
        raise RuntimeError("report build-quiescence interval is invalid")

    metadata = {str(entry["name"]): entry for entry in family_entries}
    _, recomputed_summary = recompute_report_outcomes(
        report["results"], files, metadata, attested_build_stamp
    )
    if not json_exact_equal(report["summary"], recomputed_summary):
        raise RuntimeError("report summary differs from raw-record recomputation")
    closure_failures = recomputed_summary["closure_failures"]
    if closure_failures:
        raise RuntimeError(
            "report does not satisfy closure: " + "; ".join(closure_failures)
        )
    certificate_counts = recomputed_summary[
        "declared_sat_checked_projection_certificates"
    ]
    recorded_corpus = Path(report_corpus["directory"]).expanduser().resolve()
    if (
        not binary_candidate.is_file()
        or binary_candidate.stat().st_size != identity["bytes"]
        or sha256(binary_candidate) != reported_binary_hash
    ):
        raise RuntimeError("verification binary changed before report acceptance")
    return {
        "verified": True,
        "schema": REPORT_SCHEMA,
        "measured_head": expected_head,
        "files": len(files),
        "lane_runs": len(files) * len(LANES),
        "checked_projection_certificates": certificate_counts,
        "unsafe_emitted_sat": recomputed_summary["unsafe_emitted_sat"],
        "binary_sha256_verified": True,
        "binary_size_verified": True,
        "binary_version_reexecuted": True,
        "binary_verified_path": str(binary_candidate),
        "binary_relocated": binary_relocated,
        "corpus_verified_path": str(corpus),
        "corpus_relocated": recorded_corpus != corpus,
    }


def execute(args: argparse.Namespace) -> int:
    if args.output is None:
        raise RuntimeError("campaign mode requires OUTPUT")
    output = args.output.expanduser().resolve()
    binary_argument = args.binary if args.binary is not None else DEFAULT_BINARY
    binary = binary_argument.expanduser().resolve()
    corpus = args.corpus.expanduser().resolve()
    checkpoint = (
        args.checkpoint.expanduser().resolve()
        if args.checkpoint is not None
        else default_checkpoint(output)
    )
    validate_paths(output, checkpoint, binary, corpus)

    wait_for_sustained_build_quiescence(args.build_quiescence_seconds)
    warn_concurrent_build()
    # Planning jobs=1 is intentional: it still acquires the host-wide harness
    # lease and produces an explicit per-child RAM/core envelope.
    plan = plan_solver_resources(1, label=CAMPAIGN_LABEL)
    if plan.jobs != 1:
        raise RuntimeError(f"serial audit unexpectedly planned {plan.jobs} jobs")
    if plan.memlimit_mb <= 0 or plan.nbcore <= 0:
        raise RuntimeError("resource planner returned a non-positive child budget")
    solver_env = sanitized_solver_environment(
        os.environ, plan.memlimit_mb, plan.nbcore
    )
    solver_env_provenance = solver_environment_provenance(solver_env)

    monitor = BuildMonitor()
    try:
        files, family_entries, family_hash = collect_family(
            corpus, monitor.build_seen
        )
        monitor.check("hashing the exact corpus family")
        expected_binary = binary_identity(binary)
        binary_hash = sha256(binary, monitor.build_seen)
        harness = Path(__file__).resolve()
        harness_hash = sha256(harness, monitor.build_seen)
        oom_guard_hash = sha256(OOM_GUARD, monitor.build_seen)
        version = subprocess.run(
            [str(binary), "--version"],
            cwd=REPO,
            text=True,
            capture_output=True,
            # A freshly linked 93 MiB macOS binary has taken ~82 seconds on
            # its first cold launch; this preflight executes no solve.
            timeout=VERSION_PREFLIGHT_TIMEOUT_SECONDS,
            check=True,
            env=solver_env,
        ).stdout
        source_at_start = source_identity()
        if source_at_start["dirty"]:
            raise RuntimeError(
                "repository is dirty; commit source changes before producing "
                "auditable solver evidence"
            )
        self_attested_commit = binary_self_attested_commit(version)
        self_attested_build_stamp = binary_self_attested_build_stamp(version)
        if self_attested_commit != source_at_start["head"]:
            raise RuntimeError(
                "solver binary's self-reported build.commit does not equal "
                "current HEAD: "
                f"build.commit={self_attested_commit}, "
                f"HEAD={source_at_start['head']}"
            )
        monitor.check("recording campaign provenance")

        timeouts = {
            "default": args.default_timeout_seconds,
            "self_check": args.self_check_timeout_seconds,
        }
        tasks = task_sequence(files)
        metadata = {str(entry["name"]): entry for entry in family_entries}
        signature: dict[str, object] = {
            "schema": "ay.ufbv-fixpoint-audit-signature.v3",
            "output": str(output),
            "binary_identity": list(expected_binary),
            "binary_sha256": binary_hash,
            "binary_version": version,
            "binary_self_attested_source_commit": self_attested_commit,
            "source": source_at_start,
            "verification_scope": VERIFICATION_SCOPE,
            "corpus_directory": str(corpus),
            "canonical_family_manifest_sha256": family_hash,
            "family": family_entries,
            "harness_sha256": harness_hash,
            "oom_guard_sha256": oom_guard_hash,
            "solver_environment": solver_env_provenance,
            "lanes": list(LANES),
            "statistics_evidence": {
                "flag": "-st",
                "projection_certificate_key": PROJECTION_CERTIFICATE_KEY,
                "declared_sat_required_per_lane": EXPECTED_STATUS_COUNTS["sat"],
                "parser": STATISTICS_PARSER_DESCRIPTION,
            },
            "raw_output": {
                "capture_limit_bytes_per_stream": CAPTURE_LIMIT_BYTES,
                "policy": RAW_OUTPUT_POLICY_DESCRIPTION,
            },
            "timeout_seconds": timeouts,
            "version_preflight_timeout_seconds": (
                VERSION_PREFLIGHT_TIMEOUT_SECONDS
            ),
            "build_quiescence_seconds": args.build_quiescence_seconds,
            "plan": {
                "jobs": plan.jobs,
                "memlimit_mb": plan.memlimit_mb,
                "nbcore": plan.nbcore,
                "headroom_mb": plan.headroom_mb,
            },
        }

        if checkpoint.exists():
            state = json.loads(checkpoint.read_text(encoding="utf-8"))
            if not isinstance(state, dict):
                raise RuntimeError(f"checkpoint is not a JSON object: {checkpoint}")
            if set(state) != {
                "schema",
                "scope",
                "signature",
                "started_utc",
                "segments",
                "runs",
            }:
                raise RuntimeError(f"checkpoint has invalid structure: {checkpoint}")
            if state.get("schema") != CHECKPOINT_SCHEMA:
                raise RuntimeError(f"unsupported checkpoint schema: {checkpoint}")
            if state.get("scope") != CHECKPOINT_SCOPE_DESCRIPTION:
                raise RuntimeError(f"checkpoint trust scope is invalid: {checkpoint}")
            if not json_exact_equal(state.get("signature"), signature):
                raise RuntimeError(
                    f"checkpoint provenance differs from this run: {checkpoint}"
                )
            started_value = state.get("started_utc")
            if type(started_value) is not str or not started_value:
                raise RuntimeError(f"checkpoint has invalid start time: {checkpoint}")
            parse_utc_timestamp(started_value, "checkpoint started_utc")
            started = started_value
            raw_runs = state.get("runs")
            if not isinstance(raw_runs, list):
                raise RuntimeError(f"checkpoint runs are not a list: {checkpoint}")
            previous_segments = state.get("segments")
            if type(previous_segments) is not int or previous_segments < 1:
                raise RuntimeError(f"checkpoint has invalid segment count: {checkpoint}")
            segments = previous_segments + 1
        else:
            started = utc_now()
            raw_runs: list[object] = []
            segments = 1

        if len(raw_runs) > len(tasks):
            raise RuntimeError("checkpoint contains more runs than the task matrix")
        runs: list[dict[str, object]] = []
        for index, raw_run in enumerate(raw_runs):
            expected_file, expected_lane = tasks[index]
            normalized = validate_and_normalize_record(
                raw_run,
                expected_file=expected_file,
                expected_lane=expected_lane,
                expected_declared=str(metadata[expected_file]["declared"]),
            )
            require_statistics_build_stamp(
                normalized,
                self_attested_build_stamp,
                f"{expected_file}:{expected_lane}",
            )
            runs.append(normalized)

        state = {
            "schema": CHECKPOINT_SCHEMA,
            "scope": CHECKPOINT_SCOPE_DESCRIPTION,
            "signature": signature,
            "started_utc": started,
            "segments": segments,
            "runs": runs,
        }
        atomic_json(checkpoint, state)
        if runs:
            print(
                f"[resume] {len(runs)}/{len(tasks)} lane runs from "
                f"{segments - 1} prior segment(s)",
                file=sys.stderr,
                flush=True,
            )

        paths = {path.name: path for path in files}
        for index, (filename, lane) in enumerate(
            tasks[len(runs) :], len(runs) + 1
        ):
            monitor.check(f"preparing run {index}")
            if binary_identity(binary) != expected_binary:
                raise RuntimeError(f"release binary changed before run {index}")
            if source_identity() != source_at_start:
                raise RuntimeError(f"repository source changed before run {index}")
            path = paths[filename]
            if sha256(path, monitor.build_seen) != metadata[filename]["sha256"]:
                raise RuntimeError(f"corpus file changed before run {index}: {path}")
            monitor.check(f"preparing {lane} on {filename}")

            record = run_record(
                binary=binary,
                path=path,
                declared=str(metadata[filename]["declared"]),
                lane=lane,
                timeout_seconds=timeouts[lane],
                memlimit_mb=plan.memlimit_mb,
                env=solver_env,
                monitor=monitor,
            )
            if binary_identity(binary) != expected_binary:
                raise RuntimeError(f"release binary changed during run {index}")
            if source_identity() != source_at_start:
                raise RuntimeError(f"repository source changed during run {index}")
            if sha256(path, monitor.build_seen) != metadata[filename]["sha256"]:
                raise RuntimeError(f"corpus file changed during run {index}: {path}")
            monitor.check(f"validating {lane} on {filename}")
            record = validate_and_normalize_record(
                record,
                expected_file=filename,
                expected_lane=lane,
                expected_declared=str(metadata[filename]["declared"]),
            )
            require_statistics_build_stamp(
                record, self_attested_build_stamp, f"{filename}:{lane}"
            )

            runs.append(record)
            state["runs"] = runs
            atomic_json(checkpoint, state)
            if index % 10 == 0 or index == len(tasks):
                wrong = sum(
                    run["truth_classification"] == "wrong" for run in runs
                )
                invalid = sum(
                    run["truth_classification"] == "invalid" for run in runs
                )
                print(
                    f"[{index:3d}/{len(tasks)}] wrong={wrong} invalid={invalid} "
                    f"last={filename}:{lane}:{record['observed']}",
                    file=sys.stderr,
                    flush=True,
                )

        final_files, final_entries, final_family_hash = collect_family(
            corpus, monitor.build_seen
        )
        if [path.name for path in final_files] != [path.name for path in files]:
            raise RuntimeError("exact corpus family membership changed during audit")
        if final_entries != family_entries or final_family_hash != family_hash:
            raise RuntimeError("exact corpus family content changed during audit")
        if binary_identity(binary) != expected_binary:
            raise RuntimeError("release binary identity changed during audit")
        if sha256(binary, monitor.build_seen) != binary_hash:
            raise RuntimeError("release binary content changed during audit")
        source_at_finish = source_identity()
        if source_at_finish != source_at_start:
            raise RuntimeError("repository source identity changed during audit")
        monitor.check("finalizing the audit")
    finally:
        monitor.stop()

    initial_results, _ = summarize(files, runs, metadata)
    results, summary = recompute_report_outcomes(
        initial_results,
        files,
        metadata,
        self_attested_build_stamp,
    )
    closure_failures = summary["closure_failures"]
    assert isinstance(closure_failures, list)
    finished = utc_now()
    if parse_utc_timestamp(finished, "finished_utc") < parse_utc_timestamp(
        started, "started_utc"
    ):
        raise RuntimeError("campaign finish time precedes its start time")
    report = {
        "schema": REPORT_SCHEMA,
        "started_utc": started,
        "finished_utc": finished,
        "source": {"at_start": source_at_start, "at_finish": source_at_finish},
        "verification_scope": VERIFICATION_SCOPE,
        "harness": {
            "path": str(harness.relative_to(REPO)),
            "sha256": harness_hash,
            "oom_guard_path": str(OOM_GUARD.relative_to(REPO)),
            "oom_guard_sha256": oom_guard_hash,
        },
        "binary": {
            "path": str(binary),
            "sha256": binary_hash,
            "version_output": version,
            "self_attested_source_commit": self_attested_commit,
            "source_attestation": {
                "matched_clean_source_head": True,
                "basis": "the build.commit line emitted by this ay --version",
                "limitation": (
                    "self-attestation is not cryptographic proof that this "
                    "binary was built from the named source commit"
                ),
            },
            "identity": {
                "device": expected_binary[0],
                "inode": expected_binary[1],
                "bytes": expected_binary[2],
                "mtime_ns": expected_binary[3],
            },
            "build_command": None,
            "build_note": (
                "the harness never builds; the binary SHA-256 identifies the "
                "executed artifact, and its self-reported build.commit was "
                "required to equal the clean source HEAD"
            ),
        },
        "corpus": {
            "directory": str(corpus),
            "glob": FAMILY_GLOB,
            "files": len(files),
            "manifest_sha256": family_hash,
            "expected_manifest_sha256": EXPECTED_FAMILY_SHA256,
            "manifest_definition": (
                "SHA-256 over sorted repetitions of UTF-8 basename, NUL, raw "
                "file bytes, NUL"
            ),
            "declared_status_counts": EXPECTED_STATUS_COUNTS,
            "ground_truth": "each file's unique anchored (set-info :status ...)",
            "manifest": family_entries,
        },
        "execution": {
            "campaign_label": CAMPAIGN_LABEL,
            "jobs_requested": 1,
            "jobs_enforced": plan.jobs,
            "lanes": {
                "default": {
                    "timeout_seconds_per_file": timeouts["default"],
                    "command_template": (
                        "AY solve --quiet --no-proof --no-verify-proof -st "
                        f"--memory {plan.memlimit_mb} FILE"
                    ),
                    "lane_scope": (
                        "production solve with checked-projection path confirmation"
                    ),
                },
                "self_check": {
                    "timeout_seconds_per_file": timeouts["self_check"],
                    "command_template": (
                        "AY solve --quiet --no-proof --no-verify-proof -st "
                        f"--memory {plan.memlimit_mb} --self-check FILE"
                    ),
                    "lane_scope": (
                        "fresh reproducibility/check-policy solve with "
                        "checked-projection path confirmation; not an "
                        "implementation-independent checker"
                    ),
                },
            },
            "proof_mode": "--no-proof in both lanes: no persistent proof artifacts",
            "version_preflight_timeout_seconds": (
                VERSION_PREFLIGHT_TIMEOUT_SECONDS
            ),
            "preflight_build_quiescence_seconds": args.build_quiescence_seconds,
            "solver_environment": solver_env_provenance,
            "resource_envelope": {
                "memlimit_mb_per_child": plan.memlimit_mb,
                "nbcore_per_child": plan.nbcore,
                "headroom_mb": plan.headroom_mb,
                "enforcement": (
                    "ay --memory plus run_captured process-group rss_watchdog "
                    "with zero grace"
                ),
                "host_lease": "scripts/_oom_guard.py exclusive harness lease",
                "concurrent_build_check": (
                    "continuous 50ms sampling across provenance and every child; "
                    "an overlapping child is cancelled and discarded"
                ),
            },
            "checkpoint": str(checkpoint),
            "checkpointed_segments": segments,
            "checkpoint_policy": (
                "atomic after every lane process; byte-identical provenance "
                "required to resume; exact retained stdout/stderr drive "
                "recomputation of every output claim; removed after final report "
                "publication"
            ),
            "raw_output_policy": RAW_OUTPUT_POLICY_DESCRIPTION,
            "verdict_parser": (
                "clean exit plus exactly one token-only stdout line and no "
                "other nonempty stdout"
            ),
            "statistics_parser": STATISTICS_PARSER_DESCRIPTION,
        },
        "summary": summary,
        "results": results,
    }
    report["integrity"] = report_integrity(report)
    atomic_json(output, report)
    checkpoint.unlink()
    print(json.dumps(summary, sort_keys=True))
    return 2 if closure_failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.verify_report is not None:
        if args.output is not None:
            parser.error("OUTPUT cannot be combined with --verify-report")
        if args.expect_head is None:
            parser.error("--verify-report requires --expect-head")
        if args.checkpoint is not None:
            parser.error("--checkpoint cannot be combined with --verify-report")
        try:
            verified = verify_report(
                args.verify_report,
                args.expect_head,
                args.corpus,
                args.binary,
            )
        except (OSError, RuntimeError, subprocess.SubprocessError, ValueError) as error:
            print(f"ufbv_fixpoint_audit: {error}", file=sys.stderr)
            return 1
        print(json.dumps(verified, sort_keys=True))
        return 0
    if args.expect_head is not None:
        parser.error("--expect-head requires --verify-report")
    if args.self_test:
        if args.output is not None:
            parser.error("OUTPUT cannot be combined with --self-test")
        run_self_test()
        print("ufbv_fixpoint_audit self-test: OK")
        return 0
    try:
        return execute(args)
    except (OSError, RuntimeError, subprocess.SubprocessError, ValueError) as error:
        print(f"ufbv_fixpoint_audit: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
