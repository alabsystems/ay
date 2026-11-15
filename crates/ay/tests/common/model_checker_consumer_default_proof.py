# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""One source-bound R24 CLI request; no compiler or solver runs at import time.

Admission is out-of-band scheduling. After admission, one absolute 30-second
deadline owns input admission, materialization, binary hashing, CLI launch,
default proof production, complete capture and authenticated group cleanup.
The shared guard's post-resume timeout is only a second backstop: a timer tied
to the original deadline cancels it, and final admission checks that SAME owner.
The 4 GiB RSS sampler is a backstop, not an instantaneous allocation bound.
This is not independent certificate replay or whole-consumer acceptance.
This helper owns the campaign lease: do not nest it inside run_guarded.py or
another lease-owning harness. Invoke it directly (or through its Rust test).
"""
import dataclasses
import hashlib
import json
import os
from pathlib import Path
import resource
import sys
import tempfile
import threading
import time

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts"))
import _oom_guard as guard
from model_checker_consumer_libtest_evidence import guarded_success, require

SOURCE_BYTES = 18809
SOURCE_SHA256 = "340e1289b1d92921da4498e9ac82a39c1ff38c1a5eb34c812a0427c67b3f41e8"
REQUEST_SECONDS = 30.0
MEMORY_MIB = 4096
FILE_LIMIT_BYTES = 16 * 1024 * 1024
LABEL = "model-checker-consumer-r24-original-default-proof"


class OriginalOwner:
    """A single absolute deadline; rejection is sticky, including zero work."""

    def __init__(self, clock=time.monotonic):
        self.clock = clock
        self.started = clock()
        self.deadline = self.started + REQUEST_SECONDS
        self.cancel = threading.Event()

    def remaining(self):
        left = self.deadline - self.clock()
        if left <= 0:
            self.cancel.set()
        require(not self.cancel.is_set(), "original 30-second request owner stopped")
        return left


def source_bytes(path):
    with path.open("rb") as source:
        body = source.read(SOURCE_BYTES + 1)
    require(len(body) == SOURCE_BYTES and hashlib.sha256(body).hexdigest() == SOURCE_SHA256,
            "original R24 fixture identity mismatch")
    return body


def executable_identity(metadata):
    return dict(device=metadata.st_dev, inode=metadata.st_ino, size=metadata.st_size,
                mtime_ns=metadata.st_mtime_ns, ctime_ns=metadata.st_ctime_ns)


def require_binary_identity(binary, expected, owner):
    owner.remaining()
    try:
        observed = executable_identity(binary.stat())
    except OSError as error:
        raise RuntimeError("CLI executable identity unavailable") from error
    require(observed == expected, "CLI executable replaced or changed after hashing")
    owner.remaining()


def binary_identity(binary, owner):
    digest = hashlib.sha256()
    with binary.open("rb") as source:
        before = os.fstat(source.fileno())
        while True:
            owner.remaining()
            chunk = source.read(1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
        after = os.fstat(source.fileno())
    require(executable_identity(before) == executable_identity(after),
            "CLI binary changed during provenance capture")
    return digest.hexdigest(), executable_identity(before)


def require_default_unsat(result, proof_bytes):
    guarded_success(result, MEMORY_MIB)
    require("\ufffd" not in result.stdout + result.stderr, "lossy UTF-8 capture refused")
    require(result.stdout.endswith("\n") and result.stdout.split() == ["unsat"],
            "original R24 requires exactly UNSAT, never Unknown or a partial response")
    rows = [line for line in result.stderr.splitlines()
            if line.startswith("c ay.proof.certificate ")]
    require(len(rows) == 1, "missing/ambiguous same-run default proof disclosure")
    admissions = [word for word in rows[0].split() if word.startswith("unsat_admission=")]
    require(admissions in (["unsat_admission=strict-proof"],
                           ["unsat_admission=checked-bool-bv"]),
            "UNSAT must retain checked admission, not merely a rendered certificate")
    require(0 < proof_bytes <= FILE_LIMIT_BYTES, "missing or oversized default proof artifact")


def captured_receipt(result):
    receipt = dataclasses.asdict(result)
    # Both bounded streams are emitted separately, without truncation here.
    receipt.pop("stdout")
    receipt.pop("stderr")
    return receipt


def run_request(binary, fixture):
    owner = OriginalOwner()
    timer = threading.Timer(owner.remaining(), owner.cancel.set)
    timer.daemon = True
    timer.start()
    watch = guard.MemoryPressureWatch(label=LABEL, on_critical=owner.cancel.set)
    try:
        identity, executable = binary_identity(binary, owner)
        body = source_bytes(fixture)
        with watch, tempfile.TemporaryDirectory(prefix="ay-r24-default-proof-") as directory:
            query = Path(directory) / "query.smt2"
            query.write_bytes(body)
            require_binary_identity(binary, executable, owner)
            left = owner.remaining()
            # Only resource options: the ordinary default proof/rigor/file route
            # remains intact. No --no-proof, --chc, --self-check or rigor override.
            command = [str(binary), "--timeout", str(max(1, int(left * 1000))),
                       "--memory", str(MEMORY_MIB), str(query)]
            result = guard.run_captured(
                command, MEMORY_MIB, left, label=LABEL, cwd=ROOT,
                env=dict(os.environ, CI="1"), cancel_event=owner.cancel,
            )
            # These streams are capped and completely drained by run_captured.
            # Keep failure diagnostics visible without an unbounded second pipe.
            print(result.stdout, end="", flush=True)
            print(result.stderr, end="", file=sys.stderr, flush=True)
            # Preserve complete returned guard evidence even for Unknown,
            # missing artifacts, late completion or a refused verdict/receipt.
            # This record is explicitly NOT the accepted single-row report.
            print(json.dumps(dict(stage="captured-not-accepted", binary_sha256=identity,
                                  binary_file_identity=executable,
                                  source_sha256=SOURCE_SHA256, source_bytes=len(body),
                                  argv=command, receipt=captured_receipt(result))), flush=True)
            require_binary_identity(binary, executable, owner)
            try:
                proof_bytes = query.with_suffix(".smt2.alethe").stat().st_size
            except FileNotFoundError:
                proof_bytes = 0
            require_default_unsat(result, proof_bytes)
    finally:
        timer.cancel()
        timer.join()
    # Includes mandatory guard, pipe, watch, temporary file and timer cleanup.
    owner.remaining()
    require(not watch.tripped, "memory pressure refused this request")
    return dict(stage="accepted-single-row", binary_sha256=identity, source_sha256=SOURCE_SHA256,
                binary_file_identity=executable,
                source_bytes=len(body), argv=command, receipt=captured_receipt(result),
                request_budget_seconds=REQUEST_SECONDS,
                request_wall_seconds=owner.clock() - owner.started,
                proof_bytes=proof_bytes, portable_proof_replay="not run",
                qualification="one original default-proof BMC row only")


def main():
    require(len(sys.argv) == 3, "usage: helper AY_BINARY ORIGINAL_FIXTURE")
    binary, fixture = map(Path, sys.argv[1:])
    # Bound default proof disk growth in the child without changing its route.
    # The helper inherits the same cap; its diagnostic output is bounded too.
    soft, hard = resource.getrlimit(resource.RLIMIT_FSIZE)
    cap = min([FILE_LIMIT_BYTES] + [value for value in (soft, hard)
                                  if value != resource.RLIM_INFINITY])
    resource.setrlimit(resource.RLIMIT_FSIZE, (cap, hard))
    admission_started = time.monotonic()
    try:
        plan, admission = guard.admit_campaign(1, label=LABEL, mem_floor_mb=MEMORY_MIB)
        admission_seconds = time.monotonic() - admission_started
        require(plan.jobs == 1 and plan.memlimit_mb >= MEMORY_MIB, "insufficient resource plan")
        print(json.dumps(dict(admission=admission, plan=plan._asdict(),
                              admission_wall_seconds=admission_seconds,
                              enforced_rss_mib=MEMORY_MIB,
                              enforced_file_limit_bytes=cap)), flush=True)
        report = run_request(binary, fixture)
    finally:
        guard._release_harness_lease()
    print(json.dumps(report), flush=True)


if __name__ == "__main__":
    main()
