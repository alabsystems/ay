# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

"""Pure/mocked controls: no compiler, solver, memory admission or child launch."""
from contextlib import nullcontext
import copy
import dataclasses
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    "model_checker_consumer_default_proof", Path(__file__).with_name("model_checker_consumer_default_proof.py"))
helper = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(helper)
FIXTURE = Path(__file__).parents[1] / "group_soundness/fixtures/model_checker_consumer_bmc_walker_original.smt2"


def receipt():
    return helper.guard.CapturedRun(
        stdout="unsat\n", stderr="c ay.proof.certificate path=q.alethe unsat_admission=strict-proof\n",
        returncode=0, timed_out=False, memout=False, wall_sec=1,
        stdout_truncated=False, stderr_truncated=False, cancelled=False,
        guard_evidence=dict(
            phase="reaped", group_identity=[42, "start"], identity_lost=False,
            identity_lost_time_ns=None, peak_rss_mib=110, kill_threshold_mib=4096,
            poll_seconds=0.02, breached=False, breach_time_ns=None, worker_error=None,
            events=[dict(kind=kind) for kind in
                    ("authenticated-resume", "monitor-joined", "group-reaped")]))


class SourceAndOwnerTests(unittest.TestCase):
    def test_exact_original_bytes_are_present(self):
        self.assertEqual(len(helper.source_bytes(FIXTURE)), 18809)

    def test_same_size_corruption_and_append_refuse(self):
        original = helper.source_bytes(FIXTURE)
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "query.smt2"
            for body in (b"X" + original[1:], original + b"\n"):
                target.write_bytes(body)
                with self.assertRaisesRegex(RuntimeError, "fixture identity"):
                    helper.source_bytes(target)

    def test_original_deadline_is_not_renewed_and_refusal_is_sticky(self):
        now = [10.0]
        owner = helper.OriginalOwner(clock=lambda: now[0])
        now[0] = 39.0
        self.assertEqual(owner.remaining(), 1.0)
        now[0] = 40.0
        with self.assertRaises(RuntimeError):
            owner.remaining()
        now[0] = 10.0
        with self.assertRaises(RuntimeError):
            owner.remaining()

    def test_pressure_or_original_timer_cancellation_cannot_resume(self):
        owner = helper.OriginalOwner(clock=lambda: 0)
        owner.cancel.set()
        with self.assertRaises(RuntimeError):
            owner.remaining()

    def test_same_bytes_atomic_executable_replacement_refuses(self):
        owner = helper.OriginalOwner(clock=lambda: 0)
        with tempfile.TemporaryDirectory() as directory:
            binary = Path(directory) / "ay"
            replacement = Path(directory) / "new-ay"
            binary.write_bytes(b"same-test-only-executable-bytes")
            _, identity = helper.binary_identity(binary, owner)
            helper.require_binary_identity(binary, identity, owner)
            replacement.write_bytes(binary.read_bytes())
            replacement.replace(binary)
            with self.assertRaisesRegex(RuntimeError, "replaced or changed"):
                helper.require_binary_identity(binary, identity, owner)


class VerdictTests(unittest.TestCase):
    def test_checked_unsat_with_default_artifact_passes_without_portability_claim(self):
        helper.require_default_unsat(receipt(), 100)
        value = dataclasses.replace(receipt(), stderr=(
            "c ay.proof.certificate path=q.alethe trust_free=no carcara_surface=unsupported "
            "unsat_admission=checked-bool-bv\n"))
        helper.require_default_unsat(value, 100)

    def test_unknown_wrong_duplicate_or_partial_verdict_refuses(self):
        for stdout in ("unknown\n", "sat\n", "unsat", "unsat\nunsat\n", "unsat\n(error x)\n",
                       "unsat\n\ufffd"):
            with self.subTest(stdout=stdout), self.assertRaises(RuntimeError):
                helper.require_default_unsat(dataclasses.replace(receipt(), stdout=stdout), 100)

    def test_weakened_or_absent_proof_admission_and_artifact_refuse(self):
        for stderr in ("", "c ay.proof.certificate unsat_admission=none-recorded\n",
                       receipt().stderr * 2):
            with self.subTest(stderr=stderr), self.assertRaises(RuntimeError):
                helper.require_default_unsat(dataclasses.replace(receipt(), stderr=stderr), 100)
        for size in (0, helper.FILE_LIMIT_BYTES + 1):
            with self.subTest(size=size), self.assertRaises(RuntimeError):
                helper.require_default_unsat(receipt(), size)

    def test_truncated_capture_resource_stop_and_unreaped_group_refuse(self):
        for field, value in (("stdout_truncated", True), ("stderr_truncated", True),
                             ("timed_out", True), ("memout", True), ("cancelled", True),
                             ("returncode", 1)):
            with self.subTest(field=field), self.assertRaises(RuntimeError):
                helper.require_default_unsat(dataclasses.replace(receipt(), **{field: value}), 100)
        for field, value in (("phase", "active"), ("identity_lost", True),
                             ("events", []), ("worker_error", "lost monitor")):
            evidence = copy.deepcopy(receipt().guard_evidence)
            evidence[field] = value
            with self.subTest(field=field), self.assertRaises(RuntimeError):
                helper.require_default_unsat(dataclasses.replace(receipt(), guard_evidence=evidence), 100)


class RouteTests(unittest.TestCase):
    def run_fake(self, late, verdict="unsat", artifact=True, replaced=False):
        now = [0.0]
        owner = helper.OriginalOwner(clock=lambda: now[0])
        calls = []

        def identity(_binary, _owner):
            now[0] = 29.0
            return "test-only-binary", dict(device=1, inode=2, size=3, mtime_ns=4, ctime_ns=5)

        def identity_check(_binary, _expected, _owner):
            owner.remaining()
            if replaced and calls:
                raise RuntimeError("CLI executable replaced or changed after hashing")

        def capture(command, memory, seconds, **kwargs):
            self.assertIs(kwargs["cancel_event"], owner.cancel)
            self.assertEqual((memory, seconds), (4096, 1.0))
            self.assertEqual(command[1:-1], ["--timeout", "1000", "--memory", "4096"])
            query = Path(command[-1])
            self.assertEqual(query.read_bytes(), helper.source_bytes(FIXTURE))
            if artifact:
                query.with_suffix(".smt2.alethe").write_bytes(b"test-only-artifact")
            calls.append(command)
            now[0] = 31.0 if late else 29.5
            return dataclasses.replace(receipt(), stdout=verdict + "\n")

        with patch.object(helper, "OriginalOwner", return_value=owner), \
                patch.object(helper, "binary_identity", side_effect=identity), \
                patch.object(helper, "require_binary_identity", side_effect=identity_check), \
                patch.object(helper.guard, "run_captured", side_effect=capture), \
                patch.object(helper.guard, "MemoryPressureWatch",
                             return_value=nullcontext()), \
                patch.object(helper.threading, "Timer"), \
                patch("builtins.print") as printed:
            # nullcontext has no runtime state; explicitly model the one queried
            # pressure fact instead of starting the real monitor in a unit test.
            watch = helper.guard.MemoryPressureWatch.return_value
            watch.tripped = False
            try:
                result = helper.run_request(Path("/test-only-ay"), FIXTURE)
            finally:
                records = [json.loads(call.args[0]) for call in printed.call_args_list
                           if call.args[0].startswith("{")]
                self.assertEqual(len(records), 1)
                self.assertEqual(records[0]["stage"], "captured-not-accepted")
                self.assertEqual(records[0]["binary_sha256"], "test-only-binary")
                self.assertEqual(records[0]["binary_file_identity"]["inode"], 2)
                self.assertEqual(records[0]["source_sha256"], helper.SOURCE_SHA256)
                self.assertEqual(records[0]["receipt"], helper.captured_receipt(receipt()))
        self.assertEqual(len(calls), 1)
        return result

    def test_exact_default_route_spends_remaining_original_credit(self):
        report = self.run_fake(late=False)
        self.assertEqual(report["request_wall_seconds"], 29.5)
        self.assertEqual(report["portable_proof_replay"], "not run")

    def test_late_unsat_does_not_get_fresh_credit_or_pass(self):
        with self.assertRaisesRegex(RuntimeError, "original 30-second"):
            self.run_fake(late=True)

    def test_unknown_keeps_captured_receipt_before_refusal(self):
        with self.assertRaisesRegex(RuntimeError, "requires exactly UNSAT"):
            self.run_fake(late=False, verdict="unknown", artifact=False)

    def test_missing_default_artifact_keeps_receipt_and_intended_rejection(self):
        with self.assertRaisesRegex(RuntimeError, "missing or oversized default proof"):
            self.run_fake(late=False, artifact=False)

    def test_post_capture_executable_replacement_keeps_receipt_and_refuses(self):
        with self.assertRaisesRegex(RuntimeError, "replaced or changed"):
            self.run_fake(late=False, replaced=True)


if __name__ == "__main__":
    unittest.main()
