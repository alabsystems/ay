# ay-script: nra-oracle-shards-tests
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Unit tests for the bounded NRA oracle shard harness."""

import hashlib
import io
import json
import sys
import tempfile
import types
import unittest
from contextlib import redirect_stderr
from pathlib import Path
from unittest import mock


SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))

import nra_oracle_shards as shards  # noqa: E402
import nra_oracle_campaign as campaign  # noqa: E402
import nra_oracle_shards_lib as shard_lib  # noqa: E402


def captured(**overrides):
    fields = {
        "stdout": "",
        "stderr": "",
        "returncode": 0,
        "timed_out": False,
        "memout": False,
        "cancelled": False,
        "wall_sec": 0.25,
        "stdout_truncated": False,
        "stderr_truncated": False,
        "output_truncated": False,
    }
    fields.update(overrides)
    if fields["stdout_truncated"] or fields["stderr_truncated"]:
        fields["output_truncated"] = True
    return types.SimpleNamespace(**fields)


class ShardConstructionTest(unittest.TestCase):
    def test_ranges_are_contiguous_and_final_shard_is_short(self):
        ranges = list(shard_lib.iter_shards(11, 10, 4))
        self.assertEqual(
            [(item.ordinal, item.start, item.cases, item.end) for item in ranges],
            [(0, 11, 4, 15), (1, 15, 4, 19), (2, 19, 2, 21)],
        )

    def test_command_matches_current_oracle_parser(self):
        args = types.SimpleNamespace(seed=7, progress=0, max_cost=420)
        shard = shard_lib.Shard(2, 4000, 2000)
        command = campaign.shard_command(
            args,
            Path("/oracle"),
            Path("/trusted/libz3.so"),
            shard,
            Path("/out/divergences"),
        )
        self.assertEqual(
            command,
            [
                "/oracle",
                "fuzz",
                "--z3",
                "/trusted/libz3.so",
                "--seed",
                "7",
                "--start",
                "4000",
                "--cases",
                "2000",
                "--progress",
                "0",
                "--max-cost",
                "420",
                "--dump",
                "/out/divergences",
            ],
        )

    def test_parse_rejects_a_range_past_u64(self):
        with self.assertRaises(SystemExit):
            shards.parse_args(
                [
                    "--binary",
                    "/oracle",
                    "--z3",
                    "/libz3.so",
                    "--out-dir",
                    "/out",
                    "--start",
                    str(shards.U64_MAX),
                    "--cases",
                    "2",
                ]
            )

    def test_parse_rejects_more_than_the_persisted_shard_cap(self):
        with self.assertRaises(SystemExit):
            shards.parse_args(
                [
                    "--binary",
                    "/oracle",
                    "--z3",
                    "/libz3.so",
                    "--out-dir",
                    "/out",
                    "--cases",
                    str(shards.MAX_SHARDS + 1),
                    "--shard-cases",
                    "1",
                ]
            )


class ClassificationTest(unittest.TestCase):
    def test_timeout_memout_cancel_and_bad_rc_are_abandoned(self):
        cases = (
            (captured(timed_out=True, returncode=-9), "timeout"),
            (captured(memout=True, returncode=-9), "memout"),
            (captured(cancelled=True, returncode=-9), "cancelled"),
            (captured(returncode=2), "nonaccepted-returncode-2"),
            (captured(stdout_truncated=True), "output-truncated"),
        )
        for result, reason in cases:
            with self.subTest(reason=reason):
                record = shards.captured_record(
                    "fuzz",
                    ["oracle", "fuzz"],
                    result,
                    shard_lib.ACCEPTED_FUZZ_RETURN_CODES,
                )
                self.assertTrue(record["abandoned"])
                self.assertEqual(record["status"], "abandoned")
                self.assertEqual(record["abandon_reason"], reason)

    def test_fuzz_rc_one_is_a_completed_divergence(self):
        record = shards.captured_record(
            "fuzz",
            ["oracle", "fuzz"],
            captured(returncode=1),
            shard_lib.ACCEPTED_FUZZ_RETURN_CODES,
        )
        self.assertFalse(record["abandoned"])
        self.assertEqual(record["oracle_outcome"], "divergences")


class ResourceExecutionTest(unittest.TestCase):
    def setUp(self):
        self.plan = types.SimpleNamespace(
            jobs=2, memlimit_mb=777, nbcore=3, headroom_mb=16000
        )

    def test_probe_uses_guarded_capture_and_extracts_loaded_z3_version(self):
        result = captured(stdout="reference libz3: /trusted/libz3.so (4.13.4.0)\n")
        environment = {"MEMLIMIT": "777", "NBCORE": "3"}
        with mock.patch.object(shards, "run_captured", return_value=result) as run:
            record, version = shards.run_probe(
                Path("/oracle"),
                Path("/trusted/libz3.so"),
                self.plan,
                12.5,
                environment,
            )
        self.assertEqual(version, "4.13.4.0")
        self.assertFalse(record["abandoned"])
        run.assert_called_once_with(
            ["/oracle", "probe", "--z3", "/trusted/libz3.so"],
            777,
            12.5,
            label="nra_oracle_shards.py[probe]",
            env=environment,
        )

    def test_run_shard_persists_guard_outcome_and_exact_plan(self):
        args = types.SimpleNamespace(seed=9, progress=0, max_cost=420, timeout=15.0)
        environment = {"MEMLIMIT": "777", "NBCORE": "3"}
        envelope = {"memlimit_mb_per_child": 777, "nbcore_per_child": 3}
        shard = shard_lib.Shard(0, 100, 50)
        result = captured(stdout="full persisted output", timed_out=True, returncode=-9)
        with (
            tempfile.TemporaryDirectory() as directory,
            mock.patch.object(campaign, "run_captured", return_value=result) as run,
        ):
            record = campaign.run_shard(
                args,
                Path("/oracle"),
                Path("/libz3.so"),
                Path(directory),
                shard,
                self.plan,
                environment,
                envelope,
                campaign.CampaignControl(),
            )
            persisted = json.loads(
                next(Path(directory).glob("shard-*.json")).read_text()
            )
        self.assertTrue(record["abandoned"])
        self.assertEqual(persisted["abandon_reason"], "timeout")
        self.assertEqual(persisted["shard"]["end_exclusive"], 150)
        self.assertEqual(persisted["resource_envelope"], envelope)
        self.assertEqual(persisted["stdout"], "full persisted output")
        self.assertNotIn("stdout", record)
        self.assertNotIn("stderr", record)
        self.assertEqual(record["result_json"], "shard-000000-100-150.json")
        self.assertEqual(run.call_args.args[1:3], (777, 15.0))
        self.assertEqual(run.call_args.kwargs["env"], environment)

    def test_campaign_pending_futures_are_capped_at_admitted_jobs(self):
        args = types.SimpleNamespace(
            start=0,
            cases=5,
            shard_cases=1,
            seed=1,
            progress=0,
            max_cost=420,
            timeout=10.0,
        )
        observed_pending = []
        executors = []

        class FakeFuture:
            def __init__(self, shard):
                self.shard = shard

            def result(self):
                return {
                    "status": "completed",
                    "abandoned": False,
                    "abandon_reason": None,
                    "oracle_outcome": "clean",
                    "shard": {
                        "ordinal": self.shard.ordinal,
                        "start": self.shard.start,
                        "cases": self.shard.cases,
                        "end_exclusive": self.shard.end,
                    },
                }

        class FakeExecutor:
            def __init__(self, max_workers):
                self.max_workers = max_workers
                self.submissions = 0
                executors.append(self)

            def __enter__(self):
                return self

            def __exit__(self, *_exc):
                return False

            def submit(self, _function, *call_args):
                self.submissions += 1
                return FakeFuture(call_args[4])

        def fake_wait(pending, **_kwargs):
            observed_pending.append(len(pending))
            return {next(iter(pending))}, set()

        with (
            tempfile.TemporaryDirectory() as directory,
            mock.patch.object(campaign, "ThreadPoolExecutor", FakeExecutor),
            mock.patch.object(campaign, "wait", side_effect=fake_wait),
        ):
            records = campaign.run_campaign(
                args,
                Path("/oracle"),
                Path("/libz3.so"),
                Path(directory),
                self.plan,
                {},
                {},
                campaign.CampaignControl(),
            )
        self.assertEqual(len(records), 5)
        self.assertEqual(executors[0].max_workers, 2)
        self.assertEqual(executors[0].submissions, 5)
        self.assertLessEqual(max(observed_pending), 2)


class MainPersistenceTest(unittest.TestCase):
    def test_main_plans_once_and_persists_complete_envelope(self):
        plan = types.SimpleNamespace(
            jobs=1, memlimit_mb=888, nbcore=4, headroom_mb=12000
        )
        probe = {
            "status": "completed",
            "abandoned": False,
            "abandon_reason": None,
        }
        record = {
            "status": "completed",
            "abandoned": False,
            "abandon_reason": None,
            "oracle_outcome": "clean",
            "shard": {
                "ordinal": 0,
                "start": 0,
                "cases": 10,
                "end_exclusive": 10,
            },
        }
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / "ay-nra-oracle"
            binary.write_bytes(b"oracle-binary")
            binary.chmod(0o755)
            z3_path = root / "libz3.so"
            z3_path.write_bytes(b"trusted-z3")
            output = root / "campaign"
            argv = [
                "--binary",
                str(binary),
                "--z3",
                str(z3_path),
                "--out-dir",
                str(output),
                "--cases",
                "10",
                "--jobs",
                "5",
                "--timeout",
                "30",
                "--mem-floor-mb",
                "2048",
            ]
            with (
                mock.patch.object(shards, "warn_concurrent_build") as warn,
                mock.patch.object(
                    shards, "plan_solver_resources", return_value=plan
                ) as planner,
                mock.patch.object(
                    shards, "run_probe", return_value=(probe, "4.13.4.0")
                ),
                mock.patch.object(shards, "run_campaign", return_value=[record]),
                mock.patch.object(shards, "install_cancel_handlers", return_value={}),
            ):
                self.assertEqual(shards.main(argv), 0)
            envelope = json.loads((output / "resource-envelope.json").read_text())
            results = json.loads((output / "results.json").read_text())
        warn.assert_called_once_with()
        planner.assert_called_once_with(
            1, mem_floor_mb=2048, label="nra_oracle_shards.py"
        )
        self.assertEqual(envelope["requested_jobs"], 5)
        self.assertEqual(envelope["user_requested_jobs"], 5)
        self.assertEqual(envelope["effective_planner_jobs"], 1)
        self.assertEqual(envelope["admitted_jobs"], 1)
        self.assertEqual(envelope["planned_shards"], 1)
        self.assertEqual(envelope["max_shards"], shards.MAX_SHARDS)
        self.assertEqual(envelope["max_in_flight_children"], shards.MAX_IN_FLIGHT)
        self.assertEqual(envelope["memlimit_mb_per_child"], 888)
        self.assertEqual(envelope["nbcore_per_child"], 4)
        self.assertEqual(envelope["headroom_mb"], 12000)
        self.assertEqual(envelope["timeout_seconds_per_child"], 30.0)
        self.assertEqual(
            envelope["capture_limit_bytes_per_stream"],
            shards.CAPTURE_LIMIT_BYTES,
        )
        self.assertEqual(
            envelope["max_in_flight_capture_bytes"],
            2 * shards.CAPTURE_LIMIT_BYTES,
        )
        self.assertEqual(envelope["trusted_z3_version"], "4.13.4.0")
        self.assertEqual(
            envelope["oracle_binary_sha256"],
            hashlib.sha256(b"oracle-binary").hexdigest(),
        )
        self.assertEqual(results["summary"]["completed_cases"], 10)
        self.assertNotIn("stdout", results["results"][0])

    def test_main_handles_resource_refusal_without_a_traceback(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / "ay-nra-oracle"
            binary.write_bytes(b"oracle-binary")
            binary.chmod(0o755)
            z3_path = root / "libz3.so"
            z3_path.write_bytes(b"trusted-z3")
            argv = [
                "--binary",
                str(binary),
                "--z3",
                str(z3_path),
                "--out-dir",
                str(root / "campaign"),
                "--cases",
                "10",
            ]
            stderr = io.StringIO()
            with (
                mock.patch.object(
                    shards,
                    "warn_concurrent_build",
                    side_effect=RuntimeError("busy"),
                ),
                mock.patch.object(shards, "plan_solver_resources") as planner,
                redirect_stderr(stderr),
            ):
                self.assertEqual(shards.main(argv), 2)
        planner.assert_not_called()
        self.assertIn("resource admission failed: busy", stderr.getvalue())
        self.assertNotIn("Traceback", stderr.getvalue())

    def test_main_handles_planner_failure_without_a_traceback(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / "ay-nra-oracle"
            binary.write_bytes(b"oracle-binary")
            binary.chmod(0o755)
            z3_path = root / "libz3.so"
            z3_path.write_bytes(b"trusted-z3")
            argv = [
                "--binary",
                str(binary),
                "--z3",
                str(z3_path),
                "--out-dir",
                str(root / "campaign"),
                "--cases",
                "10",
            ]
            stderr = io.StringIO()
            with (
                mock.patch.object(shards, "warn_concurrent_build"),
                mock.patch.object(
                    shards,
                    "plan_solver_resources",
                    side_effect=RuntimeError("no safe memory plan"),
                ),
                redirect_stderr(stderr),
            ):
                self.assertEqual(shards.main(argv), 2)
        self.assertIn(
            "resource admission failed: no safe memory plan", stderr.getvalue()
        )
        self.assertNotIn("Traceback", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
