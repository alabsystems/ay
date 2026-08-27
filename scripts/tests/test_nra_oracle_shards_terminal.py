# ay-script: nra-oracle-shards-terminal-tests
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Terminal-summary and campaign-abort tests for NRA oracle sharding."""

import json
import sys
import tempfile
import threading
import types
import unittest
from pathlib import Path
from unittest import mock


SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))

import nra_oracle_campaign as campaign  # noqa: E402
import nra_oracle_shards as shards  # noqa: E402
import nra_oracle_shards_lib as shard_lib  # noqa: E402


def terminal_summary(cases=10, asserts=20, comparisons=15, failures=0, divergences=0):
    return (
        "=== ay-nra-oracle: differential run ===\n"
        f"cases executed       {cases}\n"
        f"differential asserts {asserts}\n"
        f"reference comparisons {comparisons}\n"
        f"reference failures   {failures}\n"
        f"DIVERGENCES          {divergences}\n"
    )


def captured(stdout="", returncode=0, **overrides):
    fields = {
        "stdout": stdout,
        "stderr": "",
        "returncode": returncode,
        "timed_out": False,
        "memout": False,
        "cancelled": False,
        "wall_sec": 0.25,
        "stdout_truncated": False,
        "stderr_truncated": False,
        "output_truncated": False,
    }
    fields.update(overrides)
    return types.SimpleNamespace(**fields)


def campaign_args(cases=3, jobs=1):
    return types.SimpleNamespace(
        start=0,
        cases=cases,
        shard_cases=1,
        seed=1,
        progress=0,
        max_cost=420,
        timeout=10.0,
        jobs=jobs,
        mem_floor_mb=1,
    )


class TerminalSummaryTest(unittest.TestCase):
    def test_clean_and_divergence_summaries_are_valid(self):
        clean = shard_lib.parse_oracle_summary(terminal_summary(), 10, 0)
        divergence = shard_lib.parse_oracle_summary(
            terminal_summary(divergences=2), 10, 1
        )
        self.assertTrue(clean["valid"], clean)
        self.assertTrue(divergence["valid"], divergence)
        self.assertEqual(clean["counts"]["cases_executed"], 10)
        self.assertEqual(divergence["counts"]["divergences"], 2)

    def test_invalid_summary_rejection_matrix(self):
        valid = terminal_summary()
        fields = {
            "cases": "cases executed       10\n",
            "asserts": "differential asserts 20\n",
            "comparisons": "reference comparisons 15\n",
            "failures": "reference failures   0\n",
            "divergences": "DIVERGENCES          0\n",
        }
        cases = {
            "wrong-cases": terminal_summary(cases=9),
            "zero-asserts": terminal_summary(asserts=0),
            "zero-reference-comparisons": terminal_summary(comparisons=0),
            "reference-failure": terminal_summary(failures=1),
            "rc0-with-divergence": terminal_summary(divergences=1),
        }
        for name, line in fields.items():
            cases[f"missing-{name}"] = valid.replace(line, "")
            cases[f"duplicate-{name}"] = valid + line
        for name, stdout in cases.items():
            with self.subTest(name=name):
                parsed = shard_lib.parse_oracle_summary(stdout, 10, 0)
                self.assertFalse(parsed["valid"], parsed)
                self.assertTrue(parsed["errors"])
        parsed = shard_lib.parse_oracle_summary(terminal_summary(), 10, 1)
        self.assertFalse(parsed["valid"], parsed)

    def test_run_shard_persists_validated_counts(self):
        args = campaign_args(cases=10)
        args.shard_cases = 10
        plan = types.SimpleNamespace(memlimit_mb=777, jobs=1)
        shard = shard_lib.Shard(0, 100, 10)
        with (
            tempfile.TemporaryDirectory() as directory,
            mock.patch.object(
                campaign,
                "run_captured",
                return_value=captured(terminal_summary(cases=10)),
            ),
        ):
            index = campaign.run_shard(
                args,
                Path("/oracle"),
                Path("/libz3.so"),
                Path(directory),
                shard,
                plan,
                {"MEMLIMIT": "777", "NBCORE": "1"},
                {},
                campaign.CampaignControl(),
            )
            full = json.loads(
                (Path(directory) / "shard-000000-100-110.json").read_text()
            )
        self.assertFalse(index["abandoned"])
        self.assertEqual(index["oracle_counts"]["differential_asserts"], 20)
        self.assertTrue(full["oracle_summary"]["valid"])
        self.assertEqual(full["oracle_counts"]["reference_comparisons"], 15)

    def test_invalid_summary_abandons_the_whole_shard(self):
        args = campaign_args(cases=10)
        args.shard_cases = 10
        plan = types.SimpleNamespace(memlimit_mb=777, jobs=1)
        shard = shard_lib.Shard(0, 200, 10)
        invalid = terminal_summary(cases=9)
        with (
            tempfile.TemporaryDirectory() as directory,
            mock.patch.object(campaign, "run_captured", return_value=captured(invalid)),
        ):
            index = campaign.run_shard(
                args,
                Path("/oracle"),
                Path("/libz3.so"),
                Path(directory),
                shard,
                plan,
                {},
                {},
                campaign.CampaignControl(),
            )
            full = json.loads(
                (Path(directory) / "shard-000000-200-210.json").read_text()
            )
        self.assertTrue(index["abandoned"])
        self.assertEqual(index["abandon_reason"], "invalid-oracle-summary")
        self.assertNotIn("oracle_outcome", index)
        self.assertFalse(full["oracle_summary"]["valid"])

    def test_aggregate_totals_include_only_accepted_shards(self):
        clean = {
            "abandoned": False,
            "oracle_outcome": "clean",
            "oracle_counts": {
                "cases_executed": 10,
                "differential_asserts": 20,
                "reference_comparisons": 15,
                "reference_failures": 0,
                "divergences": 0,
            },
            "shard": {"cases": 10},
        }
        divergent = {
            "abandoned": False,
            "oracle_outcome": "divergences",
            "oracle_counts": {
                "cases_executed": 5,
                "differential_asserts": 8,
                "reference_comparisons": 7,
                "reference_failures": 0,
                "divergences": 2,
            },
            "shard": {"cases": 5},
        }
        abandoned = {
            "abandoned": True,
            "abandon_reason": "invalid-oracle-summary",
            "oracle_counts": {key: 999 for key in shard_lib.ORACLE_COUNT_KEYS},
            "shard": {"cases": 3},
        }
        summary = shard_lib.summarize([clean, divergent, abandoned])
        self.assertEqual(summary["oracle_totals"]["cases_executed"], 15)
        self.assertEqual(summary["oracle_totals"]["differential_asserts"], 28)
        self.assertEqual(summary["oracle_totals"]["reference_comparisons"], 22)
        self.assertEqual(summary["oracle_totals"]["reference_failures"], 0)
        self.assertEqual(summary["oracle_totals"]["divergences"], 2)


class HarnessAbortTest(unittest.TestCase):
    def test_run_captured_exception_stops_refill_and_cancels_peer(self):
        args = campaign_args(cases=4, jobs=2)
        plan = types.SimpleNamespace(memlimit_mb=777, jobs=2)
        barrier = threading.Barrier(2)

        def run_side_effect(_command, _memory, _timeout, **kwargs):
            barrier.wait(timeout=2)
            if kwargs["label"].endswith("shard-0]"):
                raise RuntimeError("capture failed")
            self.assertTrue(kwargs["cancel_event"].wait(timeout=2))
            return captured(returncode=-9, cancelled=True)

        control = campaign.CampaignControl()
        with (
            tempfile.TemporaryDirectory() as directory,
            mock.patch.object(
                campaign, "run_captured", side_effect=run_side_effect
            ) as run,
        ):
            records = campaign.run_campaign(
                args,
                Path("/oracle"),
                Path("/libz3.so"),
                Path(directory),
                plan,
                {},
                {},
                control,
            )
            persisted = list(Path(directory).glob("shard-*.json"))
        self.assertTrue(control.harness_aborted.is_set())
        self.assertEqual(run.call_count, 2)
        self.assertEqual(len(records), 4)
        self.assertEqual(len(persisted), 4)
        self.assertTrue(all(record["abandoned"] for record in records))
        self.assertIn("run_captured", {row["source"] for row in control.abort_events()})

    def test_future_exception_is_a_campaign_abort_without_refill(self):
        args = campaign_args(cases=3)
        plan = types.SimpleNamespace(memlimit_mb=777, jobs=1)
        control = campaign.CampaignControl()
        with (
            tempfile.TemporaryDirectory() as directory,
            mock.patch.object(
                campaign, "run_shard", side_effect=RuntimeError("future failed")
            ) as run,
        ):
            records = campaign.run_campaign(
                args,
                Path("/oracle"),
                Path("/libz3.so"),
                Path(directory),
                plan,
                {},
                {},
                control,
            )
        self.assertEqual(run.call_count, 1)
        self.assertEqual(len(records), 3)
        self.assertTrue(control.harness_aborted.is_set())
        self.assertIn("future", {row["source"] for row in control.abort_events()})

    def test_persistence_exception_is_a_campaign_abort_without_refill(self):
        args = campaign_args(cases=3)
        plan = types.SimpleNamespace(memlimit_mb=777, jobs=1)
        control = campaign.CampaignControl()
        with (
            tempfile.TemporaryDirectory() as directory,
            mock.patch.object(
                campaign,
                "run_captured",
                return_value=captured(terminal_summary(cases=1)),
            ) as run,
            mock.patch.object(
                campaign, "atomic_write_json", side_effect=OSError("disk full")
            ),
        ):
            records = campaign.run_campaign(
                args,
                Path("/oracle"),
                Path("/libz3.so"),
                Path(directory),
                plan,
                {},
                {},
                control,
            )
        self.assertEqual(run.call_count, 1)
        self.assertEqual(len(records), 3)
        self.assertTrue(control.harness_aborted.is_set())
        self.assertTrue(any(not record["persisted"] for record in records))
        self.assertIn("persistence", {row["source"] for row in control.abort_events()})


class PlannerClampTest(unittest.TestCase):
    def test_low_floor_high_jobs_is_clamped_before_the_sole_plan(self):
        args = campaign_args(cases=100, jobs=100_000)
        plan = types.SimpleNamespace(
            jobs=shard_lib.MAX_IN_FLIGHT,
            memlimit_mb=1,
            nbcore=1,
            headroom_mb=0,
        )
        with (
            mock.patch.object(shards, "warn_concurrent_build"),
            mock.patch.object(
                shards, "plan_solver_resources", return_value=plan
            ) as planner,
        ):
            admitted, effective = shards.admit_resources(args)
        self.assertIs(admitted, plan)
        self.assertEqual(effective, shard_lib.MAX_IN_FLIGHT)
        planner.assert_called_once_with(
            shard_lib.MAX_IN_FLIGHT,
            mem_floor_mb=1,
            label="nra_oracle_shards.py",
        )


class MainTerminationTest(unittest.TestCase):
    def run_main(self, termination):
        plan = types.SimpleNamespace(
            jobs=1, memlimit_mb=777, nbcore=1, headroom_mb=16000
        )
        probe = {
            "status": "completed",
            "abandoned": False,
            "abandon_reason": None,
            "cancelled": False,
        }
        record = {
            "status": "abandoned",
            "abandoned": True,
            "abandon_reason": termination,
            "shard": {
                "ordinal": 0,
                "start": 0,
                "cases": 1,
                "end_exclusive": 1,
            },
        }

        def terminate_campaign(*call_args):
            control = call_args[-1]
            if termination == "harness-abort":
                control.request_harness_abort("future", "boom")
            else:
                control.request_user_cancel()
            return [record]

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / "ay-nra-oracle"
            binary.write_bytes(b"oracle")
            binary.chmod(0o755)
            z3_path = root / "libz3.so"
            z3_path.write_bytes(b"z3")
            output = root / "out"
            argv = [
                "--binary",
                str(binary),
                "--z3",
                str(z3_path),
                "--out-dir",
                str(output),
                "--cases",
                "1",
            ]
            with (
                mock.patch.object(shards, "warn_concurrent_build"),
                mock.patch.object(shards, "plan_solver_resources", return_value=plan),
                mock.patch.object(
                    shards, "run_probe", return_value=(probe, "4.13.4.0")
                ),
                mock.patch.object(
                    shards, "run_campaign", side_effect=terminate_campaign
                ),
                mock.patch.object(shards, "install_cancel_handlers", return_value={}),
            ):
                returncode = shards.main(argv)
            payload = json.loads((output / "results.json").read_text())
        return returncode, payload

    def test_harness_abort_returns_two(self):
        returncode, payload = self.run_main("harness-abort")
        self.assertEqual(returncode, 2)
        self.assertEqual(payload["termination"]["kind"], "harness-abort")

    def test_user_signal_is_the_only_130_path(self):
        returncode, payload = self.run_main("user-signal")
        self.assertEqual(returncode, 130)
        self.assertEqual(payload["termination"]["kind"], "user-signal")


if __name__ == "__main__":
    unittest.main()
