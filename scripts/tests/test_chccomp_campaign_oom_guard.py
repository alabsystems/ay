# ay-script: chccomp-campaign-oom-guard-tests
"""Resource-envelope checks for the CHC campaign scripts."""

import os
import sys
import types
import unittest
from pathlib import Path
from unittest import mock

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS_DIR))

import chccomp_regression  # noqa: E402
import chccomp_track_sweep  # noqa: E402


class ChcEnvelopeRecordingTest(unittest.TestCase):
    """Campaign records identify the enforced per-child memory envelope."""

    def test_track_sweep_record_carries_memlimit(self):
        task = types.SimpleNamespace(
            smt2=os.devnull, verdict=None, rel_id="fam/x.smt2"
        )
        captured = types.SimpleNamespace(
            returncode=0,
            stdout="",
            memout=False,
            timed_out=False,
            output_truncated=False,
        )
        with mock.patch.object(
            chccomp_track_sweep, "run_captured", return_value=captured
        ):
            rec = chccomp_track_sweep.run_one(
                task, 5, "fake-ay", memlimit_mb=777
            )
        self.assertEqual(rec["memlimit_mb"], 777)
        self.assertEqual(rec["status"], "unknown")

    def test_track_sweep_rejects_unenforced_resource_budgets(self):
        task = types.SimpleNamespace(
            smt2=os.devnull, verdict=None, rel_id="fam/x.smt2"
        )
        for kwargs in (
            {},
            {"memlimit_mb": 0, "nbcore": 1},
            {"memlimit_mb": 777, "nbcore": 0},
        ):
            with self.subTest(kwargs=kwargs):
                with self.assertRaisesRegex(
                    ValueError,
                    "track sweep requires positive memory and core budgets",
                ):
                    chccomp_track_sweep.run_one(
                        task, 5, "fake-ay", **kwargs
                    )

    def test_regression_record_carries_memlimit(self):
        entry = {
            "year": "2025",
            "track": "LIA-Lin",
            "instance": "i.yml",
            "verdict": "sat",
            "wall": 1.0,
        }
        captured = types.SimpleNamespace(
            returncode=0,
            stdout="",
            stderr="",
            memout=False,
            timed_out=False,
            cancelled=False,
            output_truncated=False,
            wall_sec=0.0,
        )
        with (
            mock.patch.object(
                chccomp_regression, "resolve_smt2", return_value=os.devnull
            ),
            mock.patch.object(
                chccomp_regression, "run_captured", return_value=captured
            ),
        ):
            rec = chccomp_regression.run(
                entry, 1, "fake-ay", memlimit_mb=777
            )
        self.assertEqual(rec["memlimit_mb"], 777)
        self.assertEqual(rec["status"], "unknown")


if __name__ == "__main__":
    unittest.main()
