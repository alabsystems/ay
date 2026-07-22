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


@unittest.skipUnless(os.path.exists("/usr/bin/true"), "needs /usr/bin/true")
class ChcEnvelopeRecordingTest(unittest.TestCase):
    """Campaign records identify the enforced per-child memory envelope."""

    def test_track_sweep_record_carries_memlimit(self):
        task = types.SimpleNamespace(
            smt2=os.devnull, verdict=None, rel_id="fam/x.smt2"
        )
        rec = chccomp_track_sweep.run_one(
            task, 5, "/usr/bin/true", memlimit_mb=777
        )
        self.assertEqual(rec["memlimit_mb"], 777)
        self.assertEqual(rec["status"], "unknown")

    def test_track_sweep_record_zero_means_solver_default(self):
        task = types.SimpleNamespace(
            smt2=os.devnull, verdict=None, rel_id="fam/x.smt2"
        )
        rec = chccomp_track_sweep.run_one(task, 5, "/usr/bin/true")
        self.assertEqual(rec["memlimit_mb"], 0)

    def test_regression_record_carries_memlimit(self):
        entry = {
            "year": "2025",
            "track": "LIA-Lin",
            "instance": "i.yml",
            "verdict": "sat",
            "wall": 1.0,
        }
        with mock.patch.object(
            chccomp_regression, "resolve_smt2", return_value=os.devnull
        ):
            rec = chccomp_regression.run(
                entry, 1, "/usr/bin/true", memlimit_mb=777
            )
        self.assertEqual(rec["memlimit_mb"], 777)
        self.assertEqual(rec["status"], "unknown")


if __name__ == "__main__":
    unittest.main()
