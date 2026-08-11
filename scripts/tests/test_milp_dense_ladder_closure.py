# ay-script: dense-ladder-closure-tests
"""Pure stdlib tests for the dense-ladder AY/Gurobi closure gate."""

import math
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS_DIR))

import milp_dense_ladder_closure as dense  # noqa: E402


class Plan:
    memlimit_mb = 4096


def point_check(objective="273"):
    return {
        "process_wall_sec": 0.1,
        "returncode": 0,
        "timed_out": False,
        "memout": False,
        "cancelled": False,
        "stdout_truncated": False,
        "stderr_truncated": False,
        "output_truncated": False,
        "parsed": {
            "status": "FEASIBLE",
            "objective": objective,
            "columns": {"named": 80, "total": 80},
        },
    }


def certificate_check(status="PARTIAL", returncode=11, verified="primal"):
    return {
        "process_wall_sec": 0.1,
        "returncode": returncode,
        "timed_out": False,
        "memout": False,
        "cancelled": False,
        "stdout_truncated": False,
        "stderr_truncated": False,
        "output_truncated": False,
        "parsed": {
            "status": status,
            "claims": {"verified": verified, "refuted": "-", "unbacked": "dual"},
        },
    }


def ay_result(**updates):
    result = {
        "status": "optimal",
        "objective": "273",
        "solver_runtime_sec": 2.0,
        "worker_budget": 1,
        "deterministic": True,
        "process_wall_sec": 2.1,
        "returncode": 0,
        "timed_out": False,
        "memout": False,
        "cancelled": False,
        "output_truncated": False,
        "parse_error": None,
        "certificate": {"exists": True},
        "certificate_check": certificate_check(),
        "point_check": point_check(),
    }
    result.update(updates)
    return result


def gurobi_result(**updates):
    result = {
        "status": "optimal",
        "objective": 273.0,
        "solver_runtime_sec": 3.0,
        "worker_budget": 1,
        "seed": 0,
        "mip_gap": 0.0,
        "mip_gap_abs": 0.0,
        "process_wall_sec": 3.1,
        "returncode": 0,
        "timed_out": False,
        "memout": False,
        "cancelled": False,
        "output_truncated": False,
        "parse_error": None,
        "solution_error": None,
        "point_check": point_check(),
    }
    result.update(updates)
    return result


class CorpusAndPostureTest(unittest.TestCase):
    def test_known_open_corpus_is_exact_and_unique(self):
        self.assertEqual(len(dense.LADDER_8T), 12)
        self.assertEqual(len(set(dense.LADDER_8T)), 12)
        self.assertEqual(dense.LADDER_1T, dense.LADDER_8T)
        self.assertEqual(dense.SERIAL_1T, ((80, 60, 2026, 273),))
        self.assertEqual(
            len(dense.LADDER_8T) + len(dense.LADDER_1T) + len(dense.SERIAL_1T),
            25,
        )

    def test_environment_scrubs_lane_controls_then_sets_explicit_posture(self):
        with mock.patch.dict(
            dense.os.environ,
            {
                "PATH": "/bin",
                "AY_MILP_GMI_ROUNDS": "99",
                "AY_PB_PARALLEL": "8",
                "NY_NO_CNF_ROUTE": "1",
                "MEMLIMIT": "99999",
                "NBCORE": "99",
            },
            clear=True,
        ):
            env = dense.controlled_env(Plan(), 8, 60.0)
        self.assertNotIn("AY_MILP_GMI_ROUNDS", env)
        self.assertNotIn("AY_MILP_THREADS", env)
        self.assertNotIn("AY_PB_PARALLEL", env)
        self.assertNotIn("NY_NO_CNF_ROUTE", env)
        self.assertNotIn("MEMLIMIT", env)
        self.assertNotIn("NBCORE", env)
        self.assertNotIn("TIME_LIMIT", env)
        self.assertEqual(env["OMP_NUM_THREADS"], "8")
        self.assertEqual(env["RAYON_NUM_THREADS"], "8")

    def test_gurobi_driver_pins_seed_threads_and_zero_gaps(self):
        compile(dense.GUROBI_DRIVER, "<gurobi-driver>", "exec")
        self.assertIn("model.Params.Threads = threads", dense.GUROBI_DRIVER)
        self.assertIn("model.Params.Seed = 0", dense.GUROBI_DRIVER)
        self.assertIn("model.Params.MIPGap = 0.0", dense.GUROBI_DRIVER)
        self.assertIn("model.Params.MIPGapAbs = 0.0", dense.GUROBI_DRIVER)

    def test_production_ay_command_pins_posture_and_evidence(self):
        command = dense.build_ay_command(
            Path("/frozen/ay-milp"),
            Path("/instances/60x45-s7.mps"),
            8,
            60.0,
            Path("/artifacts/result.ayc"),
            Path("/artifacts/result.sol"),
        )
        self.assertEqual(command[:3], [
            "/frozen/ay-milp", "solve", "/instances/60x45-s7.mps"
        ])
        self.assertIn("--threads", command)
        self.assertEqual(command[command.index("--threads") + 1], "8")
        self.assertIn("--no-deterministic", command)
        self.assertEqual(command[command.index("--require") + 1], "witness")
        self.assertEqual(command[command.index("--witness-format") + 1], "rational")

        serial = dense.build_ay_command(
            Path("/frozen/ay-milp"), Path("/instances/case.mps"), 1, 200.0,
            Path("/artifacts/result.ayc"), Path("/artifacts/result.sol"),
        )
        self.assertIn("--deterministic", serial)
        self.assertNotIn("--no-deterministic", serial)

    def test_launch_order_is_balanced_at_one_repetition_and_flips_on_repeat(self):
        first_solvers = [dense.solver_order(index, 0)[0] for index in range(25)]
        self.assertLessEqual(abs(first_solvers.count("ay") - first_solvers.count("gurobi")), 1)
        for index in range(25):
            self.assertNotEqual(
                dense.solver_order(index, 0)[0], dense.solver_order(index, 1)[0]
            )


class EvidenceGateTest(unittest.TestCase):
    def test_valid_matched_results_pass(self):
        self.assertEqual(dense.valid_optimum(ay_result(), 273, "ay", 1), [])
        self.assertEqual(
            dense.valid_optimum(gurobi_result(), 273, "gurobi", 1), []
        )

    def test_nonfinite_process_wall_fails_closed(self):
        failures = dense.valid_optimum(
            ay_result(process_wall_sec=math.nan), 273, "ay", 1
        )
        self.assertIn("process wall is invalid", " ".join(failures))

    def test_requested_ay_determinism_must_be_observed(self):
        failures = dense.valid_optimum(
            ay_result(worker_budget=8, deterministic=True), 273, "ay", 8
        )
        self.assertIn("deterministic posture", " ".join(failures))

    def test_gurobi_nonzero_gap_fails_closed(self):
        failures = dense.valid_optimum(
            gurobi_result(mip_gap=1e-4), 273, "gurobi", 1
        )
        self.assertIn("mip_gap", " ".join(failures))

    def test_reported_and_exactly_checked_objectives_must_agree(self):
        failures = dense.valid_optimum(
            ay_result(point_check=point_check("272")), 273, "ay", 1
        )
        self.assertIn("checked point objective", " ".join(failures))

    def test_partial_certificate_must_still_verify_the_primal_claim(self):
        failures = dense.valid_optimum(
            ay_result(certificate_check=certificate_check(verified="-")),
            273,
            "ay",
            1,
        )
        self.assertIn("verified primal", " ".join(failures))

    def test_timeout_memout_and_truncation_each_fail(self):
        for field in ("timed_out", "memout", "cancelled", "output_truncated"):
            with self.subTest(field=field):
                failures = dense.valid_optimum(
                    ay_result(**{field: True}), 273, "ay", 1
                )
                self.assertIn(field, " ".join(failures))

    def test_frozen_binary_hash_must_match_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source"
            destination = root / "frozen"
            source.write_bytes(b"binary")
            identity = dense.freeze_binary(source, destination)
            self.assertEqual(
                identity["source"]["sha256"], identity["frozen"]["sha256"]
            )

            def corrupt_copy(_source, target):
                Path(target).write_bytes(b"different")

            with mock.patch.object(dense.shutil, "copy2", side_effect=corrupt_copy):
                with self.assertRaisesRegex(RuntimeError, "changed while"):
                    dense.freeze_binary(source, root / "corrupt")

    def test_exit_zero_requires_every_record_and_repetition_closed(self):
        closed = {
            "closed": True,
            "summary": {
                "expected_cases": 1,
                "expected_repetitions_per_case": 1,
            },
            "records": [{
                "closed": True,
                "repetitions": [{"closed": True, "repetition": 0}],
            }],
        }
        self.assertEqual(dense.campaign_exit_code(closed), 0)
        for payload in (
            {"closed": True, "records": []},
            {"closed": False, "records": closed["records"]},
            {
                "closed": True,
                "summary": closed["summary"],
                "records": [{
                    "closed": True,
                    "repetitions": [{"closed": False, "repetition": 0}],
                }],
            },
        ):
            with self.subTest(payload=payload):
                self.assertEqual(dense.campaign_exit_code(payload), 1)


if __name__ == "__main__":
    unittest.main()
