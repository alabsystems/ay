# ay-script: ay-gurobi-closure-tests
"""Pure stdlib tests for the AY-vs-Gurobi closure harness.

These tests exercise list integrity, command posture, parsers, and evidence
classification.  They never import Gurobi and never launch either solver.
"""

import gzip
import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stderr
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS_DIR))

import ay_gurobi_closure as closure  # noqa: E402


def clean_process(wall=1.0, returncode=0):
    return {
        "launch_error": None,
        "returncode": returncode,
        "timed_out": False,
        "memout": False,
        "cancelled": False,
        "stdout_truncated": False,
        "stderr_truncated": False,
        "wall_sec": wall,
    }


def point_check(status="FEASIBLE"):
    return {
        "process": clean_process(0.01),
        "parsed": {"status": status, "objective": "7", "columns": None},
    }


def ay_result(
    status="OPTIMAL",
    value=7.0,
    wall=1.0,
    cert_status="VERIFIED",
    verified_claims="primal,dual",
    unbacked_claims="-",
):
    checker_exit = {
        "VERIFIED": 0,
        "UNVERIFIED": 10,
        "PARTIAL": 11,
        "REFUTED": 20,
        "MISMATCH": 30,
    }[cert_status]
    return {
        "process": clean_process(wall),
        "parse_error": None,
        "verdict": {
            "status": status,
            "value": value,
            "dual_bound": None,
        },
        "point_check": point_check() if value is not None else {},
        "certificate_check": {
            "process": clean_process(0.01, checker_exit),
            "parsed": {
                "status": cert_status,
                "census": (
                    f"CLAIMS verified={verified_claims} refuted=- "
                    f"unbacked={unbacked_claims}"
                ),
                "claims": {
                    "verified": verified_claims,
                    "refuted": "-",
                    "unbacked": unbacked_claims,
                },
            },
        },
    }


def gurobi_result(status="OPTIMAL", value=7.0, wall=2.0):
    return {
        "process": clean_process(wall),
        "parse_error": None,
        "verdict": {
            "status": status,
            "objective": value,
            "dual_bound": value,
            "solution_count": 1 if value is not None else 0,
        },
        "point_check": point_check() if value is not None else {},
    }


class FrozenCorpusTest(unittest.TestCase):
    def test_historical_list_is_exactly_101_unique_cases(self):
        names = closure.load_case_list()
        self.assertEqual(len(names), 101)
        self.assertEqual(len(set(names)), 101)
        self.assertEqual(names[0], "ej")
        self.assertEqual(names[65], "mtest4ma")
        self.assertEqual(names[66], "stein9inf")
        self.assertEqual(names[-1], "qnet1_o")
        self.assertNotIn("control30-3-2-3", names)
        self.assertNotIn("neos-3421095-cinca", names)

    def test_first_panel_is_a_unique_subset_and_keeps_rout(self):
        names = set(closure.load_case_list())
        self.assertEqual(len(closure.FIRST_PANEL), len(set(closure.FIRST_PANEL)))
        self.assertTrue(set(closure.FIRST_PANEL).issubset(names))
        self.assertIn("rout", closure.FIRST_PANEL)
        self.assertIn("nexp-50-20-1-1", closure.FIRST_PANEL)
        self.assertIn("enlight_hard", closure.FIRST_PANEL)

    def test_duplicate_custom_list_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory, "dupes.txt")
            path.write_text("a\na\n")
            with self.assertRaisesRegex(ValueError, "duplicate"):
                closure.load_case_list(path)


class SelectionTest(unittest.TestCase):
    def test_default_selection_remains_the_complete_frozen_corpus(self):
        parser = closure.build_parser()
        args = parser.parse_args([])
        all_names = closure.load_case_list()
        self.assertEqual(args.only, "all")
        self.assertIsNone(args.case)
        self.assertEqual(closure.select_names(args, all_names, parser), all_names)

    def test_case_selects_exactly_one_frozen_instance(self):
        parser = closure.build_parser()
        args = parser.parse_args(["--case", "rout"])
        self.assertEqual(
            closure.select_names(args, closure.load_case_list(), parser), ["rout"]
        )

    def test_case_and_only_are_mutually_exclusive(self):
        parser = closure.build_parser()
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            parser.parse_args(["--case", "rout", "--only", "first-panel"])

    def test_unknown_case_fails_closed(self):
        parser = closure.build_parser()
        args = parser.parse_args(["--case", "not-in-the-frozen-corpus"])
        with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            closure.select_names(args, closure.load_case_list(), parser)


class CommandPostureTest(unittest.TestCase):
    def test_ay_command_uses_production_cli_and_evidence_flags(self):
        command = closure.build_ay_command(
            Path("/frozen/ay-milp"),
            Path("/corpus/rout.mps.gz"),
            60.0,
            0,
            Path("/artifacts/rout.ayc"),
            Path("/artifacts/rout.sol"),
        )
        self.assertEqual(command[:3], ["/frozen/ay-milp", "solve", "/corpus/rout.mps.gz"])
        self.assertNotIn("examples/mps_solve", " ".join(command))
        for required in (
            "--threads", "--seed", "--deterministic", "--require",
            "--emit-cert", "--emit-witness", "--witness-format", "--format",
        ):
            self.assertIn(required, command)
        self.assertEqual(command[command.index("--threads") + 1], "1")
        self.assertEqual(command[command.index("--require") + 1], "witness")
        self.assertEqual(command[-1], "json")

    def test_gurobi_child_pins_one_thread_seed_and_zero_gaps(self):
        command = closure.build_gurobi_command(
            Path("/usr/bin/python3"), Path("/corpus/rout.mps.gz"), 60.0, 0,
            Path("/artifacts/rout.sol"), Path("/artifacts/rout.log"),
        )
        self.assertEqual(command[:2], ["/usr/bin/python3", "-c"])
        self.assertEqual(command[3], "solve")
        self.assertIn('model.setParam("Threads", 1)', closure.GUROBI_CHILD)
        self.assertIn('model.setParam("Seed", seed)', closure.GUROBI_CHILD)
        self.assertIn('model.setParam("MIPGap", 0.0)', closure.GUROBI_CHILD)
        self.assertIn('model.setParam("MIPGapAbs", 0.0)', closure.GUROBI_CHILD)
        shown = closure.display_command(command)
        self.assertIn("GUROBI_CHILD sha256=", shown[2])
        self.assertNotIn("import gurobipy", shown[2])
        compile(closure.GUROBI_CHILD, "<gurobi-child>", "exec")

    def test_controlled_environment_removes_hidden_ay_knobs(self):
        env, posture = closure.controlled_environment(
            {
                "PATH": "/bin",
                "AY_MILP_GMI_MAX_ROWS": "999",
                "AY_PB_PARALLEL": "8",
                "NY_NO_CNF_ROUTE": "1",
                "MEMLIMIT": "999999",
                "NBCORE": "99",
                "TIME_LIMIT": "999",
                "OMP_NUM_THREADS": "8",
                "GRB_LICENSE_FILE": "/secret/license.lic",
            }
        )
        self.assertNotIn("AY_MILP_GMI_MAX_ROWS", env)
        self.assertNotIn("AY_PB_PARALLEL", env)
        self.assertNotIn("NY_NO_CNF_ROUTE", env)
        self.assertNotIn("MEMLIMIT", env)
        self.assertNotIn("NBCORE", env)
        self.assertNotIn("TIME_LIMIT", env)
        self.assertEqual(env["OMP_NUM_THREADS"], "1")
        self.assertEqual(
            posture["removed_solver_environment"],
            {
                "AY_MILP_GMI_MAX_ROWS": "999",
                "AY_PB_PARALLEL": "8",
                "MEMLIMIT": "999999",
                "NBCORE": "99",
                "NY_NO_CNF_ROUTE": "1",
                "TIME_LIMIT": "999",
            },
        )
        self.assertEqual(
            posture["gurobi_license_environment_names_present"],
            ["GRB_LICENSE_FILE"],
        )
        self.assertNotIn("/secret/license.lic", json.dumps(posture))


class ParserTest(unittest.TestCase):
    def test_last_json_parser_ignores_banner_and_malformed_lines(self):
        parsed = closure.parse_last_json_object(
            "license banner\n{bad json}\n{\"status\":\"OPTIMAL\",\"nodes\":3}\n"
        )
        self.assertEqual(parsed, {"status": "OPTIMAL", "nodes": 3})

    def test_verify_parser_keeps_claim_census(self):
        parsed = closure.parse_verify_output(
            "  claim primal witness ok detail\n"
            "CLAIMS verified=primal refuted=- unbacked=dual\nPARTIAL\n"
        )
        self.assertEqual(parsed["status"], "PARTIAL")
        self.assertEqual(parsed["claims"]["verified"], "primal")
        self.assertEqual(parsed["claims"]["unbacked"], "dual")

    def test_point_parser_records_exact_checker_coverage(self):
        parsed = closure.parse_point_output(
            "point: 556 of 556 columns named\n"
            "FEASIBLE  objective 26939/25 (file frame)\n"
        )
        self.assertEqual(parsed["status"], "FEASIBLE")
        self.assertEqual(parsed["objective"], "26939/25")
        self.assertEqual(parsed["columns"], {"named": 556, "total": 556})

    def test_point_parser_accepts_explicit_exact_continuous_repair(self):
        parsed = closure.parse_point_output(
            "point: 556 of 556 columns named\n"
            "point: decimal text failed exact checking (RowBound { row: Row(0) }); "
            "attempting continuous repair\n"
            "FEASIBLE  objective 26939/25 (file frame; continuous values exactly repaired)\n"
        )
        self.assertEqual(parsed["status"], "FEASIBLE")
        self.assertEqual(parsed["objective"], "26939/25")
        self.assertEqual(parsed["columns"], {"named": 556, "total": 556})

    def test_mps_sense_defaults_to_min_and_reads_max(self):
        with tempfile.TemporaryDirectory() as directory:
            minimum = Path(directory, "min.mps.gz")
            maximum = Path(directory, "max.mps.gz")
            with gzip.open(minimum, "wt") as handle:
                handle.write("NAME min\nROWS\n N obj\nENDATA\n")
            with gzip.open(maximum, "wt") as handle:
                handle.write("NAME max\nOBJSENSE\n MAX\nROWS\n N obj\nENDATA\n")
            self.assertEqual(closure.mps_sense(minimum), "minimize")
            self.assertEqual(closure.mps_sense(maximum), "maximize")


class EvidenceGateTest(unittest.TestCase):
    def setUp(self):
        self.reference = {
            "status": "OPTIMAL", "objective": 7.0,
            "objective_text": "7", "source_token": "=opt=",
        }

    def test_verified_optimal_certificate_with_primal_and_dual_is_counted(self):
        evaluated = closure.evaluate_solver(
            "ay", ay_result(), self.reference, "minimize", 1e-6
        )
        self.assertTrue(evaluated["solved"])
        self.assertTrue(evaluated["point_verified"])
        self.assertEqual(evaluated["certificate_status"], "VERIFIED")
        self.assertTrue(evaluated["certificate_complete"])
        self.assertEqual(
            evaluated["certificate_required_claims"], ["dual", "primal"]
        )
        self.assertEqual(evaluated["certificate_missing_verified_claims"], [])
        self.assertFalse(evaluated["invalid_issues"])

    def test_partial_optimal_certificate_preserves_point_but_rejects_verdict(self):
        evaluated = closure.evaluate_solver(
            "ay",
            ay_result(
                cert_status="PARTIAL",
                verified_claims="primal",
                unbacked_claims="dual",
            ),
            self.reference,
            "minimize",
            1e-6,
        )
        self.assertFalse(evaluated["solved"])
        self.assertTrue(evaluated["point_verified"])
        self.assertEqual(evaluated["certificate_status"], "PARTIAL")
        self.assertFalse(evaluated["certificate_complete"])
        self.assertEqual(evaluated["certificate_missing_verified_claims"], ["dual"])
        diagnostics = " ".join(evaluated["invalid_issues"])
        self.assertIn("requires certificate status VERIFIED, got PARTIAL", diagnostics)
        self.assertIn("claim(s): dual", diagnostics)

    def test_unverified_optimal_certificate_is_rejected_explicitly(self):
        evaluated = closure.evaluate_solver(
            "ay",
            ay_result(
                cert_status="UNVERIFIED",
                verified_claims="primal",
                unbacked_claims="dual",
            ),
            self.reference,
            "minimize",
            1e-6,
        )
        self.assertFalse(evaluated["solved"])
        self.assertFalse(evaluated["certificate_complete"])
        diagnostics = " ".join(evaluated["invalid_issues"])
        self.assertIn("requires certificate status VERIFIED, got UNVERIFIED", diagnostics)

    def test_verified_word_without_dual_claim_rejects_optimal_verdict(self):
        evaluated = closure.evaluate_solver(
            "ay",
            ay_result(
                cert_status="VERIFIED",
                verified_claims="primal",
                unbacked_claims="dual",
            ),
            self.reference,
            "minimize",
            1e-6,
        )
        self.assertFalse(evaluated["solved"])
        self.assertFalse(evaluated["certificate_complete"])
        self.assertEqual(evaluated["certificate_missing_verified_claims"], ["dual"])
        self.assertIn("claim(s): dual", " ".join(evaluated["invalid_issues"]))

    def test_unverified_infeasible_ay_verdict_is_not_counted(self):
        reference = {
            "status": "INFEASIBLE", "objective": None,
            "objective_text": None, "source_token": "=inf=",
        }
        result = ay_result(
            status="INFEASIBLE", value=None, cert_status="UNVERIFIED"
        )
        result["certificate_check"]["parsed"]["claims"] = {
            "verified": "-", "refuted": "-", "unbacked": "infeasible"
        }
        evaluated = closure.evaluate_solver(
            "ay", result, reference, "minimize", 1e-6
        )
        self.assertFalse(evaluated["solved"])
        self.assertIn("verified infeasible", " ".join(evaluated["invalid_issues"]))

    def test_verified_infeasible_ay_verdict_is_counted(self):
        reference = {
            "status": "INFEASIBLE", "objective": None,
            "objective_text": None, "source_token": "=inf=",
        }
        result = ay_result(
            status="INFEASIBLE", value=None, cert_status="VERIFIED"
        )
        result["certificate_check"]["parsed"]["claims"] = {
            "verified": "infeasible", "refuted": "-", "unbacked": "-"
        }
        evaluated = closure.evaluate_solver(
            "ay", result, reference, "minimize", 1e-6
        )
        self.assertTrue(evaluated["solved"])
        self.assertTrue(evaluated["certificate_complete"])

    def test_verified_word_without_unbounded_claim_does_not_count(self):
        reference = {
            "status": "UNBOUNDED", "objective": None,
            "objective_text": None, "source_token": "=unbd=",
        }
        result = ay_result(
            status="UNBOUNDED", value=None, cert_status="VERIFIED"
        )
        result["certificate_check"]["parsed"]["claims"] = {
            "verified": "primal", "refuted": "-", "unbacked": "unbounded"
        }
        evaluated = closure.evaluate_solver(
            "ay", result, reference, "minimize", 1e-6
        )
        self.assertFalse(evaluated["solved"])
        self.assertIn("verified unbounded", " ".join(evaluated["invalid_issues"]))

    def test_refuted_certificate_invalidates_ay_verdict(self):
        evaluated = closure.evaluate_solver(
            "ay", ay_result(cert_status="REFUTED"),
            self.reference, "minimize", 1e-6,
        )
        self.assertFalse(evaluated["solved"])
        self.assertIn("REFUTED", " ".join(evaluated["invalid_issues"]))

    def test_certificate_word_and_exit_code_must_agree(self):
        result = ay_result(cert_status="PARTIAL")
        result["certificate_check"]["process"]["returncode"] = 0
        evaluated = closure.evaluate_solver(
            "ay", result, self.reference, "minimize", 1e-6
        )
        self.assertFalse(evaluated["solved"])
        self.assertIn("reported status", " ".join(evaluated["invalid_issues"]))

    def test_reported_value_must_match_checked_point_objective(self):
        result = ay_result(value=8.0)
        evaluated = closure.evaluate_solver(
            "ay", result, self.reference, "minimize", 1e-6
        )
        self.assertFalse(evaluated["solved"])
        self.assertIn("checked point", " ".join(evaluated["invalid_issues"]))

    def test_wrong_optimum_and_impossible_bound_are_both_detected(self):
        result = gurobi_result(value=6.0)
        result["verdict"]["dual_bound"] = 8.0
        evaluated = closure.evaluate_solver(
            "gurobi", result, self.reference, "minimize", 1e-6
        )
        self.assertFalse(evaluated["solved"])
        self.assertGreaterEqual(len(evaluated["wrong_issues"]), 2)

    def test_reference_infeasible_requires_infeasible_terminal_status(self):
        reference = {
            "status": "INFEASIBLE", "objective": None,
            "objective_text": None, "source_token": "=inf=",
        }
        result = gurobi_result(status="INFEASIBLE", value=None)
        evaluated = closure.evaluate_solver(
            "gurobi", result, reference, "minimize", 1e-6
        )
        self.assertTrue(evaluated["solved"])

    def test_time_limited_gurobi_incumbent_is_still_point_checked(self):
        result = gurobi_result(status="TIMEOUT", value=7.0)
        evaluated = closure.evaluate_solver(
            "gurobi", result, self.reference, "minimize", 1e-6
        )
        self.assertTrue(evaluated["has_incumbent"])
        self.assertTrue(evaluated["point_verified"])
        self.assertFalse(evaluated["solved"])

    def test_aggregate_exposes_known_gurobi_advantage(self):
        ay_eval = closure.evaluate_solver(
            "ay", ay_result(wall=4.0), self.reference, "minimize", 1e-6
        )
        grb_eval = closure.evaluate_solver(
            "gurobi", gurobi_result(wall=1.0), self.reference, "minimize", 1e-6
        )
        row = {
            "name": "rout",
            "repetition": 0,
            "ay_evaluation": ay_eval,
            "gurobi_evaluation": grb_eval,
        }
        summary = closure.aggregate_rows([row], ["rout"], 1)
        self.assertEqual(summary["known_gurobi_advantages"], ["rout"])
        self.assertFalse(summary["dominance_closed"])
        self.assertEqual(closure.campaign_exit_code(summary), 1)

    def test_incomplete_campaign_cannot_report_dominance(self):
        summary = closure.aggregate_rows([], ["rout"], 1)
        self.assertEqual(summary["inconclusive_cases"], ["rout"])
        self.assertFalse(summary["dominance_closed"])
        self.assertEqual(closure.campaign_exit_code(summary), 2)

    def test_both_timing_out_is_unresolved_not_dominance(self):
        ay_eval = closure.evaluate_solver(
            "ay",
            ay_result(status="UNKNOWN", value=None, cert_status="UNVERIFIED"),
            self.reference,
            "minimize",
            1e-6,
        )
        grb_eval = closure.evaluate_solver(
            "gurobi", gurobi_result(status="TIMEOUT", value=None),
            self.reference, "minimize", 1e-6,
        )
        summary = closure.aggregate_rows(
            [{
                "name": "rout",
                "repetition": 0,
                "ay_evaluation": ay_eval,
                "gurobi_evaluation": grb_eval,
            }],
            ["rout"],
            1,
        )
        self.assertEqual(summary["classification_counts"], {"NEITHER": 1})
        self.assertEqual(summary["inconclusive_cases"], ["rout"])
        self.assertFalse(summary["dominance_closed"])
        self.assertEqual(closure.campaign_exit_code(summary), 2)

    def test_partial_repetition_coverage_is_unstable_not_dominance(self):
        solved_ay = closure.evaluate_solver(
            "ay", ay_result(), self.reference, "minimize", 1e-6
        )
        solved_grb = closure.evaluate_solver(
            "gurobi", gurobi_result(), self.reference, "minimize", 1e-6
        )
        unknown_ay = closure.evaluate_solver(
            "ay",
            ay_result(status="UNKNOWN", value=None, cert_status="UNVERIFIED"),
            self.reference,
            "minimize",
            1e-6,
        )
        unknown_grb = closure.evaluate_solver(
            "gurobi", gurobi_result(status="TIMEOUT", value=None),
            self.reference, "minimize", 1e-6,
        )
        rows = [
            {
                "name": "rout",
                "repetition": 0,
                "ay_evaluation": solved_ay,
                "gurobi_evaluation": solved_grb,
            },
            {
                "name": "rout",
                "repetition": 1,
                "ay_evaluation": unknown_ay,
                "gurobi_evaluation": unknown_grb,
            },
        ]
        summary = closure.aggregate_rows(rows, ["rout"], 2)
        self.assertEqual(
            summary["classification_counts"], {"INCONCLUSIVE_UNSTABLE": 1}
        )
        self.assertEqual(summary["inconclusive_cases"], ["rout"])
        self.assertFalse(summary["dominance_closed"])

    def test_one_gurobi_faster_repetition_cannot_be_hidden_by_median(self):
        walls = ((1.0, 4.0), (1.0, 4.0), (10.0, 1.0))
        rows = []
        for repetition, (ay_wall, gurobi_wall) in enumerate(walls):
            rows.append({
                "name": "rout",
                "repetition": repetition,
                "ay_evaluation": closure.evaluate_solver(
                    "ay", ay_result(wall=ay_wall), self.reference, "minimize", 1e-6
                ),
                "gurobi_evaluation": closure.evaluate_solver(
                    "gurobi", gurobi_result(wall=gurobi_wall), self.reference,
                    "minimize", 1e-6,
                ),
            })
        summary = closure.aggregate_rows(rows, ["rout"], 3)
        self.assertEqual(
            summary["classification_counts"], {"GUROBI_TRIAL_ADVANTAGE": 1}
        )
        self.assertEqual(summary["known_gurobi_advantages"], ["rout"])
        self.assertFalse(summary["dominance_closed"])
        self.assertEqual(closure.campaign_exit_code(summary), 1)

    def test_duplicate_repetition_ids_are_incomplete_evidence(self):
        ay_eval = closure.evaluate_solver(
            "ay", ay_result(), self.reference, "minimize", 1e-6
        )
        gurobi_eval = closure.evaluate_solver(
            "gurobi", gurobi_result(), self.reference, "minimize", 1e-6
        )
        rows = [
            {
                "name": "rout",
                "repetition": 0,
                "ay_evaluation": ay_eval,
                "gurobi_evaluation": gurobi_eval,
            },
            {
                "name": "rout",
                "repetition": 0,
                "ay_evaluation": ay_eval,
                "gurobi_evaluation": gurobi_eval,
            },
        ]
        summary = closure.aggregate_rows(rows, ["rout"], 2)
        self.assertEqual(summary["classification_counts"], {"INCOMPLETE": 1})
        self.assertFalse(summary["dominance_closed"])
        self.assertEqual(closure.campaign_exit_code(summary), 2)

    def test_invalid_evidence_has_exit_code_three(self):
        bad = ay_result()
        bad["process"]["memout"] = True
        ay_eval = closure.evaluate_solver(
            "ay", bad, self.reference, "minimize", 1e-6
        )
        gurobi_eval = closure.evaluate_solver(
            "gurobi", gurobi_result(), self.reference, "minimize", 1e-6
        )
        summary = closure.aggregate_rows(
            [{
                "name": "rout",
                "repetition": 0,
                "ay_evaluation": ay_eval,
                "gurobi_evaluation": gurobi_eval,
            }],
            ["rout"],
            1,
        )
        self.assertEqual(closure.campaign_exit_code(summary), 3)


class PreflightTest(unittest.TestCase):
    def test_manifest_and_solu_must_agree(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            model = root / "tiny.mps.gz"
            with gzip.open(model, "wt") as handle:
                handle.write("NAME tiny\nROWS\n N obj\nENDATA\n")
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({
                "instances": {
                    "tiny": {"file": str(model), "ref_status": "opt"}
                }
            }))
            solu = root / "truth.solu"
            solu.write_text("=inf= tiny\n")
            with self.assertRaisesRegex(ValueError, "status mismatch"):
                closure.preflight_cases(["tiny"], manifest, solu)

    def test_nonterminal_or_nonfinite_reference_truth_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            model = root / "tiny.mps.gz"
            with gzip.open(model, "wt") as handle:
                handle.write("NAME tiny\nROWS\n N obj\nENDATA\n")
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({
                "instances": {"tiny": {"file": str(model)}}
            }))
            solu = root / "truth.solu"
            solu.write_text("=unkn= tiny\n")
            with self.assertRaisesRegex(ValueError, "non-terminal"):
                closure.preflight_cases(["tiny"], manifest, solu)
            solu.write_text("=opt= tiny nan\n")
            with self.assertRaisesRegex(ValueError, "non-finite"):
                closure.preflight_cases(["tiny"], manifest, solu)


if __name__ == "__main__":
    unittest.main()
