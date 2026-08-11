#!/usr/bin/env python3
"""Policy tests for the focused W1 process-wall closure harness."""

from __future__ import annotations

import copy
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))

import ay_gurobi_w1_latency as w1  # noqa: E402


def evaluation(wall: float, solved: bool = True) -> dict:
    return {
        "status": "OPTIMAL" if solved else "TIMEOUT",
        "valid": True,
        "correct": True,
        "solved": solved,
        "point_verified": solved,
        "outer_wall_sec": wall,
        "sat_relu_route": {
            "accepted": True,
            "attempt_count": 1,
            "decline_count": 0,
            "fallback_count": 0,
            "malformed_count": 0,
        },
        "invalid_issues": [],
        "wrong_issues": [],
    }


def row(name: str, repetition: int, ay_wall: float, gurobi_wall: float) -> dict:
    ay = evaluation(ay_wall)
    gurobi = evaluation(gurobi_wall)
    return {
        "name": name,
        "repetition": repetition,
        "ay_evaluation": ay,
        "gurobi_evaluation": gurobi,
        "comparison": w1.compare_pair(ay, gurobi),
    }


def process(returncode: int = 0, wall: float = 0.1) -> dict:
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


def route_trace(outcome: str, *, fallback_count: int = 0) -> dict:
    return {
        "attempts": [
            {
                "line_number": 1,
                "variables": 10,
                "clauses": 20,
                "outcome": outcome,
                "reason": "unit-test",
                "wall_sec": 0.001,
            }
        ],
        "fallback_count": fallback_count,
        "fallback_lines": [2] if fallback_count else [],
        "malformed": [],
        "read_error": None,
    }


def certificate_artifact(kind: str) -> dict:
    profile = {
        "read_error": None,
        "evidence": [],
        "malformed_evidence": [],
        "block_counts": {
            token: 0 for token in sorted(w1.AYC_VERDICT_BLOCK_TOKENS)
        },
        "witness_block_count": 0,
        "optcert_block_count": 0,
        "sat_relu_rup_block_count": 0,
        "sat_relu_replay_block_count": 0,
    }
    if kind == "sat":
        profile.update(
            {
                "evidence": [
                    {
                        "claim": "primal",
                        "kind": "SUCCINCT",
                        "source": "witness",
                    },
                    {
                        "claim": "dual",
                        "kind": "SUCCINCT",
                        "source": "optcert",
                    },
                ],
                "witness_block_count": 1,
                "optcert_block_count": 1,
            }
        )
        profile["block_counts"]["witness"] = 1
        profile["block_counts"]["optcert"] = 1
    elif kind == "unsat":
        profile.update(
            {
                "evidence": [
                    {
                        "claim": "infeasible",
                        "kind": "SUCCINCT",
                        "source": "sat-relu-rup",
                    }
                ],
                "sat_relu_rup_block_count": 1,
            }
        )
        profile["block_counts"]["sat-relu-rup"] = 1
    elif kind == "replay":
        profile.update(
            {
                "evidence": [
                    {
                        "claim": "infeasible",
                        "kind": "REPLAY",
                        "source": "sat-relu-cnf-unsat",
                    }
                ],
                "sat_relu_replay_block_count": 1,
            }
        )
        profile["block_counts"]["replay"] = 1
    else:
        raise ValueError(kind)
    return profile


class W1LatencyPolicyTests(unittest.TestCase):
    def test_sat_relu_trace_parser_captures_all_outcomes_and_failures(self):
        parsed = w1.parse_sat_relu_route_trace_text(
            "unrelated diagnostic\n"
            "AY_MILP_TRACE sat-relu-proof: vars=10 clauses=20 "
            "outcome=SAT reason=checked-point wall=0.001000s\n"
            "AY_MILP_TRACE sat-relu-proof: vars=11 clauses=21 "
            "outcome=UNSAT reason=resolution dag checked wall=1.250000s\n"
            "AY_MILP_TRACE sat-relu-proof: vars=12 clauses=22 "
            "outcome=DECLINE reason=proof memory limit wall=2.000000s\n"
            "AY_MILP_TRACE sat-relu-proof: fallback=ordinary-cdcl\n"
            "AY_MILP_TRACE sat-relu-proof: changed-format\n"
        )
        self.assertEqual(
            [attempt["outcome"] for attempt in parsed["attempts"]],
            ["SAT", "UNSAT", "DECLINE"],
        )
        self.assertEqual(parsed["attempts"][1]["reason"], "resolution dag checked")
        self.assertEqual(parsed["fallback_count"], 1)
        self.assertEqual(parsed["fallback_lines"], [5])
        self.assertEqual(len(parsed["malformed"]), 1)
        self.assertEqual(parsed["malformed"][0]["line_number"], 6)

    def test_complete_stderr_trace_is_digest_checked(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            stderr = root / "stderr.txt"
            stderr.write_text(
                "AY_MILP_TRACE sat-relu-proof: vars=3 clauses=4 "
                "outcome=SAT reason=checked-point wall=0.000001s\n",
                encoding="utf-8",
            )
            record = w1.closure.artifact_identity(stderr, root)
            parsed = w1.read_sat_relu_route_trace({"stderr": record}, root)
            self.assertIsNone(parsed["read_error"])
            self.assertEqual(parsed["attempts"][0]["outcome"], "SAT")

            stderr.write_text(stderr.read_text(encoding="utf-8").replace("SAT", "BAD"))
            changed = w1.read_sat_relu_route_trace({"stderr": record}, root)
            self.assertIn("artifact", changed["read_error"])

    def test_route_evaluation_accepts_exactly_one_matching_outcome(self):
        sat = w1.evaluate_sat_relu_route_trace(
            {"sat_relu_route_trace": route_trace("SAT")}, "OPTIMAL"
        )
        unsat = w1.evaluate_sat_relu_route_trace(
            {"sat_relu_route_trace": route_trace("UNSAT")}, "INFEASIBLE"
        )
        self.assertTrue(sat["accepted"])
        self.assertTrue(unsat["accepted"])

    def test_route_evaluation_fails_closed(self):
        cases = {
            "missing": {},
            "read-error": {
                "sat_relu_route_trace": {
                    **route_trace("SAT"),
                    "read_error": "artifact missing",
                }
            },
            "decline": {"sat_relu_route_trace": route_trace("DECLINE")},
            "fallback": {
                "sat_relu_route_trace": route_trace("SAT", fallback_count=1)
            },
            "malformed": {
                "sat_relu_route_trace": {
                    **route_trace("SAT"),
                    "malformed": [{"line_number": 2, "text": "changed"}],
                }
            },
            "duplicate": {
                "sat_relu_route_trace": {
                    **route_trace("SAT"),
                    "attempts": route_trace("SAT")["attempts"] * 2,
                }
            },
            "wrong-outcome": {"sat_relu_route_trace": route_trace("UNSAT")},
        }
        for label, result in cases.items():
            with self.subTest(label=label):
                evaluated = w1.evaluate_sat_relu_route_trace(result, "OPTIMAL")
                self.assertFalse(evaluated["accepted"])
                self.assertTrue(evaluated["issues"])

    def test_trace_environment_is_ay_only_and_fingerprinted(self):
        base = {"PATH": "/bin", "OMP_NUM_THREADS": "1"}
        posture = {"environment_sha256": "old", "thread_limits": {}}
        traced, traced_posture = w1.traced_ay_environment(base, posture)
        self.assertNotIn("AY_MILP_TRACE", base)
        self.assertEqual(traced["AY_MILP_TRACE"], "1")
        self.assertEqual(
            traced_posture["enabled_solver_environment"], {"AY_MILP_TRACE": "1"}
        )
        self.assertNotEqual(traced_posture["environment_sha256"], "old")

    def test_ay_solve_command_carries_the_guarded_logical_budget(self):
        budget = 768 * 1024 * 1024
        command = w1.build_ay_command(
            Path("/frozen/ay-milp"),
            Path("/cases/model.mps"),
            15.0,
            Path("/artifacts/result.sol"),
            Path("/artifacts/result.ayc"),
            budget,
        )
        self.assertEqual(command[command.index("--memory-budget") + 1], str(budget))
        self.assertIn("--deterministic", command)
        with self.assertRaises(ValueError):
            w1.build_ay_command(
                Path("/frozen/ay-milp"),
                Path("/cases/model.mps"),
                15.0,
                Path("/artifacts/result.sol"),
                Path("/artifacts/result.ayc"),
                0,
            )

    def test_ay_rational_point_command_is_literal_exact(self):
        command = w1.build_point_check_command(
            Path("/frozen/ay-milp"),
            Path("/cases/model.mps"),
            Path("/artifacts/ay.sol"),
            w1.PointEvidenceMode.AY_RATIONAL_LITERAL,
        )
        self.assertEqual(
            command,
            [
                "/frozen/ay-milp",
                "check-point",
                "--model",
                "/cases/model.mps",
                "--point",
                "/artifacts/ay.sol",
            ],
        )
        self.assertNotIn("--repair-continuous", command)
        self.assertNotIn("--repair-time-limit", command)
        self.assertNotIn("--memory-budget", command)

    def test_gurobi_decimal_point_command_has_bounded_repair(self):
        command = w1.build_point_check_command(
            Path("/frozen/ay-milp"),
            Path("/cases/model.mps"),
            Path("/artifacts/gurobi.sol"),
            w1.PointEvidenceMode.GUROBI_DECIMAL_REPAIR,
            repair_time_limit=7.5,
            memory_budget_bytes=768 * 1024 * 1024,
        )
        self.assertIn("--repair-continuous", command)
        self.assertEqual(command[command.index("--repair-time-limit") + 1], "7.5")
        self.assertEqual(
            command[command.index("--memory-budget") + 1],
            str(768 * 1024 * 1024),
        )

    def test_evaluation_rejects_checked_objective_mismatch(self):
        result = {
            "process": process(),
            "parse_error": None,
            "verdict": {
                "status": "OPTIMAL",
                "objective": 1.0,
                "posture": {
                    "threads": 1,
                    "seed": w1.SOLVER_SEED,
                    "mip_gap": 0.0,
                    "mip_gap_abs": 0.0,
                },
            },
            "point_check": {
                "process": process(),
                "parsed": {"status": "FEASIBLE", "objective": "0"},
            },
        }
        evaluated = w1.evaluate_expected("gurobi", result, "OPTIMAL")
        self.assertFalse(evaluated["valid"])
        self.assertFalse(evaluated["solved"])
        self.assertIn(
            "zero-objective mismatch: reported=1.0, checked='0'",
            evaluated["invalid_issues"],
        )

    def test_frozen_loss_list_is_unique_and_complete(self):
        names = w1.load_case_names()
        expected = w1.load_case_expectations()
        self.assertEqual(len(names), 6)
        self.assertEqual(len(set(names)), 6)
        self.assertIn("W1_sat_v83_c328_000008", names)
        self.assertIn("W1_sat_v51_c255_000008", names)
        self.assertEqual(expected["W1_sat_v83_c328_000008"], "INFEASIBLE")
        self.assertEqual(expected["W1_sat_v83_c328_000000"], "OPTIMAL")

    def test_only_the_identity_checked_manifest_can_claim_full_census(self):
        source_sha = "a" * 64
        text = (
            "# test-w1-census-v1\n"
            f"# Source SHA-256: {source_sha}\n"
            "case_a OPTIMAL\n"
            "case_b INFEASIBLE\n"
        )
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = root / "full.txt"
            custom = root / "custom.txt"
            manifest.write_text(text, encoding="utf-8")
            custom.write_text(text, encoding="utf-8")
            expectations = w1.load_case_expectations(manifest)
            custom_kind = w1.classify_case_set(custom, expectations)
            self.assertEqual(custom_kind["kind"], "custom")
            self.assertFalse(custom_kind["full_census"])

            digest = w1.closure.sha256_bytes(text.encode("utf-8"))
            full_kind = w1.classify_case_set(
                manifest,
                expectations,
                full_census_path=manifest,
                full_census_schema="test-w1-census-v1",
                full_census_count=2,
                full_census_source_sha256=source_sha,
                full_census_manifest_sha256=digest,
            )
            self.assertEqual(full_kind["kind"], "full-w1-census")
            self.assertTrue(full_kind["full_census"])
            self.assertEqual(full_kind["source_sha256"], source_sha)

            manifest.write_text(text.replace("OPTIMAL", "INFEASIBLE"), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "manifest SHA-256"):
                w1.classify_case_set(
                    manifest,
                    expectations,
                    full_census_path=manifest,
                    full_census_schema="test-w1-census-v1",
                    full_census_count=2,
                    full_census_source_sha256=source_sha,
                    full_census_manifest_sha256=digest,
                )

    def test_even_repetitions_balance_each_cases_solver_order(self):
        names = w1.load_case_names()
        for name in names:
            orders = [w1.solver_order(name, names, repetition) for repetition in range(16)]
            self.assertEqual(orders.count(("ay", "gurobi")), 8)
            self.assertEqual(orders.count(("gurobi", "ay")), 8)
        for repetition in range(16):
            self.assertCountEqual(w1.schedule_for_repetition(names, repetition), names)

    def test_both_solver_captures_finish_before_any_verification(self):
        events = []

        def capture(solver):
            events.append(("capture", solver))
            return {"solver": solver}

        def verify(solver, result):
            events.append(("verify", solver))
            self.assertEqual(result, {"solver": solver})
            return {**result, "verified": True}

        results = w1.run_pair_before_verification(
            ("gurobi", "ay"), capture, verify
        )
        self.assertEqual(
            events,
            [
                ("capture", "gurobi"),
                ("capture", "ay"),
                ("verify", "gurobi"),
                ("verify", "ay"),
            ],
        )
        self.assertTrue(results["gurobi"]["verified"])
        self.assertTrue(results["ay"]["verified"])

    def test_objective_check_sums_repeated_entries_exactly(self):
        source = """\
NAME t
ROWS
 N objective
 E row
COLUMNS
    x objective 0.1 row 1
    x objective -0.1
RHS
    rhs row 0
ENDATA
"""
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "model.mps"
            path.write_text(source, encoding="utf-8")
            self.assertEqual(w1.objective_nonzeros(path), 0)
            path.write_text(source.replace("-0.1", "-0.09"), encoding="utf-8")
            self.assertEqual(w1.objective_nonzeros(path), 1)

    def test_one_gurobi_observation_cannot_be_hidden_by_median(self):
        name = "case"
        rows = [
            row(name, 0, 0.8, 1.0),
            row(name, 1, 0.8, 1.0),
            row(name, 2, 0.8, 1.0),
            row(name, 3, 1.01, 1.0),
        ]
        summary = w1.aggregate(rows, [name], 4)
        self.assertFalse(summary["dominance_closed"])
        self.assertEqual(len(summary["known_gurobi_advantages"]), 1)
        self.assertEqual(
            summary["cases"][0]["classification"],
            "GUROBI_OBSERVATION_ADVANTAGE",
        )

    def test_duplicate_repetition_is_incomplete(self):
        rows = [row("case", 0, 0.8, 1.0), row("case", 0, 0.8, 1.0)]
        summary = w1.aggregate(rows, ["case"], 2)
        self.assertFalse(summary["dominance_closed"])
        self.assertEqual(summary["cases"][0]["classification"], "INCOMPLETE")

    def test_aggregate_rejects_route_fallback_even_if_pair_looks_valid(self):
        rows = [row("case", 0, 0.8, 1.0), row("case", 1, 0.8, 1.0)]
        rows[1]["ay_evaluation"]["sat_relu_route"] = {
            "accepted": False,
            "attempt_count": 1,
            "decline_count": 0,
            "fallback_count": 1,
            "malformed_count": 0,
        }
        summary = w1.aggregate(rows, ["case"], 2)
        self.assertFalse(summary["dominance_closed"])
        self.assertFalse(summary["ay_sat_relu_route"]["closed"])
        self.assertEqual(summary["ay_sat_relu_route"]["ordinary_cdcl_fallbacks"], 1)
        self.assertEqual(
            summary["cases"][0]["classification"], "INCONCLUSIVE_INVALID"
        )

    def test_certified_aggregate_accepts_the_pinned_rup_evidence_mode(self):
        certified = evaluation(0.25)
        certified["evidence_mode"] = "verified-sat-relu-rup"
        summary = w1.aggregate_certified(
            [{"name": "case", "repetition": 0, "evaluation": certified}],
            ["case"],
            1,
        )
        self.assertTrue(summary["functionality_closed"])
        self.assertEqual(
            summary["cases"][0]["classification"], "VERIFIED_INFEASIBLE"
        )

    def test_common_unsat_rejects_replay_only_after_bounded_decline(self):
        result = {
            "process": process(),
            "parse_error": None,
            "sat_relu_route_trace": route_trace("UNSAT"),
            "verdict": {
                "status": "INFEASIBLE",
                "replay_claims": 1,
            },
            "point_check": {"not_run": True, "process": None, "parsed": None},
            "sat_relu_replay_marker": True,
            "certificate_artifact": certificate_artifact("replay"),
            "certificate_check": {
                "process": process(returncode=10),
                "parsed": {
                    "status": "UNVERIFIED",
                    "claims": {"verified": "-", "refuted": "-", "unbacked": "infeasible"},
                },
            },
        }
        common = w1.evaluate_expected("ay", result, "INFEASIBLE")
        self.assertFalse(common["solved"])
        self.assertIn(
            "common lane lacks a VERIFIED infeasible claim",
            common["invalid_issues"],
        )
        self.assertEqual(common["evidence_mode"], "missing-verified-sat-relu-rup")

        certified = w1.evaluate_expected(
            "ay", result, "INFEASIBLE", require_verified_infeasible=True
        )
        self.assertFalse(certified["solved"])
        self.assertIn(
            "certified lane lacks a VERIFIED infeasible claim",
            certified["invalid_issues"],
        )

    def test_ay_sat_requires_verified_primal_and_dual_claims(self):
        def sat_result(status: str, verified: str, returncode: int) -> dict:
            return {
                "process": process(),
                "parse_error": None,
                "sat_relu_route_trace": route_trace("SAT"),
                "verdict": {"status": "OPTIMAL", "value": 0.0},
                "point_check": {
                    "process": process(),
                    "parsed": {"status": "FEASIBLE", "objective": "0"},
                },
                "sat_relu_replay_marker": False,
                "certificate_artifact": certificate_artifact("sat"),
                "certificate_check": {
                    "process": process(returncode=returncode),
                    "parsed": {
                        "status": status,
                        "claims": {
                            "verified": verified,
                            "refuted": "-",
                            "unbacked": "-",
                        },
                    },
                },
            }

        accepted = w1.evaluate_expected(
            "ay", sat_result("VERIFIED", "primal,dual", 0), "OPTIMAL"
        )
        self.assertTrue(accepted["solved"])
        self.assertEqual(accepted["evidence_mode"], "verified-witness-optcert")

        rejected = [
            sat_result("PARTIAL", "primal,dual", 11),
            sat_result("UNVERIFIED", "-", 10),
            sat_result("VERIFIED", "primal", 0),
            sat_result("VERIFIED", "dual", 0),
        ]
        for result in rejected:
            with self.subTest(certificate=result["certificate_check"]["parsed"]):
                evaluated = w1.evaluate_expected("ay", result, "OPTIMAL")
                self.assertFalse(evaluated["solved"])
                self.assertIn(
                    "AY SAT lacks a VERIFIED certificate with primal and dual claims",
                    evaluated["invalid_issues"],
                )

    def test_certified_unsat_requires_verified_infeasible_claim(self):
        result = {
            "process": process(wall=0.25),
            "parse_error": None,
            "sat_relu_route_trace": route_trace("UNSAT"),
            "verdict": {"status": "INFEASIBLE", "replay_claims": 0},
            "point_check": {"not_run": True, "process": None, "parsed": None},
            "sat_relu_replay_marker": False,
            "certificate_artifact": certificate_artifact("unsat"),
            "certificate_check": {
                "process": process(returncode=0),
                "parsed": {
                    "status": "VERIFIED",
                    "claims": {"verified": "infeasible", "refuted": "-", "unbacked": "-"},
                },
            },
        }
        evaluated = w1.evaluate_expected(
            "ay", result, "INFEASIBLE", require_verified_infeasible=True
        )
        self.assertTrue(evaluated["solved"])
        self.assertEqual(evaluated["evidence_mode"], "verified-sat-relu-rup")

    def test_sat_relu_marker_requires_claim_and_replay_block(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            certificate = root / "result.ayc"
            certificate.write_text(
                "evidence infeasible REPLAY sat-relu-cnf-unsat\n"
                "replay sat-relu-cnf-unsat\nend\n",
                encoding="utf-8",
            )
            identity = w1.closure.artifact_identity(certificate, root)
            self.assertTrue(w1.sat_relu_replay_marker(identity, root))
            certificate.write_text(
                "evidence infeasible REPLAY sat-relu-cnf-unsat\n",
                encoding="utf-8",
            )
            identity = w1.closure.artifact_identity(certificate, root)
            # Either replay claim or replay block is forbidden on its own.
            self.assertTrue(w1.sat_relu_replay_marker(identity, root))
            certificate.write_text("evidence infeasible NONE\n", encoding="utf-8")
            identity = w1.closure.artifact_identity(certificate, root)
            self.assertFalse(w1.sat_relu_replay_marker(identity, root))

    def test_certificate_source_inspection_rechecks_artifact_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            certificate = root / "result.ayc"
            certificate.write_text(
                "evidence primal SUCCINCT witness\n"
                "evidence dual SUCCINCT optcert\n"
                "witness cols=0\nend\n"
                "optcert sense=min bound=0 frame=model trivial=1\nend\n",
                encoding="utf-8",
            )
            identity = w1.closure.artifact_identity(certificate, root)
            profile = w1.inspect_certificate_artifact(identity, root)
            self.assertIsNone(profile["read_error"])
            self.assertEqual(profile["witness_block_count"], 1)
            self.assertEqual(profile["optcert_block_count"], 1)
            certificate.write_text(
                certificate.read_text(encoding="utf-8").replace("witness", "changed", 1),
                encoding="utf-8",
            )
            changed = w1.inspect_certificate_artifact(identity, root)
            self.assertIn("artifact digest changed", changed["read_error"])

    def test_verified_other_proof_sources_cannot_own_the_sat_relu_route(self):
        unsat = {
            "process": process(),
            "parse_error": None,
            "sat_relu_route_trace": route_trace("UNSAT"),
            "verdict": {"status": "INFEASIBLE"},
            "point_check": {"not_run": True, "process": None, "parsed": None},
            "certificate_artifact": {
                **certificate_artifact("unsat"),
                "evidence": [
                    {
                        "claim": "infeasible",
                        "kind": "SUCCINCT",
                        "source": "farkas",
                    }
                ],
                "sat_relu_rup_block_count": 0,
            },
            "certificate_check": {
                "process": process(),
                "parsed": {
                    "status": "VERIFIED",
                    "claims": {
                        "verified": "infeasible",
                        "refuted": "-",
                        "unbacked": "-",
                    },
                },
            },
        }
        evaluated = w1.evaluate_expected("ay", unsat, "INFEASIBLE")
        self.assertFalse(evaluated["solved"])
        self.assertIn(
            "AY UNSAT certificate does not contain exactly the sat-relu-rup "
            "evidence record and typed block",
            evaluated["invalid_issues"],
        )

        sat = {
            "process": process(),
            "parse_error": None,
            "sat_relu_route_trace": route_trace("SAT"),
            "verdict": {"status": "OPTIMAL", "value": 0.0},
            "point_check": {
                "process": process(),
                "parsed": {"status": "FEASIBLE", "objective": "0"},
            },
            "certificate_artifact": {
                **certificate_artifact("sat"),
                "evidence": [
                    {
                        "claim": "primal",
                        "kind": "SUCCINCT",
                        "source": "witness",
                    },
                    {
                        "claim": "dual",
                        "kind": "SUCCINCT",
                        "source": "network-design-optimality",
                    },
                ],
                "optcert_block_count": 0,
            },
            "certificate_check": {
                "process": process(),
                "parsed": {
                    "status": "VERIFIED",
                    "claims": {
                        "verified": "primal,dual",
                        "refuted": "-",
                        "unbacked": "-",
                    },
                },
            },
        }
        evaluated = w1.evaluate_expected("ay", sat, "OPTIMAL")
        self.assertFalse(evaluated["solved"])
        self.assertIn(
            "AY SAT certificate does not contain exactly the witness+optcert "
            "evidence records and typed blocks",
            evaluated["invalid_issues"],
        )

    def test_certificate_route_ownership_rejects_every_extra_record_or_block(self):
        def result(expected: str, profile: dict) -> dict:
            if expected == "OPTIMAL":
                return {
                    "process": process(),
                    "parse_error": None,
                    "sat_relu_route_trace": route_trace("SAT"),
                    "verdict": {"status": "OPTIMAL", "value": 0.0},
                    "point_check": {
                        "process": process(),
                        "parsed": {"status": "FEASIBLE", "objective": "0"},
                    },
                    "certificate_artifact": profile,
                    "certificate_check": {
                        "process": process(),
                        "parsed": {
                            "status": "VERIFIED",
                            "claims": {
                                "verified": "primal,dual",
                                "refuted": "-",
                                "unbacked": "-",
                            },
                        },
                    },
                }
            return {
                "process": process(),
                "parse_error": None,
                "sat_relu_route_trace": route_trace("UNSAT"),
                "verdict": {"status": "INFEASIBLE"},
                "point_check": {"not_run": True, "process": None, "parsed": None},
                "certificate_artifact": profile,
                "certificate_check": {
                    "process": process(),
                    "parsed": {
                        "status": "VERIFIED",
                        "claims": {
                            "verified": "infeasible",
                            "refuted": "-",
                            "unbacked": "-",
                        },
                    },
                },
            }

        mutations = (
            ("duplicate-target", "witness", None),
            ("opposite-lane", "sat-relu-rup", None),
            ("other-proof", "farkas", None),
            (
                "extra-evidence",
                None,
                {
                    "claim": "infeasible",
                    "kind": "SUCCINCT",
                    "source": "sat-relu-rup",
                },
            ),
            (
                "replay",
                "replay",
                {
                    "claim": "infeasible",
                    "kind": "REPLAY",
                    "source": "sat-relu-cnf-unsat",
                },
            ),
        )
        for label, extra_block, extra_evidence in mutations:
            with self.subTest(lane="SAT", mutation=label):
                profile = copy.deepcopy(certificate_artifact("sat"))
                if extra_block is not None:
                    profile["block_counts"][extra_block] += 1
                if extra_evidence is not None:
                    profile["evidence"].append(extra_evidence)
                evaluated = w1.evaluate_expected(
                    "ay", result("OPTIMAL", profile), "OPTIMAL"
                )
                self.assertFalse(evaluated["solved"])

        mutations = (
            ("duplicate-target", "sat-relu-rup", None),
            ("opposite-lane", "witness", None),
            ("other-proof", "tree", None),
            (
                "extra-evidence",
                None,
                {
                    "claim": "primal",
                    "kind": "SUCCINCT",
                    "source": "witness",
                },
            ),
            (
                "replay",
                "replay",
                {
                    "claim": "infeasible",
                    "kind": "REPLAY",
                    "source": "sat-relu-cnf-unsat",
                },
            ),
        )
        for label, extra_block, extra_evidence in mutations:
            with self.subTest(lane="UNSAT", mutation=label):
                profile = copy.deepcopy(certificate_artifact("unsat"))
                if extra_block is not None:
                    profile["block_counts"][extra_block] += 1
                if extra_evidence is not None:
                    profile["evidence"].append(extra_evidence)
                evaluated = w1.evaluate_expected(
                    "ay", result("INFEASIBLE", profile), "INFEASIBLE"
                )
                self.assertFalse(evaluated["solved"])


if __name__ == "__main__":
    unittest.main()
