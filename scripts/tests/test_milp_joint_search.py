#!/usr/bin/env python3
# ay-script: milp-joint-search-tests
"""Pure-stdlib tests for the preregistered joint MILP search harness.

The suite never launches AY, Gurobi, Cargo, or a benchmark process.
"""

from __future__ import annotations

import contextlib
import hashlib
import io
import tempfile
import unittest
from pathlib import Path
import sys

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS_DIR))

import milp_joint_search as joint  # noqa: E402


TRACE_OK = {"inspected": True, "issues": [], "matches": []}


def clean_process(returncode=0, wall=1.0):
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


def optimal_result(value=7.0, nodes=10):
    return {
        "process": clean_process(),
        "parse_error": None,
        "verdict": {
            "status": "OPTIMAL",
            "value": value,
            "dual_bound": value,
            "nodes": nodes,
        },
        "point_check": {
            "process": clean_process(wall=0.01),
            "parsed": {"status": "FEASIBLE", "objective": str(value)},
        },
        "certificate_check": {
            "process": clean_process(returncode=0, wall=0.01),
            "parsed": {
                "status": "VERIFIED",
                "census": "CLAIMS verified=primal,dual refuted=- unbacked=-",
                "claims": {
                    "verified": "primal,dual",
                    "refuted": "-",
                    "unbacked": "-",
                },
            },
        },
    }


def unknown_result(nodes):
    return {
        "process": clean_process(),
        "parse_error": None,
        "verdict": {
            "status": "UNKNOWN",
            "value": None,
            "dual_bound": None,
            "nodes": nodes,
        },
        "point_check": {},
        "certificate_check": {},
    }


def infeasible_result(nodes=10, verified=True):
    status = "VERIFIED" if verified else "PARTIAL"
    returncode = 0 if verified else 11
    verified_claim = "infeasible" if verified else "-"
    return {
        "process": clean_process(),
        "parse_error": None,
        "verdict": {
            "status": "INFEASIBLE",
            "value": None,
            "dual_bound": None,
            "nodes": nodes,
        },
        "point_check": {},
        "certificate_check": {
            "process": clean_process(returncode=returncode, wall=0.01),
            "parsed": {
                "status": status,
                "census": (
                    f"CLAIMS verified={verified_claim} refuted=- "
                    "unbacked=infeasible"
                ),
                "claims": {
                    "verified": verified_claim,
                    "refuted": "-",
                    "unbacked": "-" if verified else "infeasible",
                },
            },
        },
    }


def scored(solved, nodes, *, eligible=True, status=None, cap=20_000):
    return {
        "evaluation": {
            "score_eligible": eligible,
            "solved": solved,
            "nodes": nodes,
            "node_cap": cap,
            "status": status or ("OPTIMAL" if solved else "UNKNOWN"),
        }
    }


def wall_scored(solved, wall, *, eligible=True, status=None):
    return {
        "evaluation": {
            "score_eligible": eligible,
            "solved": solved,
            "status": status or ("OPTIMAL" if solved else "UNKNOWN"),
            "outer_wall_sec": wall,
            "wrong_issues": [],
        }
    }


def put_repeated(indexed, split, name, config_id, record, *, metric=joint.NODE_METRIC):
    count = (
        joint.NODE_REPETITIONS
        if metric == joint.NODE_METRIC
        else joint.WALL_REPETITIONS
    )
    for repetition in range(count):
        indexed[
            joint.run_key(split, name, config_id, repetition, metric)
        ] = dict(record)


def protocol_run(
    split,
    name,
    config_id,
    solved,
    nodes,
    repetition=0,
    *,
    metric=joint.NODE_METRIC,
    wall=1.0,
    pair_order=None,
    order_position=None,
):
    return {
        "type": "run",
        "run_key": joint.run_key(split, name, config_id, repetition, metric),
        "metric": metric,
        "split": split,
        "repetition": repetition,
        "name": name,
        "config_id": config_id,
        "pair_order": pair_order,
        "order_position": order_position,
        **(
            scored(solved, nodes)
            if metric == joint.NODE_METRIC
            else wall_scored(solved, wall)
        ),
    }


class FrozenDesignTest(unittest.TestCase):
    def test_grid_is_the_preregistered_four_coordinate_product(self):
        self.assertEqual([len(values) for _, values in joint.COORDINATES], [4, 3, 3, 4])
        self.assertEqual(len(joint.GRID), 144)
        self.assertEqual(len({config.config_id for config in joint.GRID}), 144)
        self.assertEqual(joint.DEFAULT_GRID_CONFIG.env_dict(), {})
        for config in joint.GRID:
            self.assertEqual(len(config.coordinate_dict()), 4)
            self.assertEqual(
                len(config.env_dict()), len(set(config.env_dict())),
                config.config_id,
            )
            self.assertNotIn("AY_MILP_PRESOLVE_SHARE", config.env_dict())
        self.assertEqual(joint.COORDINATES[-1][0], "structural-presolve")

    def test_frozen_splits_are_unique_disjoint_and_keep_hard_controls(self):
        train, holdout = joint.load_splits(joint.TRAIN_LIST, joint.HOLDOUT_LIST)
        self.assertEqual(len(train), 5)
        self.assertEqual(len(holdout), 6)
        self.assertFalse(set(train) & set(holdout))
        self.assertIn("rout", holdout)
        self.assertIn("timtab1CUTS", holdout)
        self.assertIn("p2m2p1m1p0n100", holdout)

    def test_duplicate_or_overlapping_custom_split_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            train = Path(directory, "train.txt")
            holdout = Path(directory, "holdout.txt")
            train.write_text("a\na\n", encoding="utf-8")
            holdout.write_text("b\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "duplicate"):
                joint.load_splits(train, holdout)
            train.write_text("a\n", encoding="utf-8")
            holdout.write_text("a\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "overlap"):
                joint.load_splits(train, holdout)


class EnvironmentAndNodeGateTest(unittest.TestCase):
    def test_environment_is_scrubbed_then_explicitly_configured(self):
        env, posture = joint.configured_environment(
            {
                "PATH": "/bin",
                "AY_MILP_GMI_ROUNDS": "999",
                "AY_ROOT_CLOSURE": "1",
                "AY_BENCH_ROOT": "/private/corpus",
                "NY_NO_CNF_ROUTE": "1",
                "OMP_NUM_THREADS": "8",
            },
            {"AY_MILP_GMI_ROUNDS": "5"},
            20_000,
        )
        self.assertEqual(env["AY_MILP_GMI_ROUNDS"], "5")
        self.assertEqual(env["AY_MILP_MAX_NODES"], "20000")
        self.assertEqual(env["OMP_NUM_THREADS"], "1")
        self.assertNotIn("AY_ROOT_CLOSURE", env)
        self.assertNotIn("AY_BENCH_ROOT", env)
        self.assertNotIn("NY_NO_CNF_ROUTE", env)
        self.assertEqual(
            posture["removed_ay_milp_environment"],
            {"AY_MILP_GMI_ROUNDS": "999"},
        )
        self.assertEqual(
            posture["configured_ay_milp_environment"],
            {
                "AY_MILP_GMI_ROUNDS": "5",
                "AY_MILP_MAX_NODES": "20000",
                "AY_MILP_TRACE": "1",
            },
        )
        self.assertEqual(
            posture["removed_non_milp_ay_environment_names"],
            ["AY_BENCH_ROOT", "AY_ROOT_CLOSURE"],
        )

    def test_production_wall_environment_has_no_node_or_trace_instrument(self):
        env, posture = joint.configured_environment(
            {"PATH": "/bin", "AY_MILP_MAX_NODES": "9", "NY_X": "1"},
            {"AY_MILP_GMI_ROUNDS": "5"},
            None,
            joint.WALL_METRIC,
        )
        self.assertEqual(posture["measurement_metric"], joint.WALL_METRIC)
        self.assertEqual(
            posture["configured_ay_milp_environment"],
            {"AY_MILP_GMI_ROUNDS": "5"},
        )
        self.assertNotIn("AY_MILP_MAX_NODES", env)
        self.assertNotIn("AY_MILP_TRACE", env)
        self.assertNotIn("NY_X", env)

    def test_exact_optimal_result_is_score_eligible(self):
        evaluated = joint.evaluate_node_run(
            optimal_result(),
            {"status": "OPTIMAL", "objective": 7.0},
            "minimize",
            20_000,
            TRACE_OK,
        )
        self.assertTrue(evaluated["solved"])
        self.assertTrue(evaluated["point_verified"])
        self.assertTrue(evaluated["score_eligible"])
        self.assertEqual(evaluated["nodes"], 10)

    def test_wrong_optimal_value_is_alarm_not_fast_arm(self):
        evaluated = joint.evaluate_node_run(
            optimal_result(value=6.0),
            {"status": "OPTIMAL", "objective": 7.0},
            "minimize",
            20_000,
            TRACE_OK,
        )
        self.assertFalse(evaluated["score_eligible"])
        self.assertTrue(evaluated["wrong_issues"])

    def test_infeasible_requires_independently_verified_claim(self):
        reference = {"status": "INFEASIBLE", "objective": None}
        accepted = joint.evaluate_node_run(
            infeasible_result(verified=True),
            reference,
            "minimize",
            20_000,
            TRACE_OK,
        )
        rejected = joint.evaluate_node_run(
            infeasible_result(verified=False),
            reference,
            "minimize",
            20_000,
            TRACE_OK,
        )
        self.assertTrue(accepted["solved"])
        self.assertTrue(accepted["score_eligible"])
        self.assertFalse(rejected["score_eligible"])
        self.assertTrue(
            any(
                "verified infeasible claim" in issue
                for issue in rejected["invalid_issues"]
            )
        )

    def test_unsolved_run_must_reach_deterministic_node_cap(self):
        reference = {"status": "OPTIMAL", "objective": 7.0}
        capped = joint.evaluate_node_run(
            unknown_result(20_000), reference, "minimize", 20_000, TRACE_OK
        )
        premature = joint.evaluate_node_run(
            unknown_result(19_999), reference, "minimize", 20_000, TRACE_OK
        )
        self.assertTrue(capped["score_eligible"])
        self.assertFalse(capped["solved"])
        self.assertFalse(premature["score_eligible"])
        self.assertIn("before the fixed node cap", premature["node_gate_issues"][0])

    def test_node_cap_stop_check_allows_only_one_node_overshoot(self):
        self.assertTrue(
            joint.evaluate_node_run(
                unknown_result(20_001),
                {"status": "OPTIMAL", "objective": 7.0},
                "minimize",
                20_000,
                TRACE_OK,
            )["score_eligible"]
        )
        too_many = joint.evaluate_node_run(
            unknown_result(20_002),
            {"status": "OPTIMAL", "objective": 7.0},
            "minimize",
            20_000,
            TRACE_OK,
        )
        self.assertFalse(too_many["score_eligible"])

    def test_traced_partial_presolve_is_ineligible(self):
        trace = {
            "inspected": True,
            "issues": ["root work was deadline-truncated (presolve-deadline)"],
            "matches": [{"kind": "presolve-deadline", "lines": []}],
        }
        evaluated = joint.evaluate_node_run(
            optimal_result(),
            {"status": "OPTIMAL", "objective": 7.0},
            "minimize",
            20_000,
            trace,
        )
        self.assertFalse(evaluated["score_eligible"])
        self.assertIn("deadline-truncated", evaluated["node_gate_issues"][0])


class AcceptanceTest(unittest.TestCase):
    def test_node_arm_requires_three_identical_repetitions(self):
        indexed = {}
        for repetition, nodes in enumerate((10, 10, 11)):
            indexed[
                joint.run_key(
                    "train", "a", joint.BASELINE_ID, repetition, joint.NODE_METRIC
                )
            ] = scored(True, nodes)
        aggregate = joint.aggregate_repetitions(
            indexed,
            metric=joint.NODE_METRIC,
            split="train",
            name="a",
            config_id=joint.BASELINE_ID,
        )
        self.assertIsNotNone(aggregate)
        self.assertFalse(aggregate["evaluation"]["score_eligible"])
        self.assertIn(
            "changed status", aggregate["evaluation"]["replication_issues"][0]
        )

    def test_missing_third_repetition_is_not_an_arm(self):
        indexed = {}
        for repetition in range(2):
            indexed[
                joint.run_key(
                    "train", "a", joint.BASELINE_ID, repetition, joint.NODE_METRIC
                )
            ] = scored(True, 10)
        self.assertIsNone(
            joint.aggregate_repetitions(
                indexed,
                metric=joint.NODE_METRIC,
                split="train",
                name="a",
                config_id=joint.BASELINE_ID,
            )
        )

    def test_wall_gate_rejects_any_per_case_median_slowdown(self):
        baseline = {
            "a": {
                "evaluation": {
                    "score_eligible": True,
                    "solved": True,
                    "median_outer_wall_sec": 1.0,
                }
            }
        }
        slower = {
            "a": {
                "evaluation": {
                    "score_eligible": True,
                    "solved": True,
                    "median_outer_wall_sec": 1.01,
                }
            }
        }
        comparison = joint.compare_wall_to_baseline(["a"], baseline, slower)
        self.assertFalse(comparison["accepted"])
        self.assertEqual(comparison["regressions"][0]["kind"], "slower-production-wall")

    def test_wall_schedule_is_exactly_order_balanced(self):
        selected = joint.GRID[-1].config_id
        rows = joint.wall_holdout_schedule(["a"], selected)
        baseline_positions = [
            position for _, config, _, _, position in rows if config == joint.BASELINE_ID
        ]
        candidate_positions = [
            position for _, config, _, _, position in rows if config == selected
        ]
        self.assertEqual(baseline_positions, [0, 1, 0, 1])
        self.assertEqual(candidate_positions, [1, 0, 1, 0])

    def test_lost_solve_and_per_case_node_increase_are_regressions(self):
        names = ["a", "b"]
        baseline = {"a": scored(True, 10), "b": scored(True, 20)}
        candidate = {"a": scored(False, 20_000), "b": scored(True, 21)}
        comparison = joint.compare_to_baseline(
            names, baseline, candidate, require_strict=True
        )
        self.assertFalse(comparison["accepted"])
        self.assertEqual(
            [row["kind"] for row in comparison["regressions"]],
            ["lost-solve", "more-nodes"],
        )

    def test_superset_coverage_and_node_reduction_pass(self):
        names = ["a", "b", "c"]
        baseline = {
            "a": scored(True, 10),
            "b": scored(False, 20_000),
            "c": scored(False, 20_000),
        }
        candidate = {
            "a": scored(True, 9),
            "b": scored(True, 15_000),
            "c": scored(False, 20_000),
        }
        comparison = joint.compare_to_baseline(
            names, baseline, candidate, require_strict=True
        )
        self.assertTrue(comparison["accepted"])
        self.assertEqual(comparison["coverage_gains"], ["b"])
        self.assertEqual([row["name"] for row in comparison["node_gains"]], ["a"])

    def test_heldout_tie_is_not_generalization(self):
        baseline = {"a": scored(True, 10)}
        tied = {"a": scored(True, 10)}
        comparison = joint.compare_to_baseline(
            ["a"], baseline, tied, require_strict=True
        )
        self.assertFalse(comparison["accepted"])
        self.assertFalse(comparison["strict_improvement"])

    def test_training_selection_uses_only_admissible_strict_winner(self):
        name = "train-case"
        indexed = {}
        put_repeated(indexed, "train", name, joint.BASELINE_ID, scored(True, 100))
        winner = joint.GRID[-1]
        for config in joint.GRID:
            nodes = 90 if config.config_id == winner.config_id else 100
            put_repeated(
                indexed, "train", name, config.config_id, scored(True, nodes)
            )
        selection = joint.training_selection(indexed, [name])
        self.assertEqual(selection["selected_config_id"], winner.config_id)
        self.assertEqual(selection["default_replication_issues"], [])

    def test_identical_default_replica_must_be_deterministic(self):
        name = "train-case"
        indexed = {}
        put_repeated(indexed, "train", name, joint.BASELINE_ID, scored(True, 100))
        for config in joint.GRID:
            nodes = 99 if config.config_id == joint.DEFAULT_GRID_CONFIG.config_id else 100
            put_repeated(
                indexed, "train", name, config.config_id, scored(True, nodes)
            )
        selection = joint.training_selection(indexed, [name])
        self.assertIsNone(selection["selected_config_id"])
        self.assertTrue(selection["default_replication_issues"])

    def test_ineligible_training_baseline_is_incomplete_not_rejection(self):
        name = "train-case"
        indexed = {}
        put_repeated(
            indexed,
            "train",
            name,
            joint.BASELINE_ID,
            scored(False, 10, eligible=False),
        )
        for config in joint.GRID:
            put_repeated(
                indexed,
                "train",
                name,
                config.config_id,
                scored(False, 20_000),
            )
        selection = joint.training_selection(indexed, [name])
        self.assertIsNone(selection["selected_config_id"])
        self.assertTrue(selection["baseline_issues"])
        final = joint.final_summary(
            [], indexed, selection, None, [name], ["holdout"]
        )
        self.assertEqual(joint.final_exit_code(final), 2)


class JsonlTest(unittest.TestCase):
    def test_artifact_digest_tampering_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            artifact = root / "raw.txt"
            artifact.write_text("original", encoding="utf-8")
            identity = {
                "exists": True,
                "path": "raw.txt",
                "size_bytes": len(b"original"),
                "sha256": hashlib.sha256(b"original").hexdigest(),
            }
            self.assertEqual(
                joint.validate_artifact_identity(identity, root, "raw"),
                artifact.resolve(),
            )
            artifact.write_text("tampered", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "digest changed"):
                joint.validate_artifact_identity(identity, root, "raw")

    def test_append_load_and_resume_index(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory, "campaign.jsonl")
            joint.append_jsonl(
                path,
                {"type": "header", "schema": joint.SCHEMA},
                exclusive=True,
            )
            run = {
                "type": "run",
                "run_key": "train|a|baseline",
                "evaluation": {},
            }
            joint.append_jsonl(path, run)
            records = joint.load_jsonl(path)
            self.assertEqual(joint.index_records(records), {run["run_key"]: run})

    def test_duplicate_run_key_fails_closed(self):
        run = {"type": "run", "run_key": "train|a|baseline"}
        with self.assertRaisesRegex(ValueError, "duplicate"):
            joint.index_records([run, dict(run)])

    def test_resume_discards_only_an_incomplete_final_line(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory, "campaign.jsonl")
            path.write_bytes(b'{"type":"header"}\n{"type":"run"')
            with contextlib.redirect_stderr(io.StringIO()):
                records = joint.load_jsonl(path, repair_trailing=True)
            self.assertEqual(records, [{"type": "header"}])
            self.assertEqual(path.read_bytes(), b'{"type":"header"}\n')

    def test_malformed_complete_line_is_never_repaired(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory, "campaign.jsonl")
            path.write_bytes(b'{"type":"header"}\n{bad}\n')
            with self.assertRaisesRegex(ValueError, "malformed JSONL"):
                joint.load_jsonl(path, repair_trailing=True)
            self.assertEqual(path.read_bytes(), b'{"type":"header"}\n{bad}\n')

    def test_holdout_cannot_precede_sealed_training_selection(self):
        records = [
            {"type": "header"},
            protocol_run("holdout", "h", joint.BASELINE_ID, True, 10),
        ]
        with self.assertRaisesRegex(ValueError, "before training selection"):
            joint.validate_record_protocol(records, ["t"], ["h"])

    def test_selection_cannot_be_written_before_complete_grid(self):
        records = [
            {"type": "header"},
            {"type": "selection", "selected_config_id": None},
        ]
        with self.assertRaisesRegex(ValueError, "repeated training grid"):
            joint.validate_record_protocol(records, ["t"], ["h"])

    def test_production_wall_cannot_run_without_node_admission(self):
        train = ["t"]
        winner = joint.GRID[-1]
        records = [{"type": "header"}]
        indexed = {}
        for name, config_id, repetition in joint.training_node_schedule(train):
            nodes = 90 if config_id == winner.config_id else 100
            record = protocol_run(
                "train", name, config_id, True, nodes, repetition
            )
            records.append(record)
            indexed[record["run_key"]] = record
        records.append(
            joint.selection_record(joint.training_selection(indexed, train))
        )
        records.append(
            protocol_run(
                "holdout",
                "h",
                joint.BASELINE_ID,
                True,
                0,
                metric=joint.WALL_METRIC,
                pair_order="baseline-first",
                order_position=0,
            )
        )
        with self.assertRaisesRegex(ValueError, "before node admission"):
            joint.validate_record_protocol(records, train, ["h"])

    def test_complete_sealed_campaign_recomputes_exactly(self):
        train = ["t"]
        holdout = ["h"]
        winner = joint.GRID[-1]
        records = [{"type": "header"}]
        indexed = {}
        for name, config_id, repetition in joint.training_node_schedule(train):
            nodes = 90 if config_id == winner.config_id else 100
            record = protocol_run(
                "train", name, config_id, True, nodes, repetition
            )
            records.append(record)
            indexed[record["run_key"]] = record
        selection = joint.selection_record(joint.training_selection(indexed, train))
        records.append(selection)
        for name, config_id, repetition in joint.holdout_node_schedule(
            holdout, winner.config_id
        ):
            nodes = 100 if config_id == joint.BASELINE_ID else 80
            record = protocol_run(
                "holdout", name, config_id, True, nodes, repetition
            )
            records.append(record)
            indexed[record["run_key"]] = record
        admission = joint.wall_admission_record(
            records, indexed, selection, train, holdout
        )
        records.append(admission)
        self.assertTrue(admission["admitted"])
        for name, config_id, repetition, pair_order, position in joint.wall_holdout_schedule(
            holdout, winner.config_id
        ):
            wall = 2.0 if config_id == joint.BASELINE_ID else 1.0
            record = protocol_run(
                "holdout",
                name,
                config_id,
                True,
                0,
                repetition,
                metric=joint.WALL_METRIC,
                wall=wall,
                pair_order=pair_order,
                order_position=position,
            )
            records.append(record)
            indexed[record["run_key"]] = record
        final = joint.final_summary(
            records, indexed, selection, admission, train, holdout
        )
        records.append(final)
        joint.validate_record_protocol(records, train, holdout)
        joint.validate_derived_records(records, train, holdout)
        self.assertTrue(final["accepted"])


if __name__ == "__main__":
    unittest.main()
