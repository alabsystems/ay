#!/usr/bin/env python3
# ay-script: continuous-benchmark-tests
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import argparse
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

from scripts import continuous_benchmark as campaign


def git(repo: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", *args],
        cwd=repo,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
    )
    return completed.stdout.strip()


class ContinuousBenchmarkTests(unittest.TestCase):
    def test_checked_in_manifests_parse(self) -> None:
        root = Path(__file__).resolve().parents[2]
        lanes = campaign.load_toml(root / "benchmarks/continuous-lanes.toml")
        self.assertEqual(lanes["interval_hours"], 4)
        self.assertGreaterEqual(len(lanes["lane"]), 10)

    def test_status_publication_branch_must_be_excluded_from_integration(self) -> None:
        root = Path(__file__).resolve().parents[2]
        manifest = campaign.load_toml(
            root / "benchmarks" / "continuous-lanes.toml"
        )
        manifest["git"]["exclude"] = []
        with self.assertRaisesRegex(campaign.CampaignError, "publication branch"):
            campaign.validate_lane_manifest(
                manifest,
                root / "benchmarks" / "continuous-2025-2026.toml",
            )

    def test_competition_summary_tracks_winner_target_gap(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            catalog = Path(temporary) / "catalog.toml"
            catalog.write_text(
                "schema_version = 1\n"
                "[[track]]\n"
                'id = "known"\n'
                'competition = "satcomp"\n'
                'status = "final"\n'
                'readiness = "ready"\n'
                'ay_adapter_status = "ready"\n'
                'official_score_direction = "minimize"\n'
                'winner_name = "reference"\n'
                "winner_score = 12.5\n"
                "ay_retroactive_win = true\n"
                "[[track]]\n"
                'id = "pending-target"\n'
                'competition = "smtcomp"\n'
                'status = "final"\n'
                'readiness = "ready"\n'
                'ay_adapter_status = "partial"\n'
                'official_score_direction = "mixed-lexicographic"\n'
            )
            targets = campaign.competition_summary(catalog)["winner_targets"]
            self.assertEqual(targets["ranked_final_tracks"], 2)
            self.assertEqual(targets["harvested"], 1)
            self.assertEqual(targets["pending"], 1)
            self.assertEqual(targets["ay_verified_retroactive_wins"], 1)

    def test_checked_in_canary_corpus_is_complete(self) -> None:
        root = Path(__file__).resolve().parents[2]
        count, errors = campaign.eval_corpus_preflight(
            root,
            "sat-continuous-canary",
        )
        self.assertEqual(count, 9)
        self.assertEqual(errors, [])

    def test_eval_corpus_preflight_checks_nested_list_entries(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            registry = root / "evals" / "registry"
            registry.mkdir(parents=True)
            (registry / "sat-fixture.yaml").write_text(
                "id: sat-fixture\n"
                "inputs:\n"
                "  benchmarks_dir: benchmarks/sat\n"
                "  list_file: benchmarks/sat/cases.txt\n"
            )
            benchmarks = root / "benchmarks" / "sat"
            benchmarks.mkdir(parents=True)
            (benchmarks / "present.cnf").write_text("p cnf 1 1\n1 0\n")
            (benchmarks / "cases.txt").write_text(
                "benchmarks/sat/present.cnf sat\n"
                "benchmarks/sat/missing.cnf unsat\n"
            )

            count, errors = campaign.eval_corpus_preflight(
                root,
                "sat-fixture",
            )
            self.assertEqual(count, 1)
            self.assertIn("1/2 benchmark input(s) are missing", " ".join(errors))

    def test_unreferenced_sat_corpus_requires_path_labels(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            registry = root / "evals" / "registry"
            registry.mkdir(parents=True)
            (registry / "sat-fixture.yaml").write_text(
                "id: sat-fixture\n"
                "inputs:\n"
                "  benchmarks_dir: benchmarks/sat\n"
            )
            benchmarks = root / "benchmarks" / "sat" / "canary"
            benchmarks.mkdir(parents=True)
            (benchmarks / "case.cnf").write_text("p cnf 1 1\n1 0\n")

            count, errors = campaign.eval_corpus_preflight(
                root,
                "sat-fixture",
            )
            self.assertEqual(count, 1)
            self.assertIn(
                "lack an authoritative sat/unsat path label",
                " ".join(errors),
            )

    def test_checked_in_small_qf_lra_proxy_is_not_admitted_as_full(self) -> None:
        root = Path(__file__).resolve().parents[2]
        manifest = campaign.load_toml(
            root / "benchmarks" / "continuous-lanes.toml"
        )
        lane = next(
            row for row in manifest["lane"] if row["id"] == "smtcomp-qf-lra"
        )
        blocker = campaign.lane_blocker(lane, root)
        self.assertIsNotNone(blocker)
        self.assertIn("at least 100 benchmarks", blocker)

    def test_numeric_alarm_is_fail_closed_for_wrong_counters(self) -> None:
        self.assertTrue(campaign.numeric_alarm({"score": {"wrong": 1}}))
        self.assertTrue(campaign.numeric_alarm({"disqualified": True}))
        self.assertTrue(campaign.numeric_alarm({"wrong_answers": ["x.cnf"]}))
        self.assertFalse(
            campaign.numeric_alarm(
                {"score": {"wrong": 0, "solved": 10, "total": 12}}
            )
        )

    def test_bounded_json_rejects_symlink_and_oversize(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            target = root / "target.json"
            target.write_text('{"ok": true}')
            link = root / "link.json"
            link.symlink_to(target)
            self.assertIsNone(campaign.read_json(link, None))
            self.assertIsNone(campaign.read_json(target, None, max_bytes=4))
            self.assertEqual(campaign.read_json(target, None), {"ok": True})

    def test_conflicted_branch_blocks_publication(self) -> None:
        branches = [
            campaign.BranchRecord("main", "a" * 40, "base"),
            campaign.BranchRecord("topic", "b" * 40, "conflicted"),
        ]
        self.assertFalse(campaign.integrations_clean(branches))
        branches[1].classification = "unique"
        self.assertTrue(campaign.integrations_clean(branches))
        branches[1].classification = "policy-review"
        self.assertFalse(campaign.integrations_clean(branches))

    def test_integration_control_plane_requires_review(self) -> None:
        self.assertTrue(
            campaign.integration_path_is_protected(
                "scripts/continuous_benchmark.py"
            )
        )
        self.assertTrue(
            campaign.integration_path_is_protected(".github/workflows/ci.yml")
        )
        self.assertTrue(campaign.integration_path_is_protected(".cargo/config.toml"))
        self.assertTrue(campaign.integration_path_is_protected("../outside"))
        self.assertTrue(
            campaign.integration_path_is_protected("reference/solver/check.py")
        )
        self.assertTrue(
            campaign.integration_path_is_protected("crates/ay-test-support/src/lib.rs")
        )
        self.assertTrue(
            campaign.integration_path_is_protected("evals/comparisons.toml")
        )
        self.assertTrue(
            campaign.integration_path_is_protected("crates/ay-proof/src/checker.rs")
        )
        self.assertFalse(
            campaign.integration_path_is_protected("crates/ay-sat/src/solver.rs")
        )

    def test_raw_git_paths_cannot_bypass_control_plane_quarantine(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary) / "repo"
            repo.mkdir()
            git(repo, "init", "-b", "main")
            git(repo, "config", "user.name", "Test")
            git(repo, "config", "user.email", "test@example.com")
            (repo / "base").write_text("base\n")
            git(repo, "add", "base")
            git(repo, "commit", "-m", "base")
            main = git(repo, "rev-parse", "HEAD")

            git(repo, "switch", "-c", "topic")
            hostile = repo / ".github" / "workflows" / "é\ninjected.yml"
            hostile.parent.mkdir(parents=True)
            hostile.write_text("name: hostile\n")
            git(repo, "add", ".")
            git(repo, "commit", "-m", "hostile path")
            topic = git(repo, "rev-parse", "HEAD")

            changes = campaign.integration_policy_changes(repo, main, topic)
            self.assertEqual(changes, [".github/workflows/é\ninjected.yml"])
            records = campaign.classify_branches(
                repo,
                "origin",
                "main",
                {"main": main, "topic": topic},
                [],
            )
            self.assertEqual(records[1].classification, "policy-review")

    def test_repair_path_enumeration_preserves_unicode_and_newlines(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            git(repo, "init", "-b", "main")
            git(repo, "config", "user.name", "Test")
            git(repo, "config", "user.email", "test@example.com")
            (repo / "base").write_text("base\n")
            git(repo, "add", "base")
            git(repo, "commit", "-m", "base")
            hostile = repo / ".github" / "workflows" / "é\nrepair.yml"
            hostile.parent.mkdir(parents=True)
            hostile.write_text("name: hostile\n")
            self.assertEqual(
                campaign.changed_paths(repo),
                [".github/workflows/é\nrepair.yml"],
            )
            self.assertEqual(
                campaign.protected_repair_changes(repo),
                [".github/workflows/é\nrepair.yml"],
            )

    def test_repair_residue_detects_ignored_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            git(repo, "init", "-b", "main")
            git(repo, "config", "user.name", "Test")
            git(repo, "config", "user.email", "test@example.com")
            (repo / ".gitignore").write_text("*.generated\n")
            git(repo, "add", ".gitignore")
            git(repo, "commit", "-m", "ignore generated")
            self.assertFalse(campaign.repair_residue(repo))
            (repo / "solver.generated").write_text("affects build\n")
            self.assertTrue(campaign.repair_residue(repo))

    @unittest.skipUnless(os.name == "posix", "Unix permission check")
    def test_state_root_is_private(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "state"
            campaign.prepare_state_root(root)
            self.assertEqual(root.stat().st_mode & 0o077, 0)

    def test_cycle_deadline_leaves_systemd_cleanup_headroom(self) -> None:
        root = Path(__file__).resolve().parents[2]
        unit = (
            root
            / "deploy"
            / "systemd"
            / "ay-continuous-benchmark.service"
        ).read_text()
        self.assertIn("TimeoutStartSec=3h45min", unit)
        self.assertEqual(campaign.DEFAULT_CYCLE_TIMEOUT_SEC, 3 * 3600 + 30 * 60)
        exec_start = next(
            line for line in unit.splitlines() if line.startswith("ExecStart=")
        )
        self.assertNotIn("--repair-with-codex", exec_start)
        self.assertNotIn("--publish-issue", exec_start)
        self.assertIn("--publish-status-branch", exec_start)
        controller = (root / "scripts" / "continuous_benchmark.py").read_text()
        self.assertGreater(
            controller.rfind("disarm_cycle_deadline(previous_signal_handlers)"),
            controller.rfind("atomic_json(state_path, next_state)"),
        )

    def test_laboratory_repair_cannot_publish_or_push(self) -> None:
        common = {
            "repo": ".",
            "state_root": ".state",
            "repair_with_codex": True,
            "publish_issue": False,
            "push": False,
        }
        for forbidden in ("push", "publish_issue"):
            args = argparse.Namespace(**{**common, forbidden: True})
            with self.assertRaisesRegex(
                campaign.CampaignError,
                "laboratory-only",
            ):
                campaign.cycle(args)

    def test_cycle_interrupt_terminates_active_process_group(self) -> None:
        campaign._ACTIVE_CHILD_PROCESS_GROUP = 12345
        with (
            mock.patch.object(campaign.os, "killpg") as killpg,
            self.assertRaises(campaign.CycleInterrupted),
        ):
            campaign.cycle_interrupt_handler(campaign.signal.SIGTERM, None)
        killpg.assert_called_once_with(12345, campaign.signal.SIGTERM)
        self.assertIsNone(campaign._ACTIVE_CHILD_PROCESS_GROUP)

    def test_run_command_reaps_child_when_wait_is_interrupted(self) -> None:
        class FakeProcess:
            pid = 23456

            def __init__(self) -> None:
                self.wait_calls = 0

            def wait(self, *, timeout=None):
                del timeout
                self.wait_calls += 1
                if self.wait_calls == 1:
                    raise campaign.CampaignError("injected interrupt")
                return 0

            def poll(self):
                return None if self.wait_calls < 2 else 0

        fake = FakeProcess()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with (
                mock.patch.object(
                    campaign.subprocess,
                    "Popen",
                    return_value=fake,
                ),
                mock.patch.object(campaign.os, "killpg") as killpg,
                self.assertRaises(campaign.CampaignError),
            ):
                campaign.run_command(
                    ["fake"],
                    root,
                    root / "command.log",
                )
        killpg.assert_called_once_with(fake.pid, campaign.signal.SIGTERM)
        self.assertEqual(fake.wait_calls, 2)
        self.assertIsNone(campaign._ACTIVE_CHILD_PROCESS_GROUP)

    def test_scoreboard_tracks_solve_rate(self) -> None:
        outcome = campaign.LaneOutcome(
            lane_id="sat",
            eval_id="sat-dev",
            status="passed",
            detail="scorecard recorded",
            scorecard_path="/evidence/scorecard.json",
            scorecard={"results": [{"score": {"solved": 8, "total": 10, "wrong": 0}}]},
        )
        scoreboard = campaign.update_scoreboard(
            {},
            [outcome],
            current_run="20260723T000000Z",
            tested_sha="a" * 40,
            promote_scores=True,
        )
        self.assertEqual(scoreboard["sat"]["score"]["solved_rate"], 0.8)

    def test_lane_shards_track_coverage_without_mixed_sha_aggregation(self) -> None:
        shard_base = {
            "requested_index": 0,
            "shard_index": 0,
            "shard_size": 2,
            "shard_count": 2,
            "corpus_benchmark_count": 4,
            "selected_benchmark_count": 2,
            "corpus_path_inventory_sha256": "sha256:" + "1" * 64,
            "selector": "sorted-normalized-id-contiguous-v1",
        }
        first = campaign.LaneOutcome(
            lane_id="rolling",
            eval_id="fixture",
            status="passed",
            detail="passed",
            shard=shard_base,
        )
        progress = campaign.update_lane_shards(
            {},
            [first],
            current_run="first",
            tested_sha="a" * 40,
            promote=True,
        )
        self.assertEqual(progress["rolling"]["next_index"], 1)
        self.assertEqual(progress["rolling"]["completed_indices"], [0])

        second = campaign.LaneOutcome(
            lane_id="rolling",
            eval_id="fixture",
            status="passed",
            detail="passed",
            shard={
                **shard_base,
                "requested_index": 1,
                "shard_index": 1,
            },
        )
        progress = campaign.update_lane_shards(
            progress,
            [second],
            current_run="second",
            tested_sha="b" * 40,
            promote=True,
        )
        lane = progress["rolling"]
        self.assertEqual(lane["completed_sweeps"], 1)
        self.assertEqual(lane["completed_indices"], [])
        self.assertFalse(
            lane["last_completed_sweep"]["single_candidate_sha"]
        )
        self.assertIn("forbidden-across-shards", lane["score_aggregation"])

        changed_inventory = campaign.LaneOutcome(
            lane_id="rolling",
            eval_id="fixture",
            status="passed",
            detail="passed",
            shard={
                **shard_base,
                "corpus_path_inventory_sha256": "sha256:" + "2" * 64,
            },
        )
        progress = campaign.update_lane_shards(
            progress,
            [changed_inventory],
            current_run="third",
            tested_sha="c" * 40,
            promote=True,
        )
        self.assertEqual(progress["rolling"]["completed_sweeps"], 0)
        self.assertEqual(progress["rolling"]["completed_indices"], [0])

    def test_campaign_state_rejects_malformed_shard_cursor(self) -> None:
        with self.assertRaisesRegex(campaign.CampaignError, "shard cursor"):
            campaign.validate_campaign_state(
                {
                    "scoreboard": {},
                    "lane_shards": {"rolling": {"next_index": -1}},
                }
            )

    def test_scorecard_and_native_shard_metadata_must_match(self) -> None:
        shard = {
            "requested_index": 0,
            "shard_index": 0,
            "shard_size": 1,
            "shard_count": 2,
            "corpus_benchmark_count": 2,
            "selected_benchmark_count": 1,
            "corpus_path_inventory_sha256": "sha256:" + "1" * 64,
            "selector": "sorted-normalized-id-contiguous-v1",
        }
        score = {
            "par2_total": 1.0,
            "par2_avg": 1.0,
            "solved": 1,
            "solved_sat": 1,
            "solved_unsat": 0,
            "unsolved": 0,
            "wrong": 0,
            "disqualified": False,
            "total": 1,
            "timeout_sec": 5.0,
            "wrong_answers": [],
        }
        errors = campaign.scorecard_evidence_errors(
            {
                "results": [
                    {
                        "eval_id": "sat",
                        "score": score,
                        "shard": {**shard, "shard_index": 1},
                    }
                ]
            },
            {
                "domain": "sat",
                "benchmark_count": 1,
                "timeout_sec": 5.0,
                "shard": shard,
                "ay_sha256": "sha256:" + "a" * 64,
                "solver_launcher_sha256": "sha256:" + "b" * 64,
                "candidate_sha256": "sha256:" + "c" * 64,
                "candidate_size_bytes": 1,
                "candidate_sandbox": "candidate-only-bubblewrap-v1",
                "resource_plan": {
                    "jobs": 1,
                    "memlimit_mb_per_child": 1024,
                    "nbcore_per_child": 1,
                },
                "resource_enforcement": "ay-resource-v1:ay-memory",
            },
            eval_id="sat",
            official=False,
        )
        self.assertIn("shard metadata", " ".join(errors))

    def test_markdown_escapes_hostile_branch_fields(self) -> None:
        packet = {
            "run_id": "test",
            "status": "failed",
            "branches": [
                {
                    "name": "topic|forged\n| row |",
                    "sha": "a" * 40,
                    "classification": "policy-review",
                    "detail": "`closed` | forged",
                }
            ],
            "benchmarks": [],
            "scoreboard": {},
            "competition_catalog": {"total": 0, "statuses": {}},
        }
        markdown = campaign.render_markdown(packet)
        self.assertNotIn("topic|forged", markdown)
        self.assertNotIn("`closed`", markdown)
        self.assertIn("topic&#124;forged<br>", markdown)
        self.assertIn("&#96;closed&#96;", markdown)

    def test_repair_protected_paths(self) -> None:
        self.assertTrue(campaign.repair_path_is_protected("benchmarks/sat/x.cnf"))
        self.assertTrue(
            campaign.repair_path_is_protected(".github/workflows/ci.yml")
        )
        self.assertTrue(campaign.repair_path_is_protected(".cargo/config.toml"))
        self.assertTrue(campaign.repair_path_is_protected("crates/ay/build.rs"))
        self.assertTrue(campaign.repair_path_is_protected("crates/ay-proof/src/lib.rs"))
        self.assertTrue(campaign.repair_path_is_protected("crates/ay/Cargo.toml"))
        self.assertFalse(campaign.repair_path_is_protected("crates/ay-sat/src/solver.rs"))

    def test_native_evidence_rejects_unverified_definitive_answer(self) -> None:
        summary = campaign.native_evidence_summary(
            {
                "environment": {"git_commit": "a" * 40, "git_dirty": False},
                "settings": {
                    "timeout_sec": 5.0,
                    "benchmark_count": 1,
                    "runs": 1,
                    "resource_plan": {"jobs": 1, "memlimit_mb": 1024},
                    "resource_enforcement": "ay --memory",
                },
                "items": [
                    {
                        "file": "unknown.smt2",
                        "benchmark_path": "unknown.smt2",
                        "benchmark_content_hash": "sha256:x",
                        "expected": None,
                        "expected_source": "none",
                        "result": "sat",
                    }
                ],
            }
        )
        self.assertIsNotNone(summary)
        self.assertEqual(summary["unverified_definitive"], 1)
        self.assertIn("definitive answer", " ".join(summary["evidence_errors"]))
        self.assertIsNotNone(summary["corpus_identity_sha256"])

    def test_native_evidence_validates_execution_contract_and_harness_errors(
        self,
    ) -> None:
        summary = campaign.native_evidence_summary(
            {
                "environment": {
                    "git_commit": "a" * 40,
                    "git_dirty": False,
                    "ay_sha256": "sha256:" + "a" * 64,
                    "ay_build_stamp": "test",
                },
                "settings": {
                    "timeout_sec": 10.0,
                    "benchmark_count": 2,
                    "runs": 2,
                    "domain": "smt",
                    "resource_plan": {"jobs": 1, "memlimit_mb": 1024},
                    "resource_enforcement": "ay-resource-v1:ay-memory",
                },
                "items": [
                    {
                        "file": "bad.smt2",
                        "benchmark_path": "bad.smt2",
                        "benchmark_content_hash": "sha256:x",
                        "expected": "sat",
                        "expected_source": "manifest",
                        "result": "error",
                        "harness_error": "proof preparation failed",
                    }
                ],
            },
            expected_runs=1,
            expected_timeout_sec=5.0,
        )
        self.assertIsNotNone(summary)
        errors = " ".join(summary["evidence_errors"])
        self.assertIn("benchmark_count", errors)
        self.assertIn("lane runs", errors)
        self.assertIn("lane timeout", errors)
        self.assertIn("harness error", errors)
        self.assertIn("explicit error", errors)
        self.assertEqual(summary["timeout_sec"], 10.0)
        self.assertEqual(summary["runs"], 2)

    def test_agreeing_reference_requires_preserved_provenance(self) -> None:
        summary = campaign.native_evidence_summary(
            {
                "environment": {
                    "git_commit": "a" * 40,
                    "git_dirty": False,
                    "ay_sha256": "sha256:" + "a" * 64,
                    "ay_build_stamp": "test",
                },
                "settings": {
                    "timeout_sec": 5.0,
                    "benchmark_count": 1,
                    "runs": 1,
                    "domain": "smt",
                    "resource_plan": {"jobs": 1, "memlimit_mb": 1024},
                    "resource_enforcement": "ay-resource-v1:ay-memory",
                },
                "items": [
                    {
                        "file": "unknown.smt2",
                        "benchmark_path": "unknown.smt2",
                        "benchmark_content_hash": "sha256:x",
                        "expected": None,
                        "expected_source": "none",
                        "result": "sat",
                    }
                ],
                "reference_comparisons": [
                    {
                        "reference_solver": "z3",
                        "items": [
                            {"file": "unknown.smt2", "agreement": "agree"}
                        ],
                    }
                ],
                "references": [],
            }
        )
        self.assertIsNotNone(summary)
        self.assertIn(
            "lacks provenance",
            " ".join(summary["evidence_errors"]),
        )

    def test_scorecard_count_must_match_native_evidence(self) -> None:
        errors = campaign.scorecard_evidence_errors(
            {
                "results": [
                    {
                        "eval_id": "sat",
                        "score": {"total": 2, "solved": 2},
                    }
                ]
            },
            {
                "benchmark_count": 3,
                "ay_sha256": "sha256:" + "a" * 64,
                "resource_plan": {
                    "jobs": 1,
                    "memlimit_mb_per_child": 1024,
                    "nbcore_per_child": 1,
                },
                "resource_enforcement": "ay-resource-v1:ay-memory",
            },
            eval_id="sat",
            official=False,
        )
        self.assertIn("does not match", " ".join(errors))

    def test_score_shape_rejects_malformed_soundness_counters(self) -> None:
        score = {
            "par2_total": 1.0,
            "par2_avg": 1.0,
            "solved": 1,
            "solved_sat": 1,
            "solved_unsat": 0,
            "unsolved": 0,
            "wrong": "zero",
            "disqualified": False,
            "total": 1,
            "timeout_sec": 5.0,
            "wrong_answers": [],
        }
        errors = campaign.score_shape_errors(score, "sat")
        self.assertIn("wrong", " ".join(errors))

    def test_score_timeout_must_match_native_evidence(self) -> None:
        score = {
            "par2_total": 1.0,
            "par2_avg": 1.0,
            "solved": 1,
            "solved_sat": 1,
            "solved_unsat": 0,
            "unsolved": 0,
            "wrong": 0,
            "disqualified": False,
            "total": 1,
            "timeout_sec": 10.0,
            "wrong_answers": [],
        }
        errors = campaign.scorecard_evidence_errors(
            {"results": [{"eval_id": "sat", "score": score}]},
            {
                "domain": "sat",
                "benchmark_count": 1,
                "timeout_sec": 5.0,
                "ay_sha256": "sha256:" + "a" * 64,
                "solver_launcher_sha256": "sha256:" + "b" * 64,
                "candidate_sha256": "sha256:" + "c" * 64,
                "candidate_size_bytes": 1,
                "candidate_sandbox": "candidate-only-bubblewrap-v1",
                "resource_plan": {
                    "jobs": 1,
                    "memlimit_mb_per_child": 1024,
                    "nbcore_per_child": 1,
                },
                "resource_enforcement": "ay-resource-v1:ay-memory",
            },
            eval_id="sat",
            official=False,
        )
        self.assertIn("does not match native timeout", " ".join(errors))

    @unittest.skipUnless(os.name == "posix", "symlink check")
    def test_native_evidence_rejects_symlinked_run(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            external = root / "external"
            external.mkdir()
            (external / "results.json").write_text("{}")
            eval_root = root / "results" / "eval"
            eval_root.mkdir(parents=True)
            (eval_root / "forged").symlink_to(external, target_is_directory=True)
            path, summary = campaign.new_native_evidence(
                root / "results",
                "eval",
                set(),
                expected_commit="a" * 40,
            )
            self.assertIsNone(path)
            self.assertIsNone(summary)

    def test_blocked_canary_fails_closed(self) -> None:
        selected = [{"id": "canary", "kind": "canary", "eval_id": "sat"}]
        blocked = campaign.LaneOutcome(
            lane_id="canary",
            eval_id="sat",
            status="blocked",
            detail="missing corpus",
        )
        self.assertFalse(campaign.canaries_clean(selected, [blocked]))

    def test_official_marker_cannot_bypass_adapter_block(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.assertIn(
                "official replay",
                campaign.lane_blocker(
                    {
                        "id": "misclassified",
                        "kind": "rolling",
                        "official": True,
                    },
                    root,
                ),
            )
            manifest = {
                "build": {"commands": [["true"]]},
                "lane": [
                    {
                        "id": "canary",
                        "kind": "canary",
                        "eval_id": "canary",
                        "official": False,
                    },
                    {
                        "id": "misclassified",
                        "kind": "rolling",
                        "eval_id": "official-eval",
                        "official": True,
                    },
                ],
            }
            with self.assertRaises(campaign.CampaignError):
                campaign.validate_lane_manifest(
                    manifest,
                    root / "missing-catalog.toml",
                )

    def test_rotation_skips_blocked_lane(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "ready").mkdir()
            manifest = {
                "lane": [
                    {
                        "id": "canary",
                        "kind": "canary",
                        "eval_id": "sat-canary",
                    },
                    {
                        "id": "blocked",
                        "kind": "rolling",
                        "eval_id": "missing",
                        "requires_paths": ["missing"],
                    },
                    {
                        "id": "ready",
                        "kind": "rolling",
                        "eval_id": "ready",
                        "requires_paths": ["ready"],
                    },
                ]
            }
            with mock.patch.object(
                campaign,
                "eval_corpus_preflight",
                return_value=(1, []),
            ):
                selected, blocked, cursor, official_cursor = campaign.select_lanes(
                    manifest,
                    {"rolling_cursor": 0},
                    root,
                    smoke_only=False,
                    include_official=False,
                )
            self.assertEqual([row["id"] for row in selected], ["canary", "ready"])
            self.assertEqual([row.lane_id for row in blocked], ["blocked"])
            self.assertEqual(cursor, 0)
            self.assertEqual(official_cursor, 0)

    def test_rotation_uses_persisted_shard_cursor_without_mutating_manifest(
        self,
    ) -> None:
        manifest_lane = {
            "id": "rolling",
            "kind": "rolling",
            "eval_id": "fixture",
            "shard_size": 64,
        }
        manifest = {"lane": [manifest_lane]}
        with (
            tempfile.TemporaryDirectory() as temporary,
            mock.patch.object(campaign, "lane_blocker", return_value=None),
        ):
            selected, _, _, _ = campaign.select_lanes(
                manifest,
                {
                    "rolling_cursor": 0,
                    "lane_shards": {"rolling": {"next_index": 7}},
                },
                Path(temporary),
                smoke_only=False,
                include_official=False,
            )
        self.assertEqual(selected[0]["_shard_index"], 7)
        self.assertNotIn("_shard_index", manifest_lane)

    def test_official_request_scans_blocked_and_requires_a_pass(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "ready").mkdir()
            manifest = {
                "lane": [
                    {"id": "canary", "kind": "canary", "eval_id": "canary"},
                    {
                        "id": "official-blocked",
                        "kind": "official",
                        "eval_id": "blocked",
                        "enabled": False,
                    },
                    {
                        "id": "official-ready",
                        "kind": "official",
                        "eval_id": "ready",
                        "requires_paths": ["ready"],
                    },
                ]
            }
            selected, blocked, _, cursor = campaign.select_lanes(
                manifest,
                {"official_cursor": 0},
                root,
                smoke_only=True,
                include_official=True,
            )
            self.assertEqual(
                [lane["id"] for lane in selected],
                ["canary"],
            )
            self.assertEqual(
                [outcome.lane_id for outcome in blocked],
                ["official-blocked", "official-ready"],
            )
            self.assertEqual(cursor, 0)
            self.assertFalse(
                campaign.official_selection_clean(True, selected, blocked)
            )
            selected.append(manifest["lane"][2])
            passed = campaign.LaneOutcome(
                lane_id="official-ready",
                eval_id="ready",
                status="passed",
                detail="verified",
            )
            self.assertTrue(
                campaign.official_selection_clean(True, selected, [*blocked, passed])
            )

    def test_retention_preserves_official_runs(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            state = Path(temporary)
            runs = state / "runs"
            names = [
                "20260720T000000Z",
                "20260720T040000Z",
                "20260720T080000Z",
            ]
            for name in names:
                path = runs / name
                path.mkdir(parents=True)
                (path / "packet.json").write_text(
                    json.dumps(
                        {"official_requested": name == "20260720T000000Z"}
                    )
                )
            removed = campaign.prune_run_history(
                state,
                max_runs=2,
                current_run="20260720T080000Z",
            )
            self.assertEqual(removed, ["20260720T040000Z"])
            self.assertTrue((runs / "20260720T000000Z").is_dir())

    def test_retention_preserves_scoreboard_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            state = Path(temporary)
            runs = state / "runs"
            for name in (
                "20260720T000000Z",
                "20260720T040000Z",
                "20260720T080000Z",
            ):
                path = runs / name
                path.mkdir(parents=True)
                (path / "packet.json").write_text("{}")
            removed = campaign.prune_run_history(
                state,
                max_runs=2,
                current_run="20260720T080000Z",
                preserved_run_ids={"20260720T000000Z"},
            )
            self.assertEqual(removed, ["20260720T040000Z"])
            self.assertEqual(
                campaign.scoreboard_run_ids(
                    {"sat": {"score_run_id": "20260720T000000Z"}}
                ),
                {"20260720T000000Z"},
            )

    def test_retention_prunes_controller_failure_packets(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            state = Path(temporary)
            runs = state / "runs"
            failed = "20260720T000000Z-controller-123"
            current = "20260720T040000Z"
            for name in (failed, current):
                path = runs / name
                path.mkdir(parents=True)
                (path / "packet.json").write_text("{}")
            removed = campaign.prune_run_history(
                state,
                max_runs=1,
                current_run=current,
            )
            self.assertEqual(removed, [failed])

    def test_control_plane_failure_updates_latest_packet(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            state = root / "state"
            campaign.prepare_state_root(state)
            (state / "state.json").write_text(
                '{"scoreboard": ["malformed"], "issue_number": "bad"}'
            )
            packet = campaign.record_control_plane_failure(
                root,
                state,
                "origin",
                publish=False,
                official_requested=True,
                error=campaign.CampaignError("fetch failed"),
            )
            latest = json.loads((state / "latest.json").read_text())
            self.assertEqual(latest["run_id"], packet["run_id"])
            self.assertEqual(latest["status"], "failed")
            self.assertEqual(latest["phase"], "controller-bootstrap")
            self.assertIn("fetch failed", latest["error"])
            self.assertEqual(latest["scoreboard"], {})
            self.assertTrue(latest["official_requested"])
            self.assertEqual(
                latest["score_claim_class"],
                "official-replay-requested",
            )

    def test_checkpoint_does_not_swallow_cycle_interrupt(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            run_dir = root / "runs" / "run"
            state_path = root / "state.json"
            packet = {
                "run_id": "run",
                "status": "running",
                "branches": [],
                "benchmarks": [],
                "scoreboard": {},
                "competition_catalog": {"total": 0, "statuses": {}},
            }
            with (
                mock.patch.object(
                    campaign,
                    "publish_issue",
                    side_effect=lambda *_args, **_kwargs: (
                        campaign.cycle_interrupt_handler(
                            campaign.signal.SIGALRM,
                            None,
                        )
                    ),
                ),
                self.assertRaises(campaign.CycleInterrupted),
            ):
                campaign.checkpoint_progress(
                    root,
                    "origin",
                    root,
                    run_dir,
                    state_path,
                    packet,
                    {},
                    publish=True,
                )

    def test_checkpoint_publication_failure_preserves_cycle_status(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            run_dir = root / "runs" / "run"
            run_dir.mkdir(parents=True)
            state_path = root / "state.json"
            packet = {
                "run_id": "run",
                "status": "passed",
                "branches": [],
                "benchmarks": [],
                "scoreboard": {},
                "competition_catalog": {"total": 0, "statuses": {}},
            }
            with mock.patch.object(
                campaign,
                "publish_issue",
                side_effect=campaign.CampaignError("issues forbidden"),
            ):
                published = campaign.checkpoint_progress(
                    root,
                    "origin",
                    root,
                    run_dir,
                    state_path,
                    packet,
                    {},
                    publish=True,
                    persist_state=False,
                )

            self.assertFalse(published)
            self.assertEqual(packet["status"], "passed")
            self.assertEqual(packet["publication"]["status"], "failed")
            self.assertIn("issues forbidden", packet["publication"]["error"])
            self.assertFalse(state_path.exists())

    def test_status_branch_publication_is_linear_and_checkout_free(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            remote = root / "remote.git"
            repo = root / "repo"
            remote.mkdir()
            repo.mkdir()
            git(remote, "init", "--bare")
            git(repo, "init", "-b", "main")
            git(repo, "config", "user.name", "Test")
            git(repo, "config", "user.email", "test@example.com")
            (repo / "base").write_text("base\n")
            git(repo, "add", "base")
            git(repo, "commit", "-m", "base")
            git(repo, "remote", "add", "origin", str(remote))
            git(repo, "push", "-u", "origin", "main")

            run_dir = root / "run"
            run_dir.mkdir()
            (run_dir / "packet.json").write_text('{"status":"running"}\n')
            (run_dir / "status.md").write_text("# running\n")
            first = campaign.publish_status_branch(
                repo,
                "origin",
                run_dir,
                "first",
            )
            self.assertEqual(
                git(remote, "show", f"{first}:latest.md"),
                "# running",
            )

            (run_dir / "packet.json").write_text('{"status":"passed"}\n')
            (run_dir / "status.md").write_text("# passed\n")
            second = campaign.publish_status_branch(
                repo,
                "origin",
                run_dir,
                "second",
            )
            self.assertEqual(
                git(remote, "rev-list", "--count", campaign.STATUS_BRANCH),
                "2",
            )
            self.assertEqual(
                git(remote, "show", f"{second}:latest.md"),
                "# passed",
            )
            self.assertEqual(git(repo, "status", "--porcelain"), "")

    def test_trusted_dependency_fetch_is_online_and_locked(self) -> None:
        record = campaign.CommandRecord(
            argv=["cargo", "fetch", "--locked"],
            cwd="/candidate",
            exit_code=0,
            elapsed_sec=0.1,
            log="/evidence/fetch.log",
        )
        with (
            mock.patch.object(campaign.shutil, "which", return_value="/bin/cargo"),
            mock.patch.object(campaign, "run_command", return_value=record) as run,
        ):
            actual = campaign.fetch_trusted_dependencies(
                Path("/candidate"),
                Path("/evidence"),
                timeout_sec=123,
            )

        self.assertEqual(actual, record)
        run.assert_called_once_with(
            ["/bin/cargo", "fetch", "--locked"],
            Path("/candidate"),
            Path("/evidence/gates/00-dependency-fetch.log"),
            env={"CARGO_NET_OFFLINE": "false"},
            timeout=123,
        )

    @unittest.skipUnless(
        os.name == "posix" and campaign.shutil.which("bwrap"),
        "bubblewrap is required",
    )
    def test_candidate_launcher_runs_version_in_isolation(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "fake-ay"
            source.write_text("#!/bin/sh\necho 'ay 0.0-test'\n")
            source.chmod(0o700)
            run_dir = root / "run"
            results = root / "results"
            run_dir.mkdir()
            results.mkdir()
            candidate = campaign.prepare_candidate_solver(
                source,
                run_dir,
                results,
                tested_sha="a" * 40,
                label="test",
            )
            if os.environ.get(campaign.BUILD_SANDBOX_MARKER) == "1":
                self.skipTest(
                    "live nested bubblewrap probe is unavailable inside the "
                    "candidate build sandbox"
                )
            completed = subprocess.run(
                [candidate["launcher_path"], "--version"],
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=10,
                check=False,
            )
            self.assertEqual(completed.returncode, 0, completed.stderr)
            self.assertIn("ay 0.0-test", completed.stdout)

    @unittest.skipUnless(
        os.name == "posix" and campaign.shutil.which("bwrap"),
        "bubblewrap is required",
    )
    def test_candidate_launcher_exposes_only_input_and_proof_staging(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protected = root / "protected-scorecard"
            protected.write_text("trusted")
            source = root / "fake-ay"
            source.write_text(
                "#!/usr/bin/python3\n"
                "import os\n"
                "from pathlib import Path\n"
                "import sys\n"
                f"protected = Path({str(protected)!r})\n"
                "if sys.argv[1:] == ['--version']:\n"
                "    print('ay 0.0-test')\n"
                "    raise SystemExit(0)\n"
                "if 'GH_TOKEN' in os.environ:\n"
                "    raise SystemExit(91)\n"
                "try:\n"
                "    protected.write_text('forged')\n"
                "except OSError:\n"
                "    pass\n"
                "proof = Path(sys.argv[sys.argv.index('--proof') + 1])\n"
                "input_path = Path(sys.argv[-1])\n"
                "if input_path != Path('/run/ay-input/instance'):\n"
                "    raise SystemExit(92)\n"
                "if input_path.read_text() != 'p cnf 1 1\\n1 0\\n':\n"
                "    raise SystemExit(93)\n"
                "proof.write_text('proof')\n"
                "print('unsat')\n"
            )
            source.chmod(0o700)
            run_dir = root / "run"
            results = root / "results"
            private = results / "eval" / "run" / "private"
            proof_dir = private / "proof"
            proof_dir.mkdir(parents=True)
            benchmark = private / "solver-input.cnf"
            benchmark.write_text("p cnf 1 1\n1 0\n")
            proof = proof_dir / "solver-output.drat"
            run_dir.mkdir()
            candidate = campaign.prepare_candidate_solver(
                source,
                run_dir,
                results,
                tested_sha="a" * 40,
                label="test",
            )
            if os.environ.get(campaign.BUILD_SANDBOX_MARKER) == "1":
                self.skipTest(
                    "live nested bubblewrap probe is unavailable inside the "
                    "candidate build sandbox"
                )
            child_env = os.environ.copy()
            child_env["GH_TOKEN"] = "must-not-cross"
            completed = subprocess.run(
                [
                    candidate["launcher_path"],
                    "--memory",
                    "64",
                    "--proof",
                    str(proof),
                    "--",
                    str(benchmark),
                ],
                env=child_env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=10,
                check=False,
            )
            self.assertEqual(completed.returncode, 0, completed.stderr)
            self.assertEqual(completed.stdout.strip(), "unsat")
            self.assertEqual(proof.read_text(), "proof")
            self.assertEqual(protected.read_text(), "trusted")

    def test_build_resource_plan_enforces_and_records_cargo_jobs(self) -> None:
        plan = argparse.Namespace(
            jobs=1,
            memlimit_mb=2048,
            nbcore=3,
            headroom_mb=16000,
        )
        env = {"KEEP": "value", "NBCORE": "99"}

        build_env = campaign.parent_lease_build_environment(env, plan)
        self.assertEqual(
            env,
            {"KEEP": "value", "NBCORE": "99"},
            "parent-lease fields must not leak into the base lane environment",
        )
        self.assertEqual(build_env["AY_CONTINUOUS_MEMLIMIT_MB"], "2048")
        self.assertEqual(build_env["AY_CONTINUOUS_JOBS"], "1")
        self.assertEqual(build_env["AY_CONTINUOUS_HEADROOM_MB"], "16000")
        self.assertEqual(build_env["AY_OOM_GUARD_PARENT_LEASE"], "1")
        self.assertEqual(build_env["MEMLIMIT"], "2048")
        self.assertEqual(build_env["NBCORE"], "3")
        self.assertEqual(build_env["CARGO_BUILD_JOBS"], "3")
        self.assertEqual(
            campaign.resource_plan_json(plan),
            {
                "jobs": 1,
                "memlimit_mb": 2048,
                "nbcore": 3,
                "cargo_jobs": 3,
                "headroom_mb": 16000,
            },
        )
        self.assertEqual(
            campaign.build_jobs_from_environment(build_env, "unit test"),
            3,
        )

    def test_direct_cargo_and_targo_build_jobs_are_explicit(self) -> None:
        self.assertEqual(
            campaign.enforce_direct_build_jobs(
                ["/toolchain/bin/cargo", "build", "--release"],
                3,
            ),
            [
                "/toolchain/bin/cargo",
                "build",
                "--release",
                "-j",
                "3",
            ],
        )
        self.assertEqual(
            campaign.enforce_direct_build_jobs(
                [
                    "/trust/stage2/bin/targo",
                    "--unverified",
                    "test",
                    "-p",
                    "ay-sat",
                    "--",
                    "--test-threads=1",
                ],
                2,
            ),
            [
                "/trust/stage2/bin/targo",
                "--unverified",
                "test",
                "-p",
                "ay-sat",
                "-j",
                "2",
                "--",
                "--test-threads=1",
            ],
        )
        already_exact = ["cargo", "check", "--jobs=4", "--workspace"]
        self.assertEqual(
            campaign.enforce_direct_build_jobs(already_exact, 4),
            already_exact,
        )
        for option in ("-j", "--jobs"):
            global_exact = [
                "cargo",
                option,
                "4",
                "check",
                "--workspace",
            ]
            self.assertEqual(
                campaign.enforce_direct_build_jobs(global_exact, 4),
                global_exact,
            )
        self.assertEqual(
            campaign.enforce_direct_build_jobs(["cargo", "fmt", "--check"], 4),
            ["cargo", "fmt", "--check"],
        )
        self.assertEqual(
            campaign.enforce_direct_build_jobs(
                ["bash", "scripts/ci/sat_soundness_gate.sh"],
                4,
            ),
            ["bash", "scripts/ci/sat_soundness_gate.sh"],
        )

    def test_build_core_enforcement_fails_closed(self) -> None:
        for plan in (
            argparse.Namespace(
                jobs=2,
                nbcore=3,
                memlimit_mb=2048,
                headroom_mb=16000,
            ),
            argparse.Namespace(
                jobs=1,
                nbcore=0,
                memlimit_mb=2048,
                headroom_mb=16000,
            ),
            argparse.Namespace(
                jobs=1,
                nbcore=3,
                memlimit_mb=0,
                headroom_mb=16000,
            ),
            argparse.Namespace(
                jobs=1,
                nbcore=3,
                memlimit_mb=2048,
                headroom_mb=-1,
            ),
        ):
            with self.assertRaises(campaign.CampaignError):
                campaign.parent_lease_build_environment({}, plan)

        valid_env = {
            "AY_CONTINUOUS_HEADROOM_MB": "16000",
            "AY_CONTINUOUS_JOBS": "1",
            "AY_CONTINUOUS_MEMLIMIT_MB": "2048",
            "AY_OOM_GUARD_PARENT_LEASE": "1",
            "CARGO_BUILD_JOBS": "3",
            "MEMLIMIT": "2048",
            "NBCORE": "3",
        }
        invalid_envs = [
            {},
            {**valid_env, "AY_OOM_GUARD_PARENT_LEASE": "0"},
            {**valid_env, "AY_CONTINUOUS_JOBS": "2"},
            {**valid_env, "AY_CONTINUOUS_HEADROOM_MB": "-1"},
            {**valid_env, "AY_CONTINUOUS_MEMLIMIT_MB": "1024"},
            {**valid_env, "CARGO_BUILD_JOBS": "4"},
            {**valid_env, "CARGO_BUILD_JOBS": "many"},
        ]
        for env in invalid_envs:
            with self.assertRaises(campaign.CampaignError):
                campaign.build_jobs_from_environment(env, "unit test")

        for argv in (
            ["cargo", "build", "-j", "8"],
            ["targo", "test", "--jobs=8"],
            ["cargo", "check", "--jobs"],
            ["cargo", "build", "-j", "3", "--jobs=3"],
            ["cargo", "build", "--jobs=many"],
            ["cargo", "-j", "8", "build"],
            ["cargo", "--jobs", "8", "build"],
            ["cargo", "-j"],
            ["cargo", "--jobs"],
            ["cargo", "--jobs", "many", "build"],
        ):
            with self.assertRaises(campaign.CampaignError):
                campaign.enforce_direct_build_jobs(argv, 3)

    @unittest.skipUnless(
        os.path.isdir("/dev/shm") and campaign.shutil.which("bwrap"),
        "Linux tmpfs/bubblewrap check",
    )
    def test_build_sandbox_accepts_bounded_tmpfs_target(self) -> None:
        repo = Path(__file__).resolve().parents[2]
        with tempfile.TemporaryDirectory(dir="/dev/shm") as temporary:
            target = Path(temporary) / "target"
            lease = Path(temporary) / "oom-guard.lock"
            env = {
                "CARGO_TARGET_DIR": str(target),
                "AY_CONTINUOUS_HEADROOM_MB": "16000",
                "AY_CONTINUOUS_JOBS": "1",
                "AY_CONTINUOUS_MEMLIMIT_MB": "1024",
                "AY_OOM_GUARD_PARENT_LEASE": "1",
                "CARGO_BUILD_JOBS": "3",
                "MEMLIMIT": "1024",
                "NBCORE": "3",
            }
            # The production controller legitimately owns the stable host lease
            # while it runs this test as a build gate. Keep this nested planning
            # assertion isolated instead of competing with the parent campaign.
            with mock.patch.object(
                campaign._oom_guard,
                "_host_harness_lease_path",
                return_value=str(lease),
            ):
                with campaign.planned_build_resources("sandbox unit test"):
                    command = campaign.sandbox_command(
                        ["/bin/true"],
                        repo=repo,
                        worktree=repo,
                        writable_paths=[target],
                        env=env,
                    )
                    lease_index = command.index(str(lease))
                    self.assertEqual(
                        command[lease_index - 1 : lease_index + 2],
                        ["--ro-bind", str(lease), str(lease)],
                    )
                    marker_index = command.index(campaign.BUILD_SANDBOX_MARKER)
                    self.assertEqual(
                        command[marker_index - 1 : marker_index + 2],
                        ["--setenv", campaign.BUILD_SANDBOX_MARKER, "1"],
                    )
                    run_index = command.index("/run")
                    self.assertEqual(
                        command[run_index - 3 : run_index + 1],
                        ["--size", str(64 * 1024 * 1024), "--tmpfs", "/run"],
                    )
                    if os.environ.get(campaign.BUILD_SANDBOX_MARKER) == "1":
                        self.skipTest(
                            "live nested bubblewrap probe is unavailable inside "
                            "the candidate build sandbox"
                        )
                    cargo_jobs_index = command.index("CARGO_BUILD_JOBS")
                    self.assertEqual(
                        command[cargo_jobs_index - 1 : cargo_jobs_index + 2],
                        ["--setenv", "CARGO_BUILD_JOBS", "3"],
                    )
                    parent_lease_index = command.index(
                        "AY_OOM_GUARD_PARENT_LEASE"
                    )
                    self.assertEqual(
                        command[
                            parent_lease_index - 1 : parent_lease_index + 2
                        ],
                        ["--setenv", "AY_OOM_GUARD_PARENT_LEASE", "1"],
                    )
                    completed = subprocess.run(
                        command,
                        cwd=repo,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        timeout=10,
                        check=False,
                    )
            self.assertEqual(completed.returncode, 0, completed.stderr.decode())

    def test_branch_classification_detects_patch_equivalence(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary) / "repo"
            repo.mkdir()
            git(repo, "init", "-b", "main")
            git(repo, "config", "user.name", "Test")
            git(repo, "config", "user.email", "test@example.com")
            (repo / "base").write_text("base\n")
            git(repo, "add", "base")
            git(repo, "commit", "-m", "base")
            root = git(repo, "rev-parse", "HEAD")

            git(repo, "switch", "-c", "topic", root)
            (repo / "same").write_text("same\n")
            git(repo, "add", "same")
            git(repo, "commit", "-m", "topic patch")
            topic = git(repo, "rev-parse", "HEAD")

            git(repo, "switch", "main")
            (repo / "same").write_text("same\n")
            git(repo, "add", "same")
            git(repo, "commit", "-m", "equivalent on main")
            main = git(repo, "rev-parse", "HEAD")

            git(repo, "update-ref", "refs/remotes/origin/main", main)
            git(repo, "update-ref", "refs/remotes/origin/topic", topic)
            records = campaign.classify_branches(
                repo,
                "origin",
                "main",
                {"main": main, "topic": topic},
                [],
            )
            by_name = {record.name: record for record in records}
            self.assertEqual(by_name["topic"].classification, "patch-equivalent")

    def test_merge_resolution_change_is_not_patch_equivalent(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary) / "repo"
            repo.mkdir()
            git(repo, "init", "-b", "main")
            git(repo, "config", "user.name", "Test")
            git(repo, "config", "user.email", "test@example.com")
            (repo / "value").write_text("root\n")
            git(repo, "add", "value")
            git(repo, "commit", "-m", "root")
            root = git(repo, "rev-parse", "HEAD")

            git(repo, "switch", "-c", "left", root)
            (repo / "value").write_text("left\n")
            git(repo, "commit", "-am", "left")
            left = git(repo, "rev-parse", "HEAD")

            git(repo, "switch", "-c", "right", root)
            (repo / "value").write_text("right\n")
            git(repo, "commit", "-am", "right")

            git(repo, "switch", "-C", "main", left)
            merged = subprocess.run(
                ["git", "merge", "--no-ff", "right"],
                cwd=repo,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            self.assertNotEqual(merged.returncode, 0)
            (repo / "value").write_text("base resolution\n")
            git(repo, "add", "value")
            git(repo, "commit", "-m", "base resolution")
            main = git(repo, "rev-parse", "HEAD")

            git(repo, "switch", "-C", "topic", left)
            merged = subprocess.run(
                ["git", "merge", "--no-ff", "right"],
                cwd=repo,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            self.assertNotEqual(merged.returncode, 0)
            (repo / "value").write_text("topic resolution\n")
            git(repo, "add", "value")
            git(repo, "commit", "-m", "topic resolution")
            topic = git(repo, "rev-parse", "HEAD")

            records = campaign.classify_branches(
                repo,
                "origin",
                "main",
                {"main": main, "topic": topic},
                [],
            )
            by_name = {record.name: record for record in records}
            self.assertEqual(by_name["topic"].classification, "unique")

    def test_bootstrap_checkout_fast_forwards_before_policy_load(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            bare = base / "origin.git"
            source = base / "source"
            checkout = base / "checkout"
            git(base, "init", "--bare", str(bare))
            git(base, "clone", str(bare), str(source))
            git(source, "config", "user.name", "Test")
            git(source, "config", "user.email", "test@example.com")
            git(source, "switch", "-c", "main")
            (source / "policy").write_text("v1\n")
            git(source, "add", "policy")
            git(source, "commit", "-m", "v1")
            git(source, "push", "-u", "origin", "main")
            git(base, "clone", str(bare), str(checkout))
            git(checkout, "switch", "main")

            (source / "policy").write_text("v2\n")
            git(source, "commit", "-am", "v2")
            git(source, "push", "origin", "main")
            expected = git(source, "rev-parse", "HEAD")

            updated = campaign.bootstrap_checkout(checkout, "origin", "main")
            self.assertEqual(updated, expected)
            self.assertEqual(git(checkout, "rev-parse", "HEAD"), expected)
            self.assertEqual((checkout / "policy").read_text(), "v2\n")
            self.assertIsNone(
                campaign.bootstrap_checkout(checkout, "origin", "main")
            )

    def test_startup_cleanup_removes_unregistered_partial_worktree(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            repo = root / "repo"
            state = root / "state"
            repo.mkdir()
            git(repo, "init", "-b", "main")
            git(repo, "config", "user.name", "Test")
            git(repo, "config", "user.email", "test@example.com")
            (repo / "base").write_text("base\n")
            git(repo, "add", "base")
            git(repo, "commit", "-m", "base")
            stale = state / "worktrees" / "20260720T000000Z"
            stale.mkdir(parents=True)
            (stale / "partial").write_text("not registered\n")

            removed = campaign.cleanup_stale_scratch(repo, state)
            self.assertEqual(
                removed["worktrees"],
                ["20260720T000000Z"],
            )
            self.assertFalse(stale.exists())

    def test_smoke_cycle_uses_disposable_worktree(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            bare = base / "origin.git"
            source = base / "source"
            checkout = base / "checkout"
            state = base / "state"
            git(base, "init", "--bare", str(bare))
            git(base, "clone", str(bare), str(source))
            git(source, "config", "user.name", "Test")
            git(source, "config", "user.email", "test@example.com")
            git(source, "switch", "-c", "main")
            (source / "benchmarks").mkdir()
            (source / "benchmarks" / "continuous-lanes.toml").write_text(
                "\n".join(
                    [
                        "schema_version = 1",
                        "[git]",
                        'remote = "origin"',
                        'base_branch = "main"',
                        'exclude = ["continuous/*"]',
                        "[build]",
                        'commands = [["python3", "-c", "from pathlib import Path; '
                        "import sys; p=Path(sys.argv[1]); "
                        "p.parent.mkdir(parents=True, exist_ok=True); "
                        'p.touch(); p.chmod(0o755)", "{ay}"]]',
                        "[[lane]]",
                        'id = "canary"',
                        'kind = "canary"',
                        'eval_id = "fake-canary"',
                        "",
                    ]
                )
            )
            git(source, "add", ".")
            git(source, "commit", "-m", "initial")
            git(source, "push", "-u", "origin", "main")
            git(base, "clone", str(bare), str(checkout))
            git(checkout, "switch", "main")

            args = argparse.Namespace(
                repo=str(checkout),
                state_root=str(state),
                lanes="benchmarks/continuous-lanes.toml",
                catalog="benchmarks/continuous-2025-2026.toml",
                smoke_only=True,
                official=False,
                push=False,
                repair_with_codex=False,
                repair_timeout=30,
                publish_issue=False,
            )
            passed = campaign.LaneOutcome(
                lane_id="canary",
                eval_id="fake-canary",
                status="passed",
                detail="test canary",
                scorecard={
                    "results": [
                        {
                            "score": {
                                "solved": 1,
                                "total": 1,
                                "wrong": 0,
                            }
                        }
                    ]
                },
            )
            def fake_build_gates(
                _manifest,
                _repo,
                _worktree,
                _run_dir,
                _env,
                target,
                _writable_paths,
            ):
                ay = target / "release" / "ay"
                ay.parent.mkdir(parents=True, exist_ok=True)
                ay.write_bytes(b"fake candidate solver")
                ay.chmod(0o755)
                return [
                    campaign.CommandRecord(
                        argv=["fake-gate"],
                        cwd=str(_worktree),
                        exit_code=0,
                        elapsed_sec=0.0,
                        log=str(_run_dir / "fake-gate.log"),
                    )
                ]

            def fake_supervisor_build(
                _repo,
                _worktree,
                run_dir,
                _env,
                _target,
                _writable_paths,
                *,
                timeout_sec,
            ):
                del timeout_sec
                ay = run_dir / "trusted-supervisor" / "ay"
                ay.parent.mkdir(parents=True, exist_ok=True)
                ay.write_bytes(b"fake trusted supervisor")
                ay.chmod(0o500)
                return (
                    campaign.CommandRecord(
                        argv=["fake-supervisor-build"],
                        cwd=str(_worktree),
                        exit_code=0,
                        elapsed_sec=0.0,
                        log=str(run_dir / "fake-supervisor.log"),
                    ),
                    ay,
                    campaign.file_sha256(ay),
                )

            @contextlib.contextmanager
            def mocked_cycle(*, fetch_exit: int = 0):
                with (
                    mock.patch.object(
                        campaign,
                        "execute_lanes",
                        return_value=[passed],
                    ) as lanes_mock,
                    mock.patch.object(
                        campaign,
                        "execute_build_gates",
                        side_effect=fake_build_gates,
                    ) as gates_mock,
                    mock.patch.object(
                        campaign,
                        "build_trusted_supervisor",
                        side_effect=fake_supervisor_build,
                    ) as supervisor_mock,
                    mock.patch.object(
                        campaign,
                        "fetch_trusted_dependencies",
                        return_value=campaign.CommandRecord(
                            argv=["cargo", "fetch", "--locked"],
                            cwd=str(checkout),
                            exit_code=fetch_exit,
                            elapsed_sec=0.0,
                            log=str(state / "fake-fetch.log"),
                        ),
                    ),
                    mock.patch.object(
                        campaign,
                        "planned_build_resources",
                        return_value=contextlib.nullcontext(
                            argparse.Namespace(
                                jobs=1,
                                memlimit_mb=1024,
                                nbcore=1,
                                headroom_mb=256,
                            )
                        ),
                    ),
                    contextlib.redirect_stdout(io.StringIO()),
                ):
                    yield {
                        "lanes": lanes_mock,
                        "gates": gates_mock,
                        "supervisor": supervisor_mock,
                    }

            with mocked_cycle():
                self.assertEqual(campaign.cycle(args), 0)
            latest = json.loads((state / "latest.json").read_text())
            self.assertEqual(latest["status"], "passed")
            self.assertEqual(latest["base_sha"], latest["tested_sha"])
            self.assertEqual(list((state / "worktrees").iterdir()), [])

            # Give the candidate an actual unique topic so a clean cycle would
            # push. Explicit issue publication must succeed immediately before
            # that mutation.
            git(source, "switch", "-c", "topic")
            (source / "solver.txt").write_text("candidate\n")
            git(source, "add", "solver.txt")
            git(source, "commit", "-m", "candidate")
            git(source, "push", "-u", "origin", "topic")
            remote_before = git(
                base,
                "--git-dir",
                str(bare),
                "rev-parse",
                "refs/heads/main",
            )

            publish_args = argparse.Namespace(
                **{
                    **vars(args),
                    "state_root": str(base / "pre-push-state"),
                    "push": True,
                    "publish_issue": True,
                }
            )
            calls = 0

            def fail_pre_push(*_args, **_kwargs):
                nonlocal calls
                calls += 1
                if calls == 4:
                    raise campaign.CampaignError("injected pre-push outage")
                return 1

            with (
                mocked_cycle(),
                mock.patch.object(
                    campaign,
                    "publish_issue",
                    side_effect=fail_pre_push,
                ),
            ):
                self.assertEqual(campaign.cycle(publish_args), 1)
            self.assertEqual(
                git(
                    base,
                    "--git-dir",
                    str(bare),
                    "rev-parse",
                    "refs/heads/main",
                ),
                remote_before,
            )
            pre_push_latest = json.loads(
                (base / "pre-push-state" / "latest.json").read_text()
            )
            self.assertEqual(
                pre_push_latest["push"]["status"],
                "publication-blocked",
            )

            # A later outage cannot roll back a push that was preceded by the
            # required publication checkpoint; admitted scoreboard state is
            # retained even though the cycle reports the operational failure.
            calls = 0

            def fail_final(*_args, **_kwargs):
                nonlocal calls
                calls += 1
                if calls == 5:
                    raise campaign.CampaignError("injected final outage")
                return 1

            final_state = base / "final-publication-state"
            final_args = argparse.Namespace(
                **{
                    **vars(publish_args),
                    "state_root": str(final_state),
                }
            )
            with (
                mocked_cycle(),
                mock.patch.object(
                    campaign,
                    "publish_issue",
                    side_effect=fail_final,
                ),
            ):
                self.assertEqual(campaign.cycle(final_args), 1)
            final_latest = json.loads((final_state / "latest.json").read_text())
            final_persistent = json.loads((final_state / "state.json").read_text())
            self.assertEqual(final_latest["push"]["status"], "pushed")
            self.assertIn(
                f"--force-with-lease=refs/heads/main:{remote_before}",
                final_latest["push"]["command"]["argv"],
            )
            self.assertEqual(final_latest["status"], "failed")
            self.assertNotEqual(
                git(
                    base,
                    "--git-dir",
                    str(bare),
                    "rev-parse",
                    "refs/heads/main",
                ),
                remote_before,
            )
            self.assertEqual(
                final_persistent["scoreboard"]["canary"]["score_run_id"],
                final_latest["run_id"],
            )

            # A trusted-base dependency-fetch failure happens before the
            # supervisor build, topic merge, benchmark, or push.
            git(source, "switch", "main")
            git(source, "fetch", "origin")
            git(source, "merge", "--ff-only", "origin/main")
            git(source, "switch", "-c", "topic-fetch-failure")
            (source / "solver-2.txt").write_text("second candidate\n")
            git(source, "add", "solver-2.txt")
            git(source, "commit", "-m", "second candidate")
            git(source, "push", "-u", "origin", "topic-fetch-failure")
            fetch_remote_before = git(
                base,
                "--git-dir",
                str(bare),
                "rev-parse",
                "refs/heads/main",
            )
            fetch_args = argparse.Namespace(
                **{
                    **vars(args),
                    "state_root": str(base / "fetch-failure-state"),
                    "push": True,
                }
            )
            with mocked_cycle(fetch_exit=1) as mocks:
                self.assertEqual(campaign.cycle(fetch_args), 1)
            mocks["supervisor"].assert_not_called()
            mocks["gates"].assert_not_called()
            mocks["lanes"].assert_not_called()
            self.assertEqual(
                git(
                    base,
                    "--git-dir",
                    str(bare),
                    "rev-parse",
                    "refs/heads/main",
                ),
                fetch_remote_before,
            )


if __name__ == "__main__":
    unittest.main()
