"""Focused regression tests for SMT-COMP preparation, cache, and resources."""

from __future__ import annotations

import hashlib
import json
import os
import sys
import tempfile
import time
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))

import smtcomp_harness as harness  # noqa: E402


def envelope(memlimit: int = 2048, requested: int = 4, admitted: int = 2,
             nbcore: int = 8, headroom: int = 16000) -> dict:
    plan = SimpleNamespace(
        jobs=admitted,
        memlimit_mb=memlimit,
        nbcore=nbcore,
        headroom_mb=headroom,
    )
    return harness.make_resource_envelope(requested, plan)


def run_row(resource: dict, *, solver: str = "ay", instance: str = "a.smt2",
            timeout: int = 10, source: str = "source", materialized: str = "mat",
            logic: str = "QF_UF") -> dict:
    identity = {
        "version": harness.RUN_IDENTITY_VERSION,
        "instance": instance,
        "track": "sq",
        "logic": logic,
        "expected": "sat",
        "timeout_s": timeout,
        "resource_envelope": resource,
        "solver": {"name": solver, "binary": "bin"},
        "invocation": {"argv": [solver, "{INPUT}"], "stdin": None},
        "source_sha256": source,
        "materialized_sha256": materialized,
        "materialization_version": harness.MATERIALIZATION_VERSION["sq"],
    }
    return {
        "instance": instance,
        "resource_envelope": resource,
        "run_identity": identity,
        "run_cache_key": harness.identity_key(identity),
    }


def validation_row(resource: dict, *, track: str = "mv", timeout: int = 10,
                   source: str = "source", config: str = "dolmen",
                   solver: str = "ay", instance: str = "a") -> dict:
    identity = {
        "version": harness.VALIDATION_IDENTITY_VERSION,
        "instance": instance,
        "producer": solver,
        "track": track,
        "timeout_s": timeout,
        "resource_envelope": resource,
        "source_sha256": source,
        "validator_config": {"binary": config},
    }
    return {
        "validation_resource_envelope": resource,
        "validation_identity": identity,
        "validation_cache_key": harness.identity_key(identity),
    }


class StructuralPreparationTests(unittest.TestCase):
    def test_uc_precollects_labels_and_avoids_generated_collision(self) -> None:
        data = (
            b"(assert true)\n"
            b"(assert (! false :named smtcomp1))\n"
            b"(check-sat)\n"
        )
        prepped, count = harness.prep_uc(data)
        self.assertEqual(count, 2)
        self.assertIn(b":named smtcomp2", prepped)
        self.assertEqual(prepped.count(b":named smtcomp1"), 1)

    def test_uc_rejects_duplicate_normalized_existing_labels(self) -> None:
        data = (
            b"(assert (! true :named duplicate))\n"
            b"(assert (! false :named |duplicate|))\n"
        )
        with self.assertRaisesRegex(ValueError, "duplicate normalized"):
            harness.prep_uc(data)

    def test_uc_counts_and_matches_unique_names(self) -> None:
        data = (
            b"(assert (! true :named existing))\n"
            b"(assert false)\n(check-sat)\n"
        )
        prepped, count = harness.prep_uc(data)
        self.assertEqual(count, 2)
        self.assertIn(b":named smtcomp1", prepped)
        reduced, matched, baseline = harness.build_reduced(
            data, {"existing", "smtcomp1"}
        )
        self.assertEqual(matched, ["existing", "smtcomp1"])
        self.assertEqual(baseline, 2)
        self.assertEqual(reduced.count(b"(assert"), 2)

    def test_uc_ignores_option_and_get_text_outside_exact_commands(self) -> None:
        data = (
            b"; (set-option :produce-unsat-cores true) (get-unsat-core)\n"
            b"(declare-fun produce-unsat-cores () Bool)\n"
            b"(assert (= |get-unsat-core| \"produce-unsat-cores\"))\n"
            b"(check-sat ; whitespace and comment\n )\n"
            b"(get-unsat-core extra)\n"
        )
        prepped, _ = harness.prep_uc(data)
        self.assertTrue(prepped.startswith(
            b"(set-option :produce-unsat-cores true)\n"
        ))
        self.assertIn(b"\n(get-unsat-core)\n(get-unsat-core extra)", prepped)

    def test_uc_accepts_exact_whitespace_commands_and_rewrites_false(self) -> None:
        exact = (
            b"(set-option ; comment\n :produce-unsat-cores false)\n"
            b"(check-sat)\n(get-unsat-core ; comment\n )\n"
        )
        prepped, _ = harness.prep_uc(exact)
        self.assertEqual(prepped.count(
            b"(set-option :produce-unsat-cores true)"
        ), 1)
        self.assertEqual(prepped.count(b"(get-unsat-core"), 1)
        self.assertNotIn(b":produce-unsat-cores false", prepped)

    def test_mv_ignores_comment_symbol_quoted_and_extra_arg_decoys(self) -> None:
        data = (
            b"; produce-models (get-model)\n"
            b"(declare-fun produce-models () Bool)\n"
            b"(assert (= |get-model| \"produce-models\"))\n"
            b"(check-sat ; split form\n )\n(get-model extra)\n"
        )
        prepped = harness.prep_mv(data)
        self.assertTrue(prepped.startswith(
            b"(set-option :produce-models true)\n"
        ))
        self.assertIn(b"\n(get-model)\n(get-model extra)", prepped)

    def test_mv_accepts_exact_whitespace_get_and_rewrites_false_option(self) -> None:
        data = (
            b"(set-option\n :produce-models false)\n"
            b"(check-sat)\n(get-model ; exact zero-argument command\n )\n"
        )
        prepped = harness.prep_mv(data)
        self.assertEqual(prepped.count(b"(set-option :produce-models true)"), 1)
        self.assertNotIn(b":produce-models false", prepped)
        self.assertEqual(prepped.count(b"(get-model"), 1)

    def test_mv_structurally_strips_inline_multiline_set_info_only(self) -> None:
        data = (
            b"; (set-info :status sat)\n"
            b"(set-info\n :source \"text ) (\") (assert true)\n"
            b"(assert (= |set-info| 1))\n(check-sat)\n"
        )
        prepped = harness.prep_mv(data)
        self.assertNotIn(b":source", prepped)
        self.assertIn(b"; (set-info :status sat)", prepped)
        self.assertIn(b"(assert true)", prepped)
        self.assertIn(b"|set-info|", prepped)


class ResourceAndRunIdentityTests(unittest.TestCase):
    def test_envelope_records_full_plan_and_exact_watchdog(self) -> None:
        resource = envelope()
        self.assertTrue(harness.valid_resource_envelope(resource))
        self.assertEqual(resource["requested_jobs"], 4)
        self.assertEqual(resource["admitted_jobs"], 2)
        self.assertEqual(resource["nbcore"], 8)
        self.assertEqual(resource["headroom_mb"], 16000)
        self.assertEqual(resource["watchdog"]["grace_mb"], 0)
        self.assertEqual(resource["watchdog"]["limit_mb"], 2048)
        self.assertEqual(resource["watchdog"]["scope"], "process-group-rss")

    def test_run_cache_binds_timeout_command_binary_input_transform_and_envelope(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            bench = root / "a.smt2"
            bench.write_text("(set-info :status sat)\n(check-sat)\n")
            solver_bin = root / "solver"
            solver_bin.write_bytes(b"solver-v1")
            solver = harness.Solver("s", solver_bin, "plain")
            inst = harness.Instance("a.smt2", "QF_UF", "", "", "sat")
            resource = envelope()
            with mock.patch.object(harness, "BENCH_ROOT", root):
                original = harness.make_run_identity(
                    solver, inst, "sq", 10, resource
                )
                row = {
                    "run_identity": original,
                    "run_cache_key": harness.identity_key(original),
                }
                self.assertTrue(harness.reusable_run_record(row, original))

                changed_timeout = harness.make_run_identity(
                    solver, inst, "sq", 11, resource
                )
                self.assertFalse(harness.reusable_run_record(row, changed_timeout))

                changed_envelope = harness.make_run_identity(
                    solver, inst, "sq", 10, envelope(nbcore=4)
                )
                self.assertFalse(harness.reusable_run_record(row, changed_envelope))

                bench.write_text("(check-sat)\n(assert true)\n")
                changed_input = harness.make_run_identity(
                    solver, inst, "sq", 10, resource
                )
                self.assertFalse(harness.reusable_run_record(row, changed_input))

                bench.write_text("(set-info :status sat)\n(check-sat)\n")
                solver_bin.write_bytes(b"solver-v2")
                changed_binary = harness.make_run_identity(
                    solver, inst, "sq", 10, resource
                )
                self.assertFalse(harness.reusable_run_record(row, changed_binary))

                ay = harness.Solver("s", solver_bin, "ay")
                changed_command = harness.make_run_identity(
                    ay, inst, "sq", 10, resource
                )
                self.assertFalse(harness.reusable_run_record(row, changed_command))

    def test_ay_invocation_receives_memory_budget(self) -> None:
        solver = harness.Solver("ay", Path("/bin/true"), "ay")
        inv = harness.build_invocation(
            solver, "sq", "QF_UF", "input.smt2", envelope(memlimit=3072)
        )
        self.assertIsNotNone(inv)
        self.assertEqual(inv.argv[-2:], ["3072", "input.smt2"])
        self.assertIn("--memory", inv.argv)

    def test_scoring_rejects_full_envelope_timeout_and_corpus_mismatches(self) -> None:
        resource = envelope()
        records = {
            "ay": {"a.smt2": run_row(resource)},
            "z3": {"a.smt2": run_row(resource, solver="z3")},
        }
        common, timeout = harness.require_comparable_run_conditions(records)
        self.assertEqual(common, resource)
        self.assertEqual(timeout, 10)

        records["z3"]["a.smt2"] = run_row(
            envelope(nbcore=2), solver="z3"
        )
        with self.assertRaisesRegex(SystemExit, "resource envelopes"):
            harness.require_comparable_run_conditions(records)

        records["z3"]["a.smt2"] = run_row(
            resource, solver="z3", timeout=11
        )
        with self.assertRaisesRegex(SystemExit, "timeouts"):
            harness.require_comparable_run_conditions(records)

        records["z3"] = {}
        with self.assertRaisesRegex(SystemExit, "corpus variants"):
            harness.require_comparable_run_conditions(records)

    def test_validation_scoring_rejects_binary_config_and_envelope_mixes(self) -> None:
        resource = envelope()
        rows = {
            "ay": {"a": validation_row(resource)},
            "z3": {"a": validation_row(resource, solver="z3")},
        }
        self.assertEqual(
            harness.require_comparable_validation_conditions(rows, "mv"),
            resource,
        )
        rows["z3"]["a"] = validation_row(
            resource, config="other-dolmen", solver="z3"
        )
        with self.assertRaisesRegex(SystemExit, "validator configs"):
            harness.require_comparable_validation_conditions(rows, "mv")
        rows["z3"]["a"] = validation_row(
            envelope(nbcore=1), solver="z3"
        )
        with self.assertRaisesRegex(SystemExit, "resource envelopes"):
            harness.require_comparable_validation_conditions(rows, "mv")


class ValidatorIdentityTests(unittest.TestCase):
    def test_uc_cache_binds_validator_binary_timeout_source_and_envelope(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "a.smt2").write_text(
                "(set-logic QF_UF)\n(assert false)\n(check-sat)\n"
            )
            core = root / "a.core"
            core.write_text("(smtcomp1)\n")
            rec = {
                "instance": "a.smt2", "logic": "QF_UF",
                "core_path": str(core), "run_cache_key": "run-1",
            }
            v1 = harness.Solver("v", Path("/bin/true"), "plain")
            v2 = harness.Solver("v", Path("/bin/false"), "plain")
            resource = envelope()
            with mock.patch.object(harness, "BENCH_ROOT", root):
                base = harness.make_uc_validation_identity(
                    rec, "producer", [v1], 10, resource
                )
                other_binary = harness.make_uc_validation_identity(
                    rec, "producer", [v2], 10, resource
                )
                other_timeout = harness.make_uc_validation_identity(
                    rec, "producer", [v1], 11, resource
                )
                other_envelope = harness.make_uc_validation_identity(
                    rec, "producer", [v1], 10, envelope(nbcore=1)
                )
                (root / "a.smt2").write_text(
                    "(set-logic QF_UF)\n(assert true)\n(check-sat)\n"
                )
                other_source = harness.make_uc_validation_identity(
                    rec, "producer", [v1], 10, resource
                )
        keys = {
            harness.identity_key(value)
            for value in (base, other_binary, other_timeout,
                          other_envelope, other_source)
        }
        self.assertEqual(len(keys), 5)

    def test_mv_cache_binds_model_dolmen_config_input_and_envelope(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "a.smt2").write_text("(check-sat)\n")
            model = root / "model.out"
            model.write_text("sat\n(model)\n")
            dolmen = root / "dolmen"
            dolmen.write_bytes(b"dolmen-v1")
            rec = {
                "instance": "a.smt2", "model_path": str(model),
                "run_cache_key": "run-1",
            }
            resource = envelope()
            with mock.patch.object(harness, "BENCH_ROOT", root):
                base = harness.make_mv_validation_identity(
                    dolmen, rec, "1h", "40G", 3700, resource
                )
                model.write_text("sat\n(other-model)\n")
                other_model = harness.make_mv_validation_identity(
                    dolmen, rec, "1h", "40G", 3700, resource
                )
                other_config = harness.make_mv_validation_identity(
                    dolmen, rec, "2h", "40G", 3700, resource
                )
                other_envelope = harness.make_mv_validation_identity(
                    dolmen, rec, "1h", "40G", 3700, envelope(nbcore=1)
                )
                (root / "a.smt2").write_text("(assert true)\n(check-sat)\n")
                other_source = harness.make_mv_validation_identity(
                    dolmen, rec, "1h", "40G", 3700, resource
                )
        keys = {
            harness.identity_key(value)
            for value in (base, other_model, other_config,
                          other_envelope, other_source)
        }
        self.assertEqual(len(keys), 5)

    def test_uc_validator_forwards_full_resource_envelope(self) -> None:
        solver = harness.Solver("validator", Path("/bin/true"), "plain")
        resource = envelope(memlimit=3072)
        result = harness.ExecResult(
            stdout=b"unsat\n", stderr_tail="", wall_sec=0.1, cpu_sec=0.05,
            exit_code=0, timed_out=False,
        )
        with mock.patch.object(
            harness, "build_invocation", return_value=harness.Invocation(["validator"])
        ), mock.patch.object(harness, "run_process", return_value=result) as run:
            row = harness._run_validator(
                solver, "QF_UF", Path("x.smt2"), 10, resource
            )
        self.assertEqual(row["memlimit_mb"], 3072)
        run.assert_called_once_with(mock.ANY, 10, resource_envelope=resource)

    def test_dolmen_memout_is_recorded_not_mislabelled_timeout(self) -> None:
        resource = envelope(memlimit=4096)
        result = harness.ExecResult(
            stdout=b"", stderr_tail="", wall_sec=0.2, cpu_sec=0.1,
            exit_code=-9, timed_out=False, memout=True,
        )
        with mock.patch.object(harness, "run_process", return_value=result) as run:
            row = harness.run_dolmen(
                Path("/dolmen"), "bench.smt2", Path("model.out"),
                "1h", "40G", 3700, False, resource,
            )
        self.assertEqual(row["status"], harness.V_MEMOUT)
        self.assertTrue(row["dolmen_memout"])
        self.assertFalse(row["dolmen_timed_out"])
        run.assert_called_once_with(
            mock.ANY, 3700, resource_envelope=resource
        )

    def test_full_unsat_core_is_validated_for_error_semantics(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "a.smt2").write_text(
                "(set-logic QF_UF)\n(assert false)\n(check-sat)\n"
            )
            core = root / "a.core"
            core.write_text("(smtcomp1)\n")
            validator = harness.Solver("validator", Path("/bin/true"), "plain")
            rec = {
                "instance": "a.smt2", "solver": "producer",
                "logic": "QF_UF", "core_path": str(core),
                "run_cache_key": "run-1",
            }
            resource = envelope()
            with mock.patch.object(harness, "BENCH_ROOT", root), mock.patch.object(
                harness, "_run_validator", return_value={"answer": "sat"}
            ) as run:
                row = harness.validate_uc_one(
                    rec, "producer", [validator], root / "tag", 10, resource
                )
        self.assertEqual(row["status"], "invalidated")
        self.assertEqual(row["validation_resource_envelope"], resource)
        run.assert_called_once()


@unittest.skipUnless(os.name == "posix", "process-group cleanup requires POSIX")
class ProcessCleanupTests(unittest.TestCase):
    def test_nbcore_is_applied_to_child_environment(self) -> None:
        resource = envelope(nbcore=3)
        code = "import os; print(os.environ.get('NBCORE'))"
        result = harness.run_process(
            harness.Invocation([sys.executable, "-c", code]),
            timeout_s=2,
            resource_envelope=resource,
        )
        self.assertEqual(result.stdout.strip(), b"3")

    def test_exited_wrapper_cannot_leave_solver_descendant_running(self) -> None:
        code = (
            "import subprocess,sys; "
            "p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(30)']); "
            "print(p.pid, flush=True)"
        )
        result = harness.run_process(
            harness.Invocation([sys.executable, "-c", code]),
            timeout_s=2,
            resource_envelope=envelope(memlimit=256),
        )
        self.assertEqual(result.exit_code, 0)
        descendant = int(result.stdout.strip())

        active = True
        for _ in range(50):
            try:
                state = Path(f"/proc/{descendant}/stat").read_text().split()[2]
                active = state != "Z"
            except (FileNotFoundError, ProcessLookupError):
                active = False
            if not active:
                break
            time.sleep(0.02)
        self.assertFalse(active, "wrapper descendant survived process-group teardown")

    def test_watchdog_view_does_not_steal_exit_status(self) -> None:
        result = harness.run_process(
            harness.Invocation([sys.executable, "-c", "raise SystemExit(7)"]),
            timeout_s=2,
            resource_envelope=envelope(memlimit=256),
        )
        self.assertEqual(result.exit_code, 7)


class ModelArtifactJoinTests(unittest.TestCase):
    def test_validation_for_overwritten_model_or_other_run_is_stale(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            model = root / "model.out"
            model.write_bytes(b"sat\n(model-new)\n")
            current_hash = hashlib.sha256(model.read_bytes()).hexdigest()
            tag = root / "tag"
            validation = tag / "validation"
            validation.mkdir(parents=True)
            path = validation / "ay.jsonl"
            rec = {
                "instance": "a.smt2", "answer": "sat",
                "model_path": str(model), "run_cache_key": "run-new",
                "run_identity": {
                    "source_sha256": "source", "materialized_sha256": "mat"
                },
            }
            stale_identity = {
                "track": "mv", "producer_run_cache_key": "run-old",
                "source_sha256": "source", "materialized_sha256": "mat",
                "model_sha256": current_hash,
            }
            path.write_text(json.dumps({
                "instance": "a.smt2", "model_sha256": current_hash,
                "status": harness.V_OK, "validation_identity": stale_identity,
            }) + "\n")
            effective, stale = harness.load_current_mv_validation(
                tag, "ay", {"a.smt2": rec}
            )
            self.assertEqual(effective, {})
            self.assertEqual(stale, 1)

            current_identity = dict(stale_identity, producer_run_cache_key="run-new")
            with path.open("a") as fh:
                fh.write(json.dumps({
                    "instance": "a.smt2", "model_sha256": current_hash,
                    "status": harness.V_OK,
                    "validation_identity": current_identity,
                }) + "\n")
            effective, stale = harness.load_current_mv_validation(
                tag, "ay", {"a.smt2": rec}
            )
            self.assertEqual(effective["a.smt2"]["status"], harness.V_OK)
            self.assertEqual(stale, 0)


if __name__ == "__main__":
    unittest.main()
