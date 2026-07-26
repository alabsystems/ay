"""Focused tests for benchmark drivers that consume the shared OOM guard."""

import importlib.util
import argparse
import contextlib
import io
import json
import lzma
import os
import subprocess
import sys
import tempfile
import types
import unittest
from pathlib import Path
from unittest import mock


SCRIPTS = Path(__file__).resolve().parents[1]

if not hasattr(os, "killpg"):
    raise RuntimeError(
        "resource-harness tests require POSIX process-group support"
    )


def load_script(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


proof_overhead = load_script("proof_overhead_under_test",
                             SCRIPTS / "proof_overhead.py")
mzn_run = load_script("mzn_challenge_run_under_test",
                      SCRIPTS / "mzn_challenge" / "run.py")
chccomp_harness = load_script("chccomp_harness_under_test",
                              SCRIPTS / "chccomp_harness.py")
pbcomp_harness = load_script("pbcomp_harness_under_test",
                             SCRIPTS / "pbcomp_harness.py")
chccomp_regression = load_script("chccomp_regression_under_test",
                                 SCRIPTS / "chccomp_regression.py")
wind_tunnel = load_script("wind_tunnel_under_test",
                          SCRIPTS / "wind_tunnel.py")


class ProofOverheadResourceTest(unittest.TestCase):
    def test_run_applies_environment_and_reads_bounded_status(self):
        with tempfile.TemporaryDirectory() as td:
            solver = Path(td, "solver")
            solver.write_text(
                "#!/bin/sh\n"
                "test \"$MEMLIMIT\" = 256 || exit 91\n"
                "test \"$NBCORE\" = 2 || exit 92\n"
                "printf 's SATISFIABLE\\n'\n"
            )
            solver.chmod(0o755)
            status, _ = proof_overhead.run(
                str(solver), Path(td, "tiny.opb"), 1000, 2.0, 256, 2,
                "plain", None,
            )
        self.assertEqual(status, "SATISFIABLE")

    def test_run_kills_and_classifies_hard_timeout(self):
        with tempfile.TemporaryDirectory() as td:
            solver = Path(td, "solver")
            solver.write_text("#!/bin/sh\nsleep 60\n")
            solver.chmod(0o755)
            status, elapsed = proof_overhead.run(
                str(solver), Path(td, "tiny.opb"), 1000, 0.1, 256, 1,
                "plain", None,
            )
        self.assertEqual(status, "WALLTIMEOUT")
        self.assertLess(elapsed, 5)

    def test_main_persists_exact_resource_envelope(self):
        with tempfile.TemporaryDirectory() as td:
            corpus = Path(td, "corpus")
            corpus.mkdir()
            Path(corpus, "tiny.opb").write_text(
                "* #variable= 0 #constraint= 0\n"
            )
            out = Path(td, "out")
            plan = types.SimpleNamespace(jobs=1, memlimit_mb=777, nbcore=3,
                                         headroom_mb=16000)
            argv = ["proof_overhead.py", "--corpus", str(corpus),
                    "--bin", "/usr/bin/true", "--out", str(out)]
            with mock.patch.object(sys, "argv", argv), \
                 mock.patch.object(proof_overhead, "warn_concurrent_build"), \
                 mock.patch.object(proof_overhead, "plan_solver_resources",
                                   return_value=plan), \
                 mock.patch.object(proof_overhead, "run",
                                   return_value=("SATISFIABLE", 1.0)):
                self.assertEqual(proof_overhead.main(), 0)
            envelope = json.loads(Path(out, "resource-envelope.json").read_text())
        self.assertEqual(envelope["memlimit_mb_per_child"], 777)
        self.assertEqual(envelope["nbcore_per_child"], 3)
        self.assertEqual(envelope["rss_grace_mb"], 0)
        self.assertEqual(envelope["memory_enforcement"],
                         "process-group rss_watchdog")

    def test_main_fails_on_cross_mode_verdict_mismatch(self):
        with tempfile.TemporaryDirectory() as td:
            corpus = Path(td, "corpus")
            corpus.mkdir()
            Path(corpus, "tiny.opb").write_text(
                "* #variable= 0 #constraint= 0\n"
            )
            out = Path(td, "out")
            plan = types.SimpleNamespace(jobs=1, memlimit_mb=777, nbcore=1,
                                         headroom_mb=16000)
            argv = ["proof_overhead.py", "--corpus", str(corpus),
                    "--bin", "/usr/bin/true", "--out", str(out)]
            outcomes = [
                ("SATISFIABLE", 1.0),
                ("SATISFIABLE", 1.0),
                ("UNSATISFIABLE", 1.0),
            ]
            with mock.patch.object(sys, "argv", argv), \
                 mock.patch.object(proof_overhead, "warn_concurrent_build"), \
                 mock.patch.object(proof_overhead, "plan_solver_resources",
                                   return_value=plan), \
                 mock.patch.object(proof_overhead, "run",
                                   side_effect=outcomes), \
                 contextlib.redirect_stdout(io.StringIO()):
                rc = proof_overhead.main()
        self.assertEqual(rc, 3)


class MiniZincResourceTest(unittest.TestCase):
    def _write_wrapper(self, directory):
        wrapper = Path(directory, "gtimeout")
        wrapper.write_text("#!/bin/sh\nshift\nexec \"$@\"\n")
        wrapper.chmod(0o755)
        return wrapper

    def test_parse_output_streams_last_objective(self):
        with tempfile.TemporaryFile() as output:
            output.write(
                b"_objective = 9;\n----------\n"
                b"_objective = 7;\n----------\n==========\n"
            )
            parsed = mzn_run.parse_output(output)
        self.assertEqual(parsed, (2, True, False, False, 7))

    def test_run_applies_plan_and_par8_cap(self):
        with tempfile.TemporaryDirectory() as td:
            self._write_wrapper(td)
            solver = Path(td, "minizinc")
            solver.write_text(
                "#!/bin/sh\n"
                "test \"$MEMLIMIT\" = 256 || exit 91\n"
                "test \"$NBCORE\" = 2 || exit 92\n"
                "case \" $* \" in *' -p 2 '*) ;; *) exit 93;; esac\n"
                "printf '_objective = 7;\\n----------\\n==========\\n'\n"
            )
            solver.chmod(0o755)
            env = dict(mzn_run.ENV,
                       PATH=f"{td}{os.pathsep}{mzn_run.ENV['PATH']}")
            with mock.patch.object(mzn_run, "MZN", str(solver)), \
                 mock.patch.object(mzn_run, "ENV", env):
                result = mzn_run.run_instance(
                    "tiny", "model.mzn", "instance.dzn", 1000, "par8",
                    256, 2, 2,
                )
        self.assertEqual(result["status"], "SC", result)
        self.assertEqual(result["objective"], 7)
        self.assertEqual(result["parallelism"], 2)
        self.assertFalse(result["memout"])

    def test_watchdog_memout_is_not_timeout(self):
        with tempfile.TemporaryDirectory() as td:
            self._write_wrapper(td)
            solver = Path(td, "minizinc")
            solver.write_text(
                "#!/bin/sh\n"
                f"exec {sys.executable} -c 'import time; "
                "b=bytearray(128*1024*1024); time.sleep(60)'\n"
            )
            solver.chmod(0o755)
            env = dict(mzn_run.ENV,
                       PATH=f"{td}{os.pathsep}{mzn_run.ENV['PATH']}")
            with mock.patch.object(mzn_run, "MZN", str(solver)), \
                 mock.patch.object(mzn_run, "ENV", env):
                result = mzn_run.run_instance(
                    "hog", "model.mzn", "instance.dzn", 1000, "fixed",
                    32, 1, 1,
                )
        self.assertEqual(result["status"], "MEMOUT", result)
        self.assertTrue(result["memout"])
        self.assertFalse(result["timed_out"])

    def test_main_persists_plan_and_uses_admitted_parallelism(self):
        with tempfile.TemporaryDirectory() as td:
            data = Path(td, "data")
            problem = Path(data, "tiny")
            problem.mkdir(parents=True)
            Path(problem, "model.mzn").write_text("solve satisfy;\n")
            Path(problem, "instance.dzn").write_text("\n")
            reference = Path(td, "results.json")
            reference.write_text(json.dumps({
                "results": {
                    "problems": ["tiny"],
                    "instances": [[0]],
                    "benchmarks": ["instance"],
                }
            }))
            output = Path(td, "run.json")
            plan = types.SimpleNamespace(jobs=2, memlimit_mb=777, nbcore=3,
                                         headroom_mb=16000)
            record = {"problem": "tiny", "data": "instance.dzn",
                      "status": "SC", "objective": 1, "time_ms": 1}
            argv = ["run.py", "1000", "par8", "4", str(output)]
            with mock.patch.object(sys, "argv", argv), \
                 mock.patch.object(mzn_run, "DATA", str(data)), \
                 mock.patch.object(mzn_run, "RESULTS", str(reference)), \
                 mock.patch.object(mzn_run, "MZN", "/usr/bin/true"), \
                 mock.patch.object(mzn_run, "TIMEOUT_BIN", "/usr/bin/true"), \
                 mock.patch.object(mzn_run, "warn_concurrent_build"), \
                 mock.patch.object(mzn_run, "plan_solver_resources",
                                   return_value=plan), \
                 mock.patch.object(mzn_run, "run_instance",
                                   return_value=record) as run:
                self.assertEqual(mzn_run.main(), 0)
            payload = json.loads(output.read_text())
        envelope = payload["resource_envelope"]
        self.assertEqual(envelope["requested_jobs"], 4)
        self.assertEqual(envelope["jobs"], 2)
        self.assertEqual(envelope["memlimit_mb_per_child"], 777)
        self.assertEqual(envelope["nbcore_per_child"], 3)
        self.assertEqual(envelope["parallelism_per_child"], 3)
        self.assertEqual(envelope["rss_grace_mb"], 0)
        run.assert_called_once()
        self.assertEqual(run.call_args.args[-3:], (777, 3, 3))


class TwoClubCampaignSyntaxTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.script = SCRIPTS / "two_club_campaign.sh"
        cls.source = cls.script.read_text()

    def test_shell_syntax(self):
        proc = subprocess.run(
            ["bash", "-n", str(self.script)],
            capture_output=True,
            text=True,
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)

    def test_rejects_noncanonical_or_out_of_range_partition_values(self):
        for overrides in (
            {"K": "08"},
            {"K": "21"},
            {"N": "0"},
            {"SECS": "0001"},
            {"SECS": "1234567890"},
        ):
            with self.subTest(overrides=overrides):
                proc = subprocess.run(
                    ["bash", str(self.script)],
                    env={**os.environ, **overrides},
                    capture_output=True,
                    text=True,
                )
                self.assertEqual(proc.returncode, 2, proc.stderr)
                self.assertIn("ERROR:", proc.stderr)

    def test_resume_identity_pins_solver_and_enforcement_code(self):
        self.assertIn("oom_guard_sha=$OOM_GUARD_SHA", self.source)
        self.assertIn("sdp_worker_sha=$SDP_WORKER_SHA", self.source)
        self.assertIn("sdp_certifier_sha=$SDP_CERTIFIER_SHA", self.source)
        self.assertIn("sdp_pilot_sha=$SDP_PILOT_SHA", self.source)
        self.assertIn(
            "resource_sha=$RESOURCE_SHA oom_guard_sha=$OOM_GUARD_SHA",
            self.source,
        )
        self.assertNotIn("two_club_file_probe --ignored", self.source)

    def test_marked_ab_schedule_is_typed_and_part_of_the_identity(self):
        self.assertIn(
            "branch_schedule=first_below_floor_half+"
            "marked_at_or_above_floor_half",
            self.source,
        )
        self.assertIn('local branch_rule=first', self.source)
        self.assertIn('branch_rule=marked', self.source)
        self.assertIn('--branch "$branch_rule"', self.source)
        self.assertIn("'--branch first|viol|marked'", self.source)
        self.assertIn('branch_rule=%s timestamp_utc=', self.source)

    def test_planning_and_binary_probe_use_the_private_snapshot(self):
        stage = self.source.index(
            'ARTIFACT_STAGE=$(mktemp -d "$ARTIFACT_ROOT/.stage.XXXXXXXX")'
        )
        bind_guard = self.source.index(
            'OOM_GUARD=$ARTIFACT_STAGE/_oom_guard.py'
        )
        bind_binary = self.source.index("BIN=$ARTIFACT_STAGE/ay-pb-dev")
        lease = self.source.index('python3 "$OOM_GUARD" lease')
        binary_probe = self.source.index('dev_help=$("$BIN" help')
        plan = self.source.index('PLAN=$(python3 "$OOM_GUARD" plan')
        identity = self.source.index("CAMPAIGN_ID=$(sha256_text")

        self.assertLess(stage, bind_guard)
        self.assertLess(stage, bind_binary)
        self.assertLess(bind_guard, lease)
        self.assertLess(bind_guard, plan)
        self.assertLess(bind_binary, binary_probe)
        self.assertLess(lease, identity)
        self.assertLess(binary_probe, identity)
        self.assertLess(plan, identity)

    def test_optimum_claim_requires_every_exact_identity_worker(self):
        self.assertIn('while [ "$worker" -lt "$N" ]', self.source)
        self.assertIn(
            "has no exact-identity proven row",
            self.source,
        )
        self.assertIn(
            'if [ "$worker_best" -ne "$SEED_SIZE" ]',
            self.source,
        )
        self.assertIn('if [ "$covered" -ne "$N" ]', self.source)
        self.assertIn(
            'grep -F " all_done=true run_status=ok "',
            self.source,
        )


class WindTunnelResourceEnvelopeTest(unittest.TestCase):
    def test_checker_rejects_incomplete_model_and_missing_optimum_objective(self):
        incomplete = wind_tunnel.check_answer(
            "* #variable= 2 #constraint= 1\n+1 x1 >= 1;\n",
            False,
            "SATISFIABLE",
            None,
            ["x1"],
        )
        missing_objective = wind_tunnel.check_answer(
            "* #variable= 1 #constraint= 0\nmin: +1 x1;\n",
            False,
            "OPTIMUM FOUND",
            None,
            ["x1"],
        )
        missing_sat_objective = wind_tunnel.check_answer(
            "* #variable= 1 #constraint= 0\nmin: +1 x1;\n",
            False,
            "SATISFIABLE",
            None,
            ["x1"],
        )
        self.assertTrue(incomplete.startswith("BAD(model-missing="), incomplete)
        self.assertTrue(missing_objective.startswith("BAD("), missing_objective)
        self.assertTrue(missing_sat_objective.startswith("BAD("),
                        missing_sat_objective)

    def test_main_records_and_applies_authoritative_plan(self):
        with tempfile.TemporaryDirectory() as td:
            corpus = Path(td, "DEC-LIN")
            corpus.mkdir()
            instance = Path(corpus, "tiny.opb.xz")
            with lzma.open(instance, "wt") as output:
                output.write("* #variable= 1 #constraint= 1\n+1 x1 >= 1;\n")
            solver = Path(td, "solver")
            solver.write_text(
                "#!/bin/sh\n"
                "test \"$MEMLIMIT\" = 512 || exit 91\n"
                "test \"$NBCORE\" = 2 || exit 92\n"
                "printf 's SATISFIABLE\\nv x1\\n'\n"
            )
            solver.chmod(0o755)
            out = Path(td, "out")
            argv = ["wind_tunnel.py", "--corpus", str(corpus), "--bin",
                    str(solver), "--jobs", "4", "--timeout-ms", "1000",
                    "--out", str(out)]
            plan = types.SimpleNamespace(jobs=2, memlimit_mb=512, nbcore=2,
                                         headroom_mb=16000)
            with mock.patch.object(sys, "argv", argv), \
                 mock.patch.object(wind_tunnel, "warn_concurrent_build"), \
                 mock.patch.object(wind_tunnel, "plan_solver_resources",
                                   return_value=plan), \
                 contextlib.redirect_stdout(io.StringIO()), \
                 contextlib.redirect_stderr(io.StringIO()):
                rc = wind_tunnel.main()
            summary = json.loads(Path(out, "summary.json").read_text())
        self.assertEqual(rc, 0)
        envelope = summary["resource_plan"]
        self.assertEqual(envelope["requested_jobs"], 4)
        self.assertEqual(envelope["jobs"], 2)
        self.assertEqual(envelope["memlimit_mb_per_child"], 512)
        self.assertEqual(envelope["nbcore_per_child"], 2)
        self.assertEqual(envelope["rss_grace_mb"], 0)


class ChccompResumeEnvelopeTest(unittest.TestCase):
    @staticmethod
    def _record(instance, solver, envelope):
        return {
            "instance": instance,
            "solver": solver,
            "status": "sat",
            "wall_sec": 1.0,
            "timeout_sec": envelope["timeout_sec"],
            "memlimit_mb": envelope["memlimit_mb_per_child"],
            "nbcore": envelope["nbcore_per_child"],
            "resource_envelope": envelope,
            "memout": False,
            "timed_out": False,
            "exit_code": 0,
            "verdict": "sat",
            "placeholder_verdict": False,
            "correct": True,
            "stderr_tail": "",
        }

    @staticmethod
    def _envelope(solver, memory=512):
        return {
            "schema": "ay.benchmark-resource-envelope/v1",
            "year": 2025,
            "track": "LIA-Lin",
            "task_count": 1,
            "task_set_sha256": "tasks",
            "benchmark_revision": "revision",
            "requested_jobs": 2,
            "jobs": 2,
            "memlimit_mb_per_child": memory,
            "nbcore_per_child": 1,
            "headroom_mb": 16000,
            "memory_enforcement": "process-group rss_watchdog",
            "rss_grace_mb": 0,
            "solver_env": {"MEMLIMIT": str(memory), "NBCORE": "1"},
            "native_memory_enforcement": "--memory" if solver == "ay" else None,
            "timeout_sec": 10,
            "parent_wall_timeout_sec": 15,
            "timeout_enforcement": "process-group SIGKILL + reap",
            "capture": "temporary files (bounded parent RAM)",
            "solver": solver,
            "solver_command": [solver, "<instance>"],
            "executable": {"path": solver, "size": 1, "sha256": solver},
            "harness": {"path": "chccomp_harness.py", "size": 1,
                        "sha256": "harness"},
        }

    def test_cross_solver_score_accepts_same_shared_envelope(self):
        with tempfile.TemporaryDirectory() as td, \
             mock.patch.object(chccomp_harness, "RESULTS_ROOT", Path(td)):
            output = Path(td, "2025", "LIA-Lin", "same")
            output.mkdir(parents=True)
            for solver in ("ay", "z3"):
                envelope = self._envelope(solver)
                Path(output, f"{solver}.jsonl").write_text(
                    json.dumps(self._record("x.yml", solver, envelope)) + "\n"
                )
            report = chccomp_harness.summarize(
                2025, "LIA-Lin", "same", ["ay", "z3"]
            )
        self.assertTrue(report["comparable"], report)

    def test_score_refuses_mixed_shared_envelopes(self):
        with tempfile.TemporaryDirectory() as td, \
             mock.patch.object(chccomp_harness, "RESULTS_ROOT", Path(td)):
            output = Path(td, "2025", "LIA-Lin", "mixed")
            output.mkdir(parents=True)
            for solver, memory in (("ay", 512), ("z3", 256)):
                envelope = self._envelope(solver, memory)
                Path(output, f"{solver}.jsonl").write_text(
                    json.dumps(self._record("x.yml", solver, envelope)) + "\n"
                )
            report = chccomp_harness.summarize(
                2025, "LIA-Lin", "mixed", ["ay", "z3"]
            )
        self.assertFalse(report["comparable"])
        self.assertTrue(report["comparability_issues"])

    def test_score_refuses_partial_task_set(self):
        with tempfile.TemporaryDirectory() as td, \
             mock.patch.object(chccomp_harness, "RESULTS_ROOT", Path(td)):
            output = Path(td, "2025", "LIA-Lin", "partial")
            output.mkdir(parents=True)
            envelope = self._envelope("ay")
            envelope["task_count"] = 2
            Path(output, "ay.jsonl").write_text(
                json.dumps(self._record("x.yml", "ay", envelope)) + "\n"
            )
            report = chccomp_harness.summarize(
                2025, "LIA-Lin", "partial", ["ay"]
            )
        self.assertFalse(report["comparable"])
        self.assertTrue(any("partial task set" in issue
                            for issue in report["comparability_issues"]))

    def test_resume_refuses_legacy_tag_before_spawning(self):
        task = chccomp_harness.Task("x.yml", os.devnull, "sat", False)
        args = argparse.Namespace(
            year=2025, track="LIA-Lin", only_gt=False, sample=0,
            seed=2026, limit=0, solvers="truebin", jobs=1, timeout=10,
            tag="legacy",
        )
        plan = types.SimpleNamespace(jobs=1, memlimit_mb=512, nbcore=1,
                                     headroom_mb=16000)
        with tempfile.TemporaryDirectory() as td, \
             mock.patch.object(chccomp_harness, "RESULTS_ROOT", Path(td)), \
             mock.patch.object(chccomp_harness, "load_track",
                               return_value=[task]), \
             mock.patch.object(chccomp_harness, "warn_concurrent_build"), \
             mock.patch.object(chccomp_harness, "plan_solver_resources",
                               return_value=plan), \
             mock.patch.dict(chccomp_harness.SOLVERS,
                             {"truebin": lambda _f, _t: ["/usr/bin/true"]}):
            output = Path(td, "2025", "LIA-Lin", "legacy")
            output.mkdir(parents=True)
            Path(output, "truebin.jsonl").write_text(
                json.dumps({"instance": "x.yml", "status": "sat"}) + "\n"
            )
            with contextlib.redirect_stderr(io.StringIO()):
                rc = chccomp_harness.cmd_run(args)
        self.assertEqual(rc, 2)

    def test_cmd_run_records_binary_and_exact_plan(self):
        with tempfile.TemporaryDirectory() as td:
            solver = Path(td, "solver")
            solver.write_text(
                "#!/bin/sh\n"
                "test \"$MEMLIMIT\" = 512 || exit 91\n"
                "test \"$NBCORE\" = 2 || exit 92\n"
                "printf 'sat\\n'\n"
            )
            solver.chmod(0o755)
            smt2 = Path(td, "x.smt2")
            smt2.write_text("(set-logic HORN)\n(check-sat)\n")
            task = chccomp_harness.Task("x.yml", str(smt2), "sat", False)
            args = argparse.Namespace(
                year=2025, track="LIA-Lin", only_gt=False, sample=0,
                seed=2026, limit=0, solvers="fake", jobs=4, timeout=10,
                tag="exact",
            )
            plan = types.SimpleNamespace(jobs=2, memlimit_mb=512, nbcore=2,
                                         headroom_mb=16000)
            with mock.patch.object(chccomp_harness, "RESULTS_ROOT", Path(td, "out")), \
                 mock.patch.object(chccomp_harness, "load_track",
                                   return_value=[task]), \
                 mock.patch.object(chccomp_harness, "warn_concurrent_build"), \
                 mock.patch.object(chccomp_harness, "plan_solver_resources",
                                   return_value=plan), \
                 mock.patch.dict(chccomp_harness.SOLVERS,
                                 {"fake": lambda _f, _t: [str(solver)]}), \
                 contextlib.redirect_stdout(io.StringIO()), \
                 contextlib.redirect_stderr(io.StringIO()):
                rc = chccomp_harness.cmd_run(args)
            result_path = Path(td, "out", "2025", "LIA-Lin", "exact",
                               "fake.jsonl")
            record = json.loads(result_path.read_text())
        self.assertEqual(rc, 0)
        self.assertEqual(record["status"], "sat", record)
        self.assertTrue(record["correct"])
        envelope = record["resource_envelope"]
        self.assertEqual(envelope["requested_jobs"], 4)
        self.assertEqual(envelope["jobs"], 2)
        self.assertEqual(envelope["nbcore_per_child"], 2)
        self.assertEqual(envelope["rss_grace_mb"], 0)
        self.assertEqual(envelope["executable"]["path"], str(solver.resolve()))


class PbcompResourceEnvelopeTest(unittest.TestCase):
    @staticmethod
    def _envelope(timeout=10.0, memory=512):
        return {
            "schema": "ay.benchmark-resource-envelope/v1",
            "requested_jobs": 2,
            "jobs": 2,
            "memlimit_mb_per_child": memory,
            "nbcore_per_child": 1,
            "headroom_mb": 16000,
            "memory_enforcement": "process-group rss_watchdog",
            "rss_grace_mb": 0,
            "solver_env": {"MEMLIMIT": str(memory), "NBCORE": "1"},
            "timeout_sec": timeout,
            "parent_wall_timeout_sec": timeout + 5,
            "timeout_enforcement": "process-group SIGKILL + reap",
            "capture": "temporary files (bounded parent RAM)",
            "checker": "python",
            "checker_jobs": 1,
            "checker_timeout_sec": None,
            "solver_command": ["solver", "<instance>"],
            "executable": {"path": "/solver", "size": 1, "sha256": "x"},
            "harness": {"path": "pbcomp_harness.py", "size": 1,
                        "sha256": "harness"},
            "instance_count": 1,
            "instance_set_sha256": pbcomp_harness.instance_set_digest(
                ["x.opb"]
            ),
        }

    def test_validator_accepts_one_complete_envelope(self):
        envelope = self._envelope()
        result = pbcomp_harness.Result(
            "x.opb", "DEC-LIN", "UNSATISFIABLE", None, 1.0, 0,
            None, False, memlimit_mb=512, nbcore=1, timeout_sec=10.0,
            resource_envelope=envelope,
        )
        actual, issue = pbcomp_harness.validate_result_envelopes([result])
        self.assertIsNone(issue)
        self.assertEqual(actual, envelope)

    def test_validator_refuses_legacy_record(self):
        result = pbcomp_harness.Result(
            "x.opb", "DEC-LIN", "UNKNOWN", None, 1.0, 0, None, False
        )
        _actual, issue = pbcomp_harness.validate_result_envelopes([result])
        self.assertIn("legacy", issue)

    def test_validator_refuses_partial_result_set(self):
        envelope = self._envelope()
        envelope["instance_count"] = 2
        result = pbcomp_harness.Result(
            "x.opb", "DEC-LIN", "UNSATISFIABLE", None, 1.0, 0,
            None, False, memlimit_mb=512, nbcore=1, timeout_sec=10.0,
            resource_envelope=envelope,
        )
        _actual, issue = pbcomp_harness.validate_result_envelopes([result])
        self.assertIn("partial result set", issue)

    def test_checker_rejects_malformed_rows_and_missing_objective(self):
        with tempfile.TemporaryDirectory() as td:
            malformed = Path(td, "malformed.opb")
            malformed.write_text(
                "* #variable= 1 #constraint= 1\n+1 x1 nonsense 1;\n"
            )
            with self.assertRaises(ValueError):
                pbcomp_harness.parse_instance(malformed)

            instance = Path(td, "objective.opb")
            instance.write_text(
                "* #variable= 1 #constraint= 0\nmin: +1 x1;\n"
            )
            result = pbcomp_harness.verify_solver_answer(
                "/usr/bin/false", instance, "SATISFIABLE", None, ["x1"],
                "python", {}, 512,
            )
        self.assertTrue(result[3], result)
        self.assertIn("no o-line", result[5])

    def test_watchdog_memout_is_distinct_from_timeout(self):
        with tempfile.TemporaryDirectory() as td:
            instance = Path(td, "tiny.opb")
            instance.write_text("* #variable= 1 #constraint= 0\n")
            solver = Path(td, "solver")
            solver.write_text(
                "#!/bin/sh\n"
                f"exec {sys.executable} -c 'import time; "
                "b=bytearray(128*1024*1024); time.sleep(60)'\n"
            )
            solver.chmod(0o755)
            result = pbcomp_harness.run_one(
                str(solver), instance, 10.0, "python", memlimit_mb=32,
                nbcore=1, resource_envelope=self._envelope(10.0, 32),
            )
        self.assertEqual(result.status, "MEMOUT", result)
        self.assertTrue(result.memout)
        self.assertFalse(result.timed_out)

    def test_cmd_run_applies_plan_and_persists_complete_envelope(self):
        with tempfile.TemporaryDirectory() as td:
            instances = Path(td, "instances", "DEC-LIN")
            instances.mkdir(parents=True)
            Path(instances, "tiny.opb").write_text(
                "* #variable= 1 #constraint= 1\n+1 x1 >= 1;\n"
            )
            solver = Path(td, "solver")
            solver.write_text(
                "#!/bin/sh\n"
                "test \"$MEMLIMIT\" = 512 || exit 91\n"
                "test \"$NBCORE\" = 2 || exit 92\n"
                "printf 's SATISFIABLE\\nv x1\\n'\n"
            )
            solver.chmod(0o755)
            output = Path(td, "run.jsonl")
            args = argparse.Namespace(
                jobs=4, timeout=2.0, limit=0, bin=str(solver),
                instances=str(Path(td, "instances")), checker="python",
                out=str(output), baseline="",
            )
            plan = types.SimpleNamespace(jobs=2, memlimit_mb=512, nbcore=2,
                                         headroom_mb=16000)
            with mock.patch.object(pbcomp_harness, "warn_concurrent_build"), \
                 mock.patch.object(pbcomp_harness, "plan_solver_resources",
                                   return_value=plan), \
                 contextlib.redirect_stdout(io.StringIO()), \
                 contextlib.redirect_stderr(io.StringIO()):
                rc = pbcomp_harness.cmd_run(args)
            record = json.loads(output.read_text())
            sidecar = json.loads(
                Path(str(output) + ".resource-envelope.json").read_text()
            )
        self.assertEqual(rc, 0)
        self.assertEqual(record["status"], "SATISFIABLE", record)
        self.assertTrue(record["verified"])
        self.assertEqual(record["resource_envelope"], sidecar)
        self.assertEqual(sidecar["requested_jobs"], 4)
        self.assertEqual(sidecar["jobs"], 2)
        self.assertEqual(sidecar["rss_grace_mb"], 0)


class ChccompRegressionComparabilityTest(unittest.TestCase):
    def test_resource_comparison_requires_complete_matching_fields(self):
        current = {
            "jobs": 2,
            "memlimit_mb_per_child": 512,
            "nbcore_per_child": 1,
            "memory_enforcement": "AY --memory + process-group rss_watchdog",
            "rss_grace_mb": 0,
            "solver_timeout_sec": 60,
            "parent_wall_timeout_sec": 75,
            "timeout_enforcement": "process-group SIGKILL + reap",
        }
        self.assertIsNone(chccomp_regression.resource_comparison_key(None))
        self.assertEqual(
            chccomp_regression.resource_comparison_key(dict(current)),
            current,
        )
        changed = dict(current, memlimit_mb_per_child=256)
        self.assertNotEqual(
            chccomp_regression.resource_comparison_key(current),
            chccomp_regression.resource_comparison_key(changed),
        )

    def test_main_marks_legacy_nonanswer_incomparable_and_persists_it(self):
        baseline_entry = {
            "year": "2025",
            "track": "LIA-Lin",
            "instance": "x.yml",
            "verdict": "sat",
            "wall": 1.0,
        }
        plan = types.SimpleNamespace(jobs=1, memlimit_mb=512, nbcore=1,
                                     headroom_mb=16000)

        def fake_run(entry, timeout_s, _binary, memlimit_mb, nbcore,
                     campaign_envelope):
            envelope = dict(campaign_envelope)
            envelope.update({
                "solver_timeout_sec": timeout_s,
                "parent_wall_timeout_sec": timeout_s + 15,
            })
            return {
                **entry,
                "status": "unknown",
                "memlimit_mb": memlimit_mb,
                "nbcore": nbcore,
                "baseline_resource_envelope": None,
                "resource_envelope": envelope,
                "memout": False,
                "timed_out": False,
                "exit_code": 0,
                "error": "",
            }

        with tempfile.TemporaryDirectory() as td:
            baseline = Path(td, "baseline.json")
            baseline.write_text(json.dumps({"x": baseline_entry}))
            results = Path(td, "latest.json")
            argv = ["chccomp_regression.py", "--timeout", "1", "--jobs",
                    "1", "--ay-bin", "/usr/bin/true"]
            with mock.patch.object(sys, "argv", argv), \
                 mock.patch.object(chccomp_regression, "BASELINE", baseline), \
                 mock.patch.object(chccomp_regression, "RESULTS", results), \
                 mock.patch.object(chccomp_regression,
                                   "warn_concurrent_build"), \
                 mock.patch.object(chccomp_regression,
                                   "plan_solver_resources",
                                   return_value=plan), \
                 mock.patch.object(chccomp_regression, "run",
                                   side_effect=fake_run), \
                 contextlib.redirect_stdout(io.StringIO()):
                rc = chccomp_regression.main()
            payload = json.loads(results.read_text())
        self.assertEqual(rc, 2)
        self.assertEqual(payload["summary"]["incomparable"], 1)
        self.assertEqual(payload["summary"]["regressed"], 0)

    def test_run_applies_memory_core_and_exact_watchdog_envelope(self):
        entry = {
            "year": "2025",
            "track": "LIA-Lin",
            "instance": "x.yml",
            "verdict": "sat",
            "wall": 0.1,
        }
        with tempfile.TemporaryDirectory() as td:
            smt2 = Path(td, "x.smt2")
            smt2.write_text("(set-logic HORN)\n(check-sat)\n")
            solver = Path(td, "solver")
            solver.write_text(
                "#!/bin/sh\n"
                "test \"$MEMLIMIT\" = 512 || exit 91\n"
                "test \"$NBCORE\" = 2 || exit 92\n"
                "printf 'sat\\n'\n"
            )
            solver.chmod(0o755)
            campaign = {
                "jobs": 1,
                "memlimit_mb_per_child": 512,
                "nbcore_per_child": 2,
            }
            with mock.patch.object(chccomp_regression, "resolve_smt2",
                                   return_value=str(smt2)):
                result = chccomp_regression.run(
                    entry, 1, str(solver), 512, 2, campaign
                )
        self.assertEqual(result["status"], "sat", result)
        self.assertEqual(result["nbcore"], 2)
        self.assertEqual(result["resource_envelope"]["rss_grace_mb"], 0)
        self.assertFalse(result["memout"])


if __name__ == "__main__":
    unittest.main()
