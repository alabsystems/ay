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


mzn_run = load_script("mzn_challenge_run_under_test",
                      SCRIPTS / "mzn_challenge" / "run.py")
pbcomp_harness = load_script("pbcomp_harness_under_test",
                             SCRIPTS / "pbcomp_harness.py")
wind_tunnel = load_script("wind_tunnel_under_test",
                          SCRIPTS / "wind_tunnel.py")


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


class PbcompResourceEnvelopeTest(unittest.TestCase):
    @staticmethod
    def _envelope(timeout=10.0, memory=512):
        return {
            "schema": "ay.benchmark-resource-envelope/v2",
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
            "checker_command": None,
            "checker_executable": None,
            "solver_command": ["solver", "<instance>"],
            "executable": {"path": "/solver", "size": 1, "sha256": "x"},
            "harness": {"path": "pbcomp_harness.py", "size": 1,
                        "sha256": "harness"},
            "instance_count": 1,
            "instance_set_sha256": pbcomp_harness.instance_set_digest(
                ["x.opb"]
            ),
        }

    @staticmethod
    def _write_result_checker(path):
        path.write_text(
            "#!/bin/sh\n"
            "printf '%s\\n' \"$@\" > \"$AY_TEST_CHECKER_ARGS\"\n"
            "cat > \"$AY_TEST_CHECKER_STDIN\"\n"
            "printf 'c   %s\\n' \"$AY_TEST_CHECKER_FINDING\"\n"
            "printf 's VERIFICATION VERIFIED\\n'\n"
        )
        path.chmod(0o755)

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

    def test_validator_refuses_inexact_ay_checker_command(self):
        envelope = self._envelope()
        envelope["checker"] = "ay"
        envelope["checker_timeout_sec"] = 120
        envelope["checker_executable"] = {
            "path": "/ay-pb", "size": 1, "sha256": "checker",
        }
        envelope["checker_command"] = [
            "/ay-pb", "pb", "verify", "<instance>",
        ]
        result = pbcomp_harness.Result(
            "x.opb", "DEC-LIN", "UNSATISFIABLE", None, 1.0, 0,
            None, False, memlimit_mb=512, nbcore=1, timeout_sec=10.0,
            resource_envelope=envelope,
        )
        _actual, issue = pbcomp_harness.validate_result_envelopes([result])
        self.assertIn("exact checker command", issue)

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

    def test_ay_checker_reconstructs_model_only_transcript_and_objective(self):
        with tempfile.TemporaryDirectory() as td:
            instance = Path(td, "objective.opb")
            instance.write_text(
                "* #variable= 1 #constraint= 0\nmin: +7 x1;\n"
            )
            checker = Path(td, "ay-pb")
            self._write_result_checker(checker)
            args_capture = Path(td, "args")
            stdin_capture = Path(td, "stdin")
            env = dict(
                os.environ,
                AY_TEST_CHECKER_ARGS=str(args_capture),
                AY_TEST_CHECKER_STDIN=str(stdin_capture),
                AY_TEST_CHECKER_FINDING=(
                    "objective consistent: claimed = computed = 7"
                ),
            )
            ok, computed, reason = pbcomp_harness.check_solution_via_ay(
                str(checker), instance, 7, ["x1"], env, 512,
            )
            checker_args = args_capture.read_text().splitlines()
            transcript = stdin_capture.read_text()
        self.assertTrue(ok, reason)
        self.assertEqual(computed, 7)
        self.assertEqual(
            checker_args,
            ["pb", "verify", "--no-z3", str(instance)],
        )
        self.assertEqual(
            transcript,
            "o 7\ns SATISFIABLE\nv x1\n",
        )

    def test_ay_checker_parses_model_attains_without_o_line(self):
        with tempfile.TemporaryDirectory() as td:
            instance = Path(td, "objective.opb")
            instance.write_text(
                "* #variable= 1 #constraint= 0\nmin: +7 x1;\n"
            )
            checker = Path(td, "ay-pb")
            self._write_result_checker(checker)
            args_capture = Path(td, "args")
            stdin_capture = Path(td, "stdin")
            env = dict(
                os.environ,
                AY_TEST_CHECKER_ARGS=str(args_capture),
                AY_TEST_CHECKER_STDIN=str(stdin_capture),
                AY_TEST_CHECKER_FINDING=(
                    "objective not reported on an `o` line; model attains 7"
                ),
            )
            ok, computed, reason = pbcomp_harness.check_solution_via_ay(
                str(checker), instance, None, ["x1"], env, 512,
            )
            transcript = stdin_capture.read_text()
        self.assertTrue(ok, reason)
        self.assertEqual(computed, 7)
        self.assertEqual(transcript, "s SATISFIABLE\nv x1\n")

    def test_ay_checker_rejects_missing_o_when_objective_is_out_of_range(self):
        with tempfile.TemporaryDirectory() as td:
            instance = Path(td, "objective-overflow.opb")
            instance.write_text(
                "* #variable= 2 #constraint= 0\n"
                "min: +170141183460469231731687303715884105727 x1 "
                "+1 x2;\n"
            )
            checker = Path(td, "ay-pb")
            self._write_result_checker(checker)
            env = dict(
                os.environ,
                AY_TEST_CHECKER_ARGS=str(Path(td, "args")),
                AY_TEST_CHECKER_STDIN=str(Path(td, "stdin")),
                AY_TEST_CHECKER_FINDING=(
                    "objective not reported; model objective is outside the "
                    "i128 reporting range"
                ),
            )
            result = pbcomp_harness.verify_solver_answer(
                "/unused/solver", instance, "SATISFIABLE", None,
                ["x1", "x2"], "ay", env, 512,
                checker_bin_path=str(checker),
            )
        self.assertTrue(result[2], result)
        self.assertTrue(result[3], result)
        self.assertIn("no o-line", result[5])

    def test_ay_checker_binary_is_same_or_deterministic_sibling(self):
        same = pbcomp_harness.derived_pb_checker_binary(
            "/tmp/ay-pb", {"path": "/resolved/ay-pb"},
        )
        sibling = pbcomp_harness.derived_pb_checker_binary(
            "/tmp/ay", {"path": "/resolved/ay"},
        )
        self.assertEqual(same, "/resolved/ay-pb")
        self.assertEqual(sibling, "/resolved/ay-pb")

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
        self.assertIsNone(sidecar["checker_command"])
        self.assertIsNone(sidecar["checker_executable"])

    def test_cmd_run_uses_sibling_ay_pb_checker_and_records_provenance(self):
        with tempfile.TemporaryDirectory() as td:
            instances = Path(td, "instances", "OPT-LIN")
            instances.mkdir(parents=True)
            instance = Path(instances, "tiny.opb")
            instance.write_text(
                "* #variable= 1 #constraint= 0\nmin: +7 x1;\n"
            )
            solver = Path(td, "ay")
            solver.write_text(
                "#!/bin/sh\n"
                "test \"$MEMLIMIT\" = 512 || exit 91\n"
                "test \"$NBCORE\" = 2 || exit 92\n"
                "printf 'o 7\\ns OPTIMUM FOUND\\nv x1\\n'\n"
            )
            solver.chmod(0o755)
            checker = Path(td, "ay-pb")
            self._write_result_checker(checker)
            args_capture = Path(td, "checker-args")
            stdin_capture = Path(td, "checker-stdin")
            output = Path(td, "run.jsonl")
            args = argparse.Namespace(
                jobs=4, timeout=2.0, limit=0, bin=str(solver),
                instances=str(Path(td, "instances")), checker="ay",
                out=str(output), baseline="",
            )
            plan = types.SimpleNamespace(jobs=2, memlimit_mb=512, nbcore=2,
                                         headroom_mb=16000)
            checker_env = {
                "AY_TEST_CHECKER_ARGS": str(args_capture),
                "AY_TEST_CHECKER_STDIN": str(stdin_capture),
                "AY_TEST_CHECKER_FINDING": (
                    "objective consistent: claimed = computed = 7"
                ),
            }
            with mock.patch.dict(os.environ, checker_env, clear=False), \
                 mock.patch.object(pbcomp_harness, "warn_concurrent_build"), \
                 mock.patch.object(pbcomp_harness, "plan_solver_resources",
                                   return_value=plan), \
                 contextlib.redirect_stdout(io.StringIO()), \
                 contextlib.redirect_stderr(io.StringIO()):
                rc = pbcomp_harness.cmd_run(args)
            record = json.loads(output.read_text())
            sidecar = json.loads(
                Path(str(output) + ".resource-envelope.json").read_text()
            )
            transcript = stdin_capture.read_text()
        self.assertEqual(rc, 0)
        self.assertEqual(record["status"], "OPTIMUM FOUND", record)
        self.assertTrue(record["verified"], record)
        self.assertFalse(record["wrong_answer"], record)
        self.assertEqual(transcript, "o 7\ns SATISFIABLE\nv x1\n")
        self.assertEqual(
            sidecar["checker_executable"]["path"], str(checker.resolve())
        )
        self.assertTrue(sidecar["checker_executable"]["sha256"])
        self.assertEqual(
            sidecar["checker_command"],
            [str(checker.resolve()), "pb", "verify", "--no-z3",
             "<instance>"],
        )

    def test_cmd_run_refuses_missing_sibling_checker_before_planning(self):
        with tempfile.TemporaryDirectory() as td:
            instances = Path(td, "instances")
            instances.mkdir()
            Path(instances, "tiny.opb").write_text(
                "* #variable= 1 #constraint= 0\n"
            )
            solver = Path(td, "ay")
            solver.write_text("#!/bin/sh\nexit 0\n")
            solver.chmod(0o755)
            args = argparse.Namespace(
                jobs=1, timeout=2.0, limit=0, bin=str(solver),
                instances=str(instances), checker="ay",
                out=str(Path(td, "run.jsonl")), baseline="",
            )
            with mock.patch.object(
                pbcomp_harness, "warn_concurrent_build"
            ) as warn, contextlib.redirect_stderr(io.StringIO()) as stderr:
                rc = pbcomp_harness.cmd_run(args)
        self.assertEqual(rc, 2)
        warn.assert_not_called()
        self.assertIn("checker executable unavailable", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
