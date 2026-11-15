"""Shared isolation tests and resource-envelope tests for rewrite/SAT drivers."""

import importlib.util
import io
import json
import os
import select
import signal
import subprocess
import sys
import tempfile
import time
import types
import unittest
from pathlib import Path
from unittest import mock


SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))

import _oom_guard as oom_guard  # noqa: E402
import rewrite_oracle_check  # noqa: E402

if not hasattr(os, "killpg"):
    raise RuntimeError(
        "frontend resource-harness tests require POSIX process-group support"
    )


def load_script(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


sat_compare = load_script(
    "sat_compare_under_test", SCRIPTS / "sat_bench" / "sat_compare.py"
)


class CgroupDiscoveryTest(unittest.TestCase):
    @staticmethod
    def _bytes(mebibytes):
        return str(mebibytes * 1024 * 1024)

    def test_nested_v2_memory_uses_tightest_ancestor_remaining_capacity(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory, "cgroup2")
            team = Path(root, "team")
            leaf = Path(team, "job")
            leaf.mkdir(parents=True)
            Path(root, "memory.max").write_text(self._bytes(16_384))
            Path(root, "memory.current").write_text(self._bytes(15_360))
            Path(team, "memory.max").write_text(self._bytes(8_192))
            Path(team, "memory.current").write_text(self._bytes(2_048))
            Path(leaf, "memory.max").write_text("max")
            Path(leaf, "memory.current").write_text(self._bytes(512))
            cgroup = Path(directory, "self.cgroup")
            cgroup.write_text("0::/team/job\n")
            mountinfo = Path(directory, "mountinfo")
            mountinfo.write_text(
                f"29 23 0:26 / {root} rw - cgroup2 cgroup rw\n"
            )
            found = oom_guard.cgroup_memory_mb(
                cgroup_file=str(cgroup), mountinfo_file=str(mountinfo)
            )
        self.assertEqual(found, oom_guard.CgroupMemory(16_384, 15_360))

    def test_nested_v2_cpu_uses_leaf_cpuset_and_quota(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory, "cgroup2")
            team = Path(root, "team")
            leaf = Path(team, "job")
            leaf.mkdir(parents=True)
            Path(root, "cpuset.cpus.effective").write_text("0-7")
            Path(root, "cpu.max").write_text("max 100000")
            Path(team, "cpuset.cpus.effective").write_text("0-3")
            Path(team, "cpu.max").write_text("300000 100000")
            Path(leaf, "cpuset.cpus.effective").write_text("2-3")
            Path(leaf, "cpu.max").write_text("150000 100000")
            cgroup = Path(directory, "self.cgroup")
            cgroup.write_text("0::/team/job\n")
            mountinfo = Path(directory, "mountinfo")
            mountinfo.write_text(
                f"29 23 0:26 / {root} rw - cgroup2 cgroup rw\n"
            )
            found = oom_guard.cgroup_core_limit(
                cgroup_file=str(cgroup), mountinfo_file=str(mountinfo)
            )
        self.assertEqual(found, 1)

    def test_nested_v1_memory_maps_mount_root_and_membership(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory, "memory")
            team = Path(root, "team")
            leaf = Path(team, "job")
            leaf.mkdir(parents=True)
            Path(root, "memory.limit_in_bytes").write_text(self._bytes(16_384))
            Path(root, "memory.usage_in_bytes").write_text(self._bytes(4_096))
            Path(team, "memory.limit_in_bytes").write_text(self._bytes(6_144))
            Path(team, "memory.usage_in_bytes").write_text(self._bytes(2_048))
            Path(leaf, "memory.limit_in_bytes").write_text(str(1 << 62))
            Path(leaf, "memory.usage_in_bytes").write_text(self._bytes(512))
            cgroup = Path(directory, "self.cgroup")
            cgroup.write_text("5:memory:/docker/base/team/job\n")
            mountinfo = Path(directory, "mountinfo")
            mountinfo.write_text(
                f"31 23 0:27 /docker/base {root} rw - cgroup cgroup rw,memory\n"
            )
            found = oom_guard.cgroup_memory_mb(
                cgroup_file=str(cgroup), mountinfo_file=str(mountinfo)
            )
        self.assertEqual(found, oom_guard.CgroupMemory(6_144, 2_048))

    def test_nested_v1_cpu_and_cpuset_controllers_are_mapped_separately(self):
        with tempfile.TemporaryDirectory() as directory:
            cpu_root = Path(directory, "cpu")
            cpu_leaf = Path(cpu_root, "job")
            cpuset_root = Path(directory, "cpuset")
            cpuset_leaf = Path(cpuset_root, "job")
            cpu_leaf.mkdir(parents=True)
            cpuset_leaf.mkdir(parents=True)
            Path(cpu_leaf, "cpu.cfs_quota_us").write_text("150000")
            Path(cpu_leaf, "cpu.cfs_period_us").write_text("100000")
            Path(cpuset_leaf, "cpuset.cpus").write_text("0-2")
            cgroup = Path(directory, "self.cgroup")
            cgroup.write_text(
                "4:cpu,cpuacct:/slice/job\n3:cpuset:/slice/job\n"
            )
            mountinfo = Path(directory, "mountinfo")
            mountinfo.write_text(
                f"31 23 0:27 /slice {cpu_root} rw - cgroup cgroup rw,cpu,cpuacct\n"
                f"32 23 0:28 /slice {cpuset_root} rw - cgroup cgroup rw,cpuset\n"
            )
            found = oom_guard.cgroup_core_limit(
                cgroup_file=str(cgroup), mountinfo_file=str(mountinfo)
            )
        self.assertEqual(found, 1)


def _read_ready_pid(stream, timeout_s):
    deadline = time.monotonic() + timeout_s
    received = b""
    while b"\n" not in received:
        remaining = deadline - time.monotonic()
        if remaining <= 0 or not select.select([stream], [], [], remaining)[0]:
            raise AssertionError("guarded child did not publish complete readiness")
        chunk = os.read(stream.fileno(), 64)
        if not chunk:
            raise AssertionError("guarded child closed stdout before readiness")
        received += chunk
        if len(received) > 64:
            raise AssertionError("guarded child readiness exceeded its bound")
    text, _, extra = received.partition(b"\n")
    if extra or not text.isdigit() or int(text) <= 1:
        raise AssertionError("guarded child published invalid readiness")
    return int(text)


def _pipe_reaches_eof(stream, timeout_s):
    deadline = time.monotonic() + timeout_s
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0 or not select.select([stream], [], [], remaining)[0]:
            return False
        if not os.read(stream.fileno(), 4096):
            return True


class GuardCancellationTest(unittest.TestCase):
    def test_ancestor_walk_reaches_direct_parent(self):
        self.assertIn(os.getppid(), oom_guard._ancestor_pids())

    def test_run_cli_kills_child_group_when_wrapper_receives_sigterm(self):
        child_code = (
            "import os,time\n"
            "print(os.getpid(), flush=True)\n"
            "time.sleep(60)\n"
        )
        with tempfile.TemporaryFile() as wrapper_stderr:
            wrapper = subprocess.Popen(
                [
                    sys.executable,
                    str(SCRIPTS / "_oom_guard.py"),
                    "run",
                    "--limit-mb",
                    "4096",
                    "--",
                    sys.executable,
                    "-c",
                    child_code,
                ],
                stdout=subprocess.PIPE,
                stderr=wrapper_stderr,
            )
            child_pid = child_identity = None
            try:
                child_pid = _read_ready_pid(wrapper.stdout, 2)
                child_identity = oom_guard._watch_process_identity(child_pid)
                self.assertIsNotNone(child_identity, "guarded child birth unavailable")
                self.assertEqual(oom_guard._safe_getpgid(child_pid), child_pid)
                wrapper.send_signal(signal.SIGTERM)
                self.assertEqual(wrapper.wait(timeout=10), 128 + signal.SIGTERM)
                # This known child holds stdout throughout its sleep. EOF proves
                # exit on POSIX hosts without treating an absent /proc as death.
                self.assertTrue(
                    _pipe_reaches_eof(wrapper.stdout, 2),
                    "guarded child survived wrapper cancellation",
                )
            finally:
                primary_error = sys.exc_info()[1]
                try:
                    try:
                        if wrapper.poll() is None:
                            wrapper.terminate()
                        try:
                            wrapper.wait(timeout=10)
                        except subprocess.TimeoutExpired:
                            wrapper.kill()
                            wrapper.wait(timeout=10)
                    finally:
                        try:
                            if child_identity is not None:
                                oom_guard._terminate_process_group_if_authenticated(
                                    wrapper, child_pid, child_identity
                                )
                        finally:
                            self.assertTrue(
                                _pipe_reaches_eof(wrapper.stdout, 2),
                                "guarded child cleanup did not reach EOF",
                            )
                except BaseException as cleanup_error:
                    if primary_error is not None:
                        raise cleanup_error from primary_error
                    raise
                finally:
                    wrapper.stdout.close()
                    if primary_error is not None or sys.exc_info()[1] is not None:
                        try:
                            wrapper_stderr.seek(0)
                            captured = wrapper_stderr.read(65537)
                            print(
                                f"guarded wrapper returncode={wrapper.returncode}; "
                                f"wrapper_reaped={wrapper.returncode is not None}; "
                                f"stderr_first_65536_bytes={captured[:65536]!r}; "
                                f"truncated={len(captured) > 65536}",
                                file=sys.stderr,
                            )
                        except (OSError, ValueError):
                            # Reporting must not replace the original failure.
                            pass


class GuardFailureDiagnosticsTest(unittest.TestCase):
    def _failed_wrapper(self, payload, *, fail_cleanup=False):
        real_popen = subprocess.Popen
        children = []

        def spawn_failure(argv, **kwargs):
            self.assertEqual(argv[1], str(SCRIPTS / "_oom_guard.py"))
            child = real_popen(
                [sys.executable, "-c",
                 f"import sys; sys.stderr.buffer.write({payload!r}); sys.exit(23)"],
                **kwargs,
            )
            children.append(child)
            try:
                child.wait(timeout=10)
            except BaseException:
                child.kill()
                child.wait(timeout=10)
                raise
            return child

        captured = io.StringIO()
        expected = ("guarded child cleanup did not reach EOF" if fail_cleanup
                    else "guarded child closed stdout before readiness")
        case = GuardCancellationTest(
            "test_run_cli_kills_child_group_when_wrapper_receives_sigterm"
        )
        with mock.patch.object(subprocess, "Popen", side_effect=spawn_failure), \
             mock.patch.object(sys, "stderr", captured):
            if fail_cleanup:
                with mock.patch(__name__ + "._pipe_reaches_eof", return_value=False):
                    with self.assertRaisesRegex(AssertionError, expected) as caught:
                        case.test_run_cli_kills_child_group_when_wrapper_receives_sigterm()
            else:
                with self.assertRaisesRegex(AssertionError, expected) as caught:
                    case.test_run_cli_kills_child_group_when_wrapper_receives_sigterm()
        self.assertEqual(len(children), 1)
        self.assertEqual(children[0].returncode, 23)
        output = captured.getvalue()
        self.assertIn("returncode=23", output)
        self.assertIn("wrapper_reaped=True", output)
        return output, caught.exception

    def test_readiness_failure_retains_raw_stderr_after_reaping(self):
        output, _ = self._failed_wrapper(b"guard refused: \xff\n")
        self.assertIn("guard refused: \\xff", output)
        self.assertIn("truncated=False", output)

    def test_cleanup_failure_preserves_cause_and_stderr(self):
        output, error = self._failed_wrapper(b"guard cleanup diagnostic\n",
                                             fail_cleanup=True)
        self.assertIn("guard cleanup diagnostic", output)
        self.assertIsInstance(error.__cause__, AssertionError)
        self.assertIn("closed stdout before readiness", str(error.__cause__))

    def test_failure_stderr_capture_is_bounded(self):
        output, _ = self._failed_wrapper(b"A" * 65537)
        self.assertIn("truncated=True", output)
        self.assertLess(len(output), 66000)


class DirectRunnerEnvelopeTest(unittest.TestCase):
    def _solver(self, directory, body):
        path = Path(directory, "solver")
        path.write_text("#!/bin/sh\n" + body)
        path.chmod(0o755)
        return path


    def test_rewrite_runner_applies_memory_and_core_envelope(self):
        with tempfile.TemporaryDirectory() as directory:
            solver = self._solver(
                directory,
                "test \"$MEMLIMIT\" = 4096 || exit 91\n"
                "test \"$NBCORE\" = 2 || exit 92\n"
                "test \"$1\" = solve || exit 93\n"
                "test \"$2\" = --memory || exit 94\n"
                "test \"$3\" = 4096 || exit 95\n"
                "printf 'sat\\n'\n",
            )
            result = rewrite_oracle_check.run_one(
                str(solver),
                str(Path(directory, "case.smt2")),
                2,
                4096,
                dict(os.environ, MEMLIMIT="4096", NBCORE="2"),
            )
        self.assertEqual(result["status"], "sat", result)

    def test_sat_runner_gives_external_solver_same_exact_envelope(self):
        with tempfile.TemporaryDirectory() as directory:
            solver = self._solver(
                directory,
                "test \"$MEMLIMIT\" = 4096 || exit 91\n"
                "test \"$NBCORE\" = 2 || exit 92\n"
                "printf 's SATISFIABLE\\n'\n",
            )
            sat_compare.AY_MEMLIMIT_MB = 4096
            sat_compare.CHILD_ENV = dict(
                os.environ, MEMLIMIT="4096", NBCORE="2"
            )
            result = sat_compare.run_solver(
                [str(solver)], 2.0, "sat-compare-test"
            )
        self.assertEqual(result["verdict"], "SAT", result)


class PersistedEnvelopeTest(unittest.TestCase):
    PLAN = types.SimpleNamespace(
        jobs=1, memlimit_mb=3072, nbcore=2, headroom_mb=1024
    )


    def test_rewrite_main_persists_plan_and_results(self):
        with tempfile.TemporaryDirectory() as directory:
            case = Path(directory, "case.smt2")
            case.write_text("(check-sat)\n")
            oracle = Path(directory, "oracle.jsonl")
            oracle.write_text(json.dumps({"smt2": str(case), "verdict": "sat"}) + "\n")
            output = Path(directory, "result.json")
            argv = ["rewrite_oracle_check.py", "/bin/true", "--jobs", "3",
                    "--out", str(output)]
            fake = {"status": "sat", "wall_s": 0.1, "exit_code": 0}
            with mock.patch.object(sys, "argv", argv), \
                 mock.patch.object(rewrite_oracle_check, "ORACLE", str(oracle)), \
                 mock.patch.object(rewrite_oracle_check, "warn_concurrent_build"), \
                 mock.patch.object(rewrite_oracle_check, "plan_solver_resources",
                                   return_value=self.PLAN), \
                 mock.patch.object(rewrite_oracle_check, "run_one",
                                   return_value=fake) as run:
                rewrite_oracle_check.main()
            payload = json.loads(output.read_text())
            child_env = run.call_args.args[-1]
        self.assertEqual(child_env["MEMLIMIT"], "3072")
        self.assertEqual(child_env["NBCORE"], "2")
        self.assertEqual(payload["resource_plan"]["jobs"], 1)
        self.assertEqual(payload["counts"]["confirmed"], 1)

    def test_sat_main_persists_symmetric_plan(self):
        with tempfile.TemporaryDirectory() as directory:
            case = Path(directory, "case.cnf")
            case.write_text("p cnf 0 0\n")
            output = Path(directory, "result.json")
            argv = ["sat_compare.py", str(directory), "2", str(output), "3"]
            pair = {
                "cnf": "case.cnf",
                "path": str(case),
                "ay": {"verdict": "SAT", "time": 0.1, "rc": 10},
                "kissat": {"verdict": "SAT", "time": 0.1, "rc": 10},
                "disagree": False,
            }
            with mock.patch.object(sys, "argv", argv), \
                 mock.patch.object(sat_compare, "warn_concurrent_build"), \
                 mock.patch.object(sat_compare, "plan_solver_resources",
                                   return_value=self.PLAN), \
                 mock.patch.object(sat_compare, "one", return_value=pair):
                sat_compare.main()
            payload = json.loads(output.read_text())
        plan = payload["resource_plan"]
        self.assertEqual(plan["jobs"], 1)
        self.assertEqual(plan["memlimit_mb_per_child"], 3072)
        self.assertIn("AY and Kissat", plan["enforcement"])
        self.assertEqual(sat_compare.CHILD_ENV["NBCORE"], "2")


if __name__ == "__main__":
    unittest.main()
