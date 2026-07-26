# ay-script: oom-guard-tests
"""Tests for scripts/_oom_guard.py resource planning, the rss-watchdog
memory backstop, and the harness wiring (wind-tunnel child-env merge,
pbcomp child env, chccomp/chc envelope recording).

The repo had no prior convention for testing scripts/*.py (grep of ci/ and
tests/ finds only fuzz drivers invoked directly), so these are plain stdlib
unittest, runnable via:

    python3 -m unittest discover scripts/tests
"""
import contextlib
import io
import lzma
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import types
import unittest
from pathlib import Path
from unittest import mock

SCRIPTS_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, SCRIPTS_DIR)

import _oom_guard as og  # noqa: E402
import chccomp_harness  # noqa: E402
import smtcomp_harness  # noqa: E402
import chccomp_regression  # noqa: E402
import chccomp_track_sweep  # noqa: E402
import pb_sweep  # noqa: E402
import pbcomp_harness  # noqa: E402
import wind_tunnel  # noqa: E402

_missing_posix_apis = [
    name for name in ("getuid", "getpgid") if not hasattr(os, name)
]
if os.name != "posix" or _missing_posix_apis:
    raise RuntimeError(
        "OOM-guard tests require POSIX user and process-group APIs; missing "
        + ", ".join(_missing_posix_apis)
    )
TRUE_BIN = Path("/usr/bin/true")
if not TRUE_BIN.is_file():
    raise RuntimeError(
        "OOM-guard tests require the POSIX /usr/bin/true executable"
    )


class PlanSolverResourcesTest(unittest.TestCase):
    """Pure-planner tests with injected RAM/cores (no host detection)."""

    def test_incident_box_24g_14core_jobs6(self):
        # The 2026-07-11 panic config: 24 GiB / 14 cores, --jobs 6. The plan
        # must keep a sane nonzero budget after headroom and give every job
        # an enforced MEMLIMIT >= 1024 MiB.
        plan = og.plan_solver_resources(6, ram_mb=24576, cores=14)
        self.assertEqual(plan.jobs, 6)  # 6 jobs fit above the floor
        self.assertGreaterEqual(plan.memlimit_mb, 1024)
        budget = 24576 - plan.headroom_mb
        self.assertGreater(budget, 0)  # sane nonzero budget on a 24 GiB box
        self.assertLessEqual(plan.jobs * plan.memlimit_mb, budget)
        self.assertEqual(plan.nbcore, 2)  # 14 cores // 6 jobs

    def test_incident_box_overcommit_capped(self):
        # Requesting more jobs than the budget can float at the 1024 MiB
        # floor must reduce jobs, never starve each job below the floor.
        plan = og.plan_solver_resources(16, ram_mb=24576, cores=14)
        self.assertLess(plan.jobs, 16)
        self.assertGreaterEqual(plan.memlimit_mb, 1024)
        self.assertLessEqual(plan.jobs * plan.memlimit_mb,
                             24576 - plan.headroom_mb)

    def test_huge_box_noop(self):
        # 256 GiB box: the requested config already fits => jobs unchanged.
        plan = og.plan_solver_resources(6, ram_mb=262144, cores=64)
        self.assertEqual(plan.jobs, 6)
        self.assertGreaterEqual(plan.memlimit_mb, 1024)
        self.assertEqual(plan.nbcore, 10)  # 64 // 6

    def test_tiny_ram_collapses_to_one_job(self):
        # 8 GiB box: headroom swallows RAM; jobs collapse to 1 and the
        # MEMLIMIT floor is still respected.
        plan = og.plan_solver_resources(8, ram_mb=8192, cores=8)
        self.assertEqual(plan.jobs, 1)
        self.assertGreaterEqual(plan.memlimit_mb, 1024)

    def test_headroom_override(self):
        # --mem-headroom-mb for rented big boxes: override is honored exactly.
        plan = og.plan_solver_resources(6, ram_mb=24576, cores=14,
                                        headroom_mb=4096)
        self.assertEqual(plan.headroom_mb, 4096)
        self.assertEqual(plan.memlimit_mb, (24576 - 4096) // 6)

    def test_explicit_unknown_ram_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "ram_mb must be positive"):
            og.plan_solver_resources(6, ram_mb=0, cores=14)

    def test_invalid_planner_inputs_fail_closed(self):
        for kwargs in (
                {"headroom_mb": -1},
                {"mem_floor_mb": 0},
                {"cores": 0},
        ):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                og.plan_solver_resources(1, ram_mb=8192, **kwargs)

    def test_automatic_unknown_ram_fails_closed(self):
        with mock.patch.object(og, "physical_ram_mb", return_value=0), \
             mock.patch.object(og, "cgroup_memory_mb", return_value=None):
            with self.assertRaisesRegex(RuntimeError, "effective RAM ceiling"):
                og.plan_solver_resources(2)

    def test_cgroup_limit_and_current_usage_bound_automatic_plan(self):
        cgroup = og.CgroupMemory(limit_mb=8192, current_mb=2048)
        with mock.patch.object(og, "physical_ram_mb", return_value=8192), \
             mock.patch.object(og, "cgroup_memory_mb", return_value=cgroup):
            plan = og.plan_solver_resources(2, cores=4, acquire_lease=False)
        self.assertEqual(plan.headroom_mb, 1024)
        self.assertEqual(plan.jobs, 2)
        self.assertEqual(plan.memlimit_mb, 2560)
        self.assertLessEqual(
            plan.jobs * plan.memlimit_mb + plan.headroom_mb,
            cgroup.limit_mb - cgroup.current_mb,
        )

    def test_cgroup_with_no_child_budget_fails_closed(self):
        cgroup = og.CgroupMemory(limit_mb=4096, current_mb=3500)
        with mock.patch.object(og, "physical_ram_mb", return_value=4096), \
             mock.patch.object(og, "cgroup_memory_mb", return_value=cgroup):
            with self.assertRaisesRegex(RuntimeError, "need at least"):
                og.plan_solver_resources(1, cores=1)

    def test_cgroup_v2_files_are_injectable(self):
        with tempfile.TemporaryDirectory() as td:
            limit = Path(td, "memory.max")
            current = Path(td, "memory.current")
            limit.write_text(str(6 * 1024 * 1024 * 1024))
            current.write_text(str(2 * 1024 * 1024 * 1024))
            value = og.cgroup_memory_mb([(str(limit), str(current))])
        self.assertEqual(value, og.CgroupMemory(6144, 2048))

    def test_effective_core_count_honors_affinity_and_cgroup(self):
        with mock.patch.object(og, "_host_physical_core_count", return_value=16), \
             mock.patch.object(og.os, "sched_getaffinity", return_value=set(range(4))), \
             mock.patch.object(og, "cgroup_core_limit", return_value=2):
            self.assertEqual(og.physical_core_count(), 2)

    def test_cgroup_cpu_limits_are_injectable(self):
        with tempfile.TemporaryDirectory() as td:
            cpuset = Path(td, "cpuset")
            cpu_max = Path(td, "cpu.max")
            cpuset.write_text("0-3,8")
            cpu_max.write_text("250000 100000")
            value = og.cgroup_core_limit(
                cpuset_paths=[str(cpuset)], quota_pairs=[(str(cpu_max), None)]
            )
        self.assertEqual(value, 2)

    def test_nbcore_min_one(self):
        plan = og.plan_solver_resources(8, ram_mb=262144, cores=4)
        self.assertEqual(plan.nbcore, 1)

    def test_second_independent_plan_cannot_reuse_active_lease(self):
        with mock.patch.object(og, "_ACTIVE_HARNESS_LEASE", object()):
            with self.assertRaisesRegex(RuntimeError, "already active"):
                og.plan_solver_resources(
                    1,
                    ram_mb=8192,
                    cores=1,
                    headroom_mb=1024,
                    acquire_lease=True,
                )

    def test_production_lease_path_is_tmpdir_independent(self):
        with mock.patch.dict(os.environ, {"TMPDIR": "/tmp/first-campaign"}):
            first = og._host_harness_lease_path()
        with mock.patch.dict(os.environ, {"TMPDIR": "/tmp/second-campaign"}):
            second = og._host_harness_lease_path()
        expected = f"/tmp/ay-oom-guard-{os.getuid()}.lock"
        self.assertEqual(first, expected)
        self.assertEqual(second, expected)

    def test_hidden_lease_path_requires_absolute_path(self):
        with self.assertRaisesRegex(ValueError, "must be absolute"):
            og.acquire_harness_lease("relative test lease", _lock_path="lease.lock")

    def test_hidden_lease_path_coordinates_sidecars_with_distinct_tmpdirs(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            first_tmp = root / "first-tmp"
            second_tmp = root / "second-tmp"
            first_tmp.mkdir()
            second_tmp.mkdir()
            lock_path = root / "isolated-host-lease.lock"
            command = [
                sys.executable,
                og.__file__,
                "lease",
                "--test-lock-path",
                str(lock_path),
            ]
            first_env = dict(os.environ, TMPDIR=str(first_tmp))
            second_env = dict(os.environ, TMPDIR=str(second_tmp))
            first = subprocess.Popen(
                command,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                env=first_env,
            )
            try:
                ready = []
                reader = threading.Thread(
                    target=lambda: ready.append(first.stdout.readline()),
                    daemon=True,
                )
                reader.start()
                reader.join(timeout=10)
                self.assertFalse(reader.is_alive(), "first lease sidecar did not arm")
                self.assertEqual(ready, [b"AY_OOM_HARNESS_LEASE_READY_V1\n"])

                blocked = subprocess.run(
                    command,
                    input=b"",
                    capture_output=True,
                    timeout=10,
                    env=second_env,
                    check=False,
                )
                self.assertNotEqual(blocked.returncode, 0)
                self.assertNotIn(
                    b"AY_OOM_HARNESS_LEASE_READY_V1", blocked.stdout
                )

                first.stdin.close()
                self.assertEqual(first.wait(timeout=10), 0)
                replacement = subprocess.run(
                    command,
                    input=b"",
                    capture_output=True,
                    timeout=10,
                    env=second_env,
                    check=False,
                )
                self.assertEqual(replacement.returncode, 0, replacement.stderr)
                self.assertEqual(
                    replacement.stdout, b"AY_OOM_HARNESS_LEASE_READY_V1\n"
                )
            finally:
                if first.poll() is None:
                    first.kill()
                    first.wait(timeout=5)
                for stream in (first.stdin, first.stdout, first.stderr):
                    if stream is not None:
                        stream.close()

    def test_count_active_rustc_returns_count(self):
        if not Path("/proc").is_dir():
            with self.assertRaisesRegex(RuntimeError, "cannot inspect build processes"):
                og.count_active_rustc()
            return
        self.assertIsInstance(og.count_active_rustc(), int)
        self.assertGreaterEqual(og.count_active_rustc(), 0)

    def test_warn_concurrent_build_preserves_process_scan_failure(self):
        with mock.patch.object(
            og,
            "count_active_rustc",
            side_effect=RuntimeError("process scan unavailable"),
        ):
            with self.assertRaisesRegex(RuntimeError, "process scan unavailable"):
                og.warn_concurrent_build()

    def test_build_detection_includes_targo_and_trustc_and_excludes_ancestor(self):
        with tempfile.TemporaryDirectory() as td:
            proc = Path(td)

            def process(pid, name, command, state="S"):
                directory = proc / str(pid)
                directory.mkdir()
                (directory / "comm").write_text(name + "\n")
                (directory / "stat").write_text(
                    f"{pid} ({name}) {state} 1 0 0 0 0\n"
                )
                (directory / "cmdline").write_bytes(
                    b"\0".join(token.encode() for token in command) + b"\0"
                )

            process(100, "compiler_consumer", ["compiler_consumer", "crate.rs"])
            process(101, "targo", ["targo", "build"])
            process(102, "targo", ["targo", "metadata"])
            process(103, "cargo", ["cargo", "test"])
            process(104, "rustc", ["rustc", "done.rs"], state="Z")
            process(105, "compiler_consumer", ["compiler_consumer", "paused.rs"], state="T")
            process(106, "targo", ["targo", "test"], state="T")

            self.assertEqual(
                og.count_active_rustc(proc_root=td, ancestor_pids={103}),
                2,
            )

    def test_build_process_walk_is_bounded(self):
        with tempfile.TemporaryDirectory() as td:
            Path(td, "1").mkdir()
            Path(td, "2").mkdir()
            with self.assertRaisesRegex(RuntimeError, "inspection cap"):
                og._named_build_processes(td, max_entries=1)


class WindTunnelEnvMergeTest(unittest.TestCase):
    """wind_tunnel.resource_env: the admission plan is authoritative."""

    def test_plan_injected_when_no_overrides(self):
        env = wind_tunnel.resource_env({}, 1429, 2)
        self.assertEqual(env["MEMLIMIT"], "1429")
        self.assertEqual(env["NBCORE"], "2")

    def test_plan_memlimit_wins_over_explicit_env(self):
        env = wind_tunnel.resource_env({"MEMLIMIT": "4096"}, 1429, 2)
        self.assertEqual(env["MEMLIMIT"], "1429")
        self.assertEqual(env["NBCORE"], "2")

    def test_plan_nbcore_wins_and_unrelated_env_is_retained(self):
        env = wind_tunnel.resource_env({"NBCORE": "8", "FOO": "bar"}, 1429, 2)
        self.assertEqual(env["NBCORE"], "2")
        self.assertEqual(env["MEMLIMIT"], "1429")
        self.assertEqual(env["FOO"], "bar")

    def test_zero_plan_values_not_injected(self):
        # memlimit 0 = RAM unknown: nothing forced into the child env.
        env = wind_tunnel.resource_env({}, 0, 0)
        self.assertNotIn("MEMLIMIT", env)
        self.assertNotIn("NBCORE", env)


class ChcEnvelopeRecordingTest(unittest.TestCase):
    """The CHC harnesses must record the enforced per-child --memory envelope:
    baselines/sweeps were measured under ay's 85%-of-RAM default, so results
    taken under different envelopes are not comparable and a solved->unknown
    flip under a tight cap must be attributable to the cap."""

    def test_track_sweep_record_carries_memlimit(self):
        task = types.SimpleNamespace(smt2=os.devnull, verdict=None,
                                     rel_id="fam/x.smt2")
        rec = chccomp_track_sweep.run_one(task, 5, str(TRUE_BIN),
                                          memlimit_mb=777)
        self.assertEqual(rec["memlimit_mb"], 777)
        self.assertEqual(rec["status"], "unknown")

    def test_track_sweep_rejects_missing_memory_envelope(self):
        task = types.SimpleNamespace(smt2=os.devnull, verdict=None,
                                     rel_id="fam/x.smt2")
        with self.assertRaises(ValueError):
            chccomp_track_sweep.run_one(task, 5, str(TRUE_BIN))

    def test_regression_record_carries_memlimit(self):
        entry = {"year": "2025", "track": "LIA-Lin", "instance": "i.yml",
                 "verdict": "sat", "wall": 1.0}
        with mock.patch.object(chccomp_regression, "resolve_smt2",
                               return_value=os.devnull):
            rec = chccomp_regression.run(entry, 1, str(TRUE_BIN),
                                         memlimit_mb=777)
        self.assertEqual(rec["memlimit_mb"], 777)
        self.assertEqual(rec["status"], "unknown")


class RssWatchdogTest(unittest.TestCase):
    """rss_watchdog: the external backstop for solver children that do not
    enforce their envelope themselves (the main ay binary's `pb` subcommand
    ignores MEMLIMIT; external solvers have no knob)."""

    HOG = ("import time\n"
           "b = bytearray(400 * 1024 * 1024)\n"  # ~400 MiB RSS
           "time.sleep(60)\n")

    def _spawn(self, code):
        return subprocess.Popen([sys.executable, "-c", code],
                                stdout=subprocess.DEVNULL,
                                stderr=subprocess.DEVNULL,
                                start_new_session=True)

    def test_kills_child_over_envelope(self):
        proc = self._spawn(self.HOG)
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr):
            guard = og.rss_watchdog(proc, 32, label="test", poll_s=0.1,
                                    grace_mb=0)
            try:
                rc = proc.wait(timeout=30)
            finally:
                guard.stop()
        self.assertTrue(guard.breached)
        self.assertEqual(rc, -signal.SIGKILL)
        self.assertIn("memout", stderr.getvalue())

    def test_child_within_envelope_untouched(self):
        proc = self._spawn("import time; time.sleep(0.5)")
        guard = og.rss_watchdog(proc, 10000, label="test", poll_s=0.1)
        rc = proc.wait(timeout=30)
        guard.stop()
        self.assertFalse(guard.breached)
        self.assertEqual(rc, 0)

    def test_rss_watchdog_refuses_non_group_leader(self):
        proc = mock.Mock(pid=1234)
        with mock.patch.object(og.os, "getpgid", return_value=4321), \
             mock.patch.object(og, "_RssWatchdog") as watchdog:
            with self.assertRaisesRegex(RuntimeError, "not its process-group leader"):
                og.rss_watchdog(proc, 128, label="wrong-group")
        watchdog.assert_not_called()

    def test_rss_watchdog_rejects_invalid_poll_intervals(self):
        proc = mock.Mock(pid=1234)
        with mock.patch.object(og.os, "getpgid", return_value=1234):
            for poll_s in (0, -0.1, float("nan"), float("inf")):
                with self.subTest(poll_s=poll_s), self.assertRaises(ValueError):
                    og.rss_watchdog(proc, 128, poll_s=poll_s, grace_mb=0)

    def test_identity_loss_is_terminal_and_never_kills_reused_group(self):
        proc = mock.Mock(pid=4242)
        with mock.patch.object(
            og, "_watch_process_identity", return_value=(4242, "replacement")
        ), mock.patch.object(
            og, "_safe_getpgid", return_value=4242
        ), mock.patch.object(
            og, "_terminate_process_group"
        ) as terminate:
            guard = og._RssWatchdog(
                proc,
                4242,
                128,
                0.001,
                "identity-loss-test",
                (4242, "original"),
            )
            try:
                self.assertTrue(
                    guard.wait_terminal(1),
                    "identity loss must terminate the monitor instead of polling a raw PGID",
                )
                self.assertTrue(guard.identity_lost)
                self.assertFalse(guard.breached)
                self.assertFalse(guard.terminate_if_authenticated())
            finally:
                guard.stop()
        terminate.assert_not_called()

    def test_watch_server_shutdown_uses_authenticated_cleanup(self):
        class FakeGuard:
            armed = True
            breached = False
            breach_time_ns = None

            def __init__(self):
                self.cleanup_calls = 0

            def wait_terminal(self, timeout=None):
                time.sleep(min(timeout or 0, 0.001))
                return False

            def terminate_if_authenticated(self):
                self.cleanup_calls += 1
                return False

            def stop(self):
                pass

        guard = FakeGuard()
        proc = types.SimpleNamespace(pid=4242, pgid=4242)
        input_stream = io.BytesIO(b"WATCH 1 4242 128 74657374\n")
        output_stream = io.BytesIO()
        with mock.patch.object(og, "_AttachedProcess", return_value=proc), \
             mock.patch.object(
                 og, "_group_watch_identity", return_value=(4242, "original")
             ), \
             mock.patch.object(og, "rss_watchdog", return_value=guard), \
             mock.patch.object(og, "_terminate_process_group") as terminate:
            og.serve_watchdog_requests(input_stream, output_stream)
        self.assertGreaterEqual(guard.cleanup_calls, 1)
        terminate.assert_not_called()

    def test_watch_existing_process_uses_same_enforcement(self):
        proc = self._spawn(
            "import time; b = bytearray(64 * 1024 * 1024); time.sleep(60)"
        )
        breached = og.watch_existing_process(
            proc.pid, 16, label="attached-test", poll_s=0.02, grace_mb=0
        )
        rc = proc.wait(timeout=30)
        self.assertTrue(breached)
        self.assertEqual(rc, -signal.SIGKILL)

    def test_watch_existing_process_fails_closed_if_child_is_gone(self):
        with mock.patch.object(
            og, "_AttachedProcess", side_effect=ProcessLookupError("gone")
        ):
            self.assertTrue(og.watch_existing_process(999999, 128))

    def test_watch_existing_process_signals_ready_after_arming(self):
        proc = self._spawn("import time; time.sleep(0.2)")
        reaper = threading.Thread(target=proc.wait)
        reaper.start()
        with tempfile.TemporaryDirectory() as td:
            ready = Path(td, "ready")
            breached = og.watch_existing_process(
                proc.pid,
                10000,
                label="ready-test",
                poll_s=0.01,
                grace_mb=0,
                ready_file=str(ready),
            )
            self.assertFalse(breached)
            self.assertEqual(ready.read_text(), "ready\n")
        reaper.join(timeout=5)
        self.assertFalse(reaper.is_alive())
        self.assertEqual(proc.returncode, 0)

    def test_watch_existing_process_refuses_ready_when_watchdog_is_unarmed(self):
        proc = self._spawn("import time; time.sleep(60)")
        with tempfile.TemporaryDirectory() as td, mock.patch.object(
            og, "rss_watchdog", return_value=og._NoopWatchdog()
        ):
            ready = Path(td, "ready")
            self.assertTrue(
                og.watch_existing_process(
                    proc.pid,
                    10000,
                    label="unarmed-ready-test",
                    ready_file=str(ready),
                )
            )
            self.assertFalse(ready.exists())
        os.killpg(proc.pid, signal.SIGKILL)
        proc.wait(timeout=5)

    def test_terminating_watch_sidecar_kills_target_group(self):
        with tempfile.TemporaryDirectory() as td:
            ready = Path(td, "ready")
            descendant_pid = Path(td, "descendant.pid")
            target_code = (
                "import pathlib,subprocess,sys,time; "
                "child=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)']); "
                f"pathlib.Path({str(descendant_pid)!r}).write_text(str(child.pid)); "
                "time.sleep(60)"
            )
            target = subprocess.Popen(
                [sys.executable, "-c", target_code], start_new_session=True
            )
            sidecar = subprocess.Popen(
                [
                    sys.executable,
                    og.__file__,
                    "watch",
                    "--pid",
                    str(target.pid),
                    "--limit-mb",
                    "10000",
                    "--ready-file",
                    str(ready),
                    "--label",
                    "sidecar-signal-test",
                ],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
                text=True,
            )
            try:
                deadline = time.monotonic() + 10
                while (not ready.exists() or not descendant_pid.exists()) and \
                        time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertTrue(ready.exists(), "watch sidecar never armed")
                self.assertTrue(descendant_pid.exists(), "target descendant never started")
                sidecar.send_signal(signal.SIGTERM)
                sidecar.wait(timeout=10)
                target.wait(timeout=10)
                deadline = time.monotonic() + 5
                while og._process_group_exists(target.pid) and \
                        time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertFalse(
                    og._process_group_exists(target.pid),
                    "abnormal sidecar exit left target descendants alive",
                )
            finally:
                try:
                    os.killpg(target.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                if target.poll() is None:
                    target.wait(timeout=5)
                if sidecar.poll() is None:
                    sidecar.kill()
                    sidecar.wait(timeout=5)
                if sidecar.stderr is not None:
                    sidecar.stderr.close()
                if sidecar.poll() is None:
                    sidecar.kill()
                    sidecar.wait(timeout=5)

    def test_terminating_campaign_watch_server_kills_all_target_descendants(self):
        with tempfile.TemporaryDirectory() as td:
            descendant_pid = Path(td, "server-descendant.pid")
            target_code = (
                "import pathlib,subprocess,sys,time; "
                "child=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)']); "
                f"pathlib.Path({str(descendant_pid)!r}).write_text(str(child.pid)); "
                "time.sleep(60)"
            )
            target = subprocess.Popen(
                [sys.executable, "-c", target_code], start_new_session=True
            )
            server = subprocess.Popen(
                [sys.executable, og.__file__, "watch-server"],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            try:
                self.assertEqual(server.stdout.readline(), og.WATCH_SERVER_READY)
                server.stdin.write(
                    f"WATCH 1 {target.pid} 10000 7365727665722d74657374\n".encode()
                )
                server.stdin.flush()
                while True:
                    response = server.stdout.readline()
                    if response.startswith(b"HEARTBEAT "):
                        continue
                    self.assertEqual(response, b"READY 1\n")
                    break
                deadline = time.monotonic() + 10
                while not descendant_pid.exists() and time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertTrue(descendant_pid.exists(), "target descendant never started")
                server.send_signal(signal.SIGTERM)
                server.wait(timeout=10)
                target.wait(timeout=10)
                deadline = time.monotonic() + 5
                while og._process_group_exists(target.pid) and time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertFalse(
                    og._process_group_exists(target.pid),
                    "campaign server exit left target descendants alive",
                )
            finally:
                try:
                    os.killpg(target.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                if target.poll() is None:
                    target.wait(timeout=5)
                if server.poll() is None:
                    server.kill()
                    server.wait(timeout=5)
                for stream in (server.stdin, server.stdout, server.stderr):
                    if stream is not None:
                        stream.close()

    def test_watch_cli_has_distinct_memout_exit(self):
        with mock.patch.object(
            og, "watch_existing_process", return_value=(True, 123)
        ):
            rc = og._cli(["watch", "--pid", "123", "--limit-mb", "456"])
        self.assertEqual(rc, og.WATCHDOG_BREACH_EXIT)

    def test_run_guarded_timeout_has_distinct_exit(self):
        rc = og.run_guarded(
            [sys.executable, "-c", "import time; time.sleep(60)"],
            10000,
            timeout_s=0.1,
            label="run-timeout-test",
        )
        self.assertEqual(rc, og.WATCHDOG_TIMEOUT_EXIT)

    def test_guarded_popen_refuses_noop_watchdog_and_reaps_child(self):
        spawned = []
        real_popen = og.subprocess.Popen

        def capture_spawn(*args, **kwargs):
            proc = real_popen(*args, **kwargs)
            spawned.append(proc)
            return proc

        with mock.patch.object(og.subprocess, "Popen", side_effect=capture_spawn), \
             mock.patch.object(og, "rss_watchdog", return_value=og._NoopWatchdog()):
            with self.assertRaisesRegex(RuntimeError, "did not arm"):
                og.guarded_popen(
                    [sys.executable, "-c", "import time; time.sleep(60)"],
                    10000,
                    label="noop-arm-test",
                )
        self.assertEqual(len(spawned), 1)
        self.assertIsNotNone(spawned[0].returncode)

    def test_guarded_popen_resume_failure_reaps_child_and_stops_guard(self):
        spawned = []
        real_popen = og.subprocess.Popen
        real_killpg = og.os.killpg

        def capture_spawn(*args, **kwargs):
            proc = real_popen(*args, **kwargs)
            spawned.append(proc)
            return proc

        def fail_resume(pgid, signum):
            if signum == signal.SIGCONT:
                raise OSError("simulated resume failure")
            return real_killpg(pgid, signum)

        with mock.patch.object(og.subprocess, "Popen", side_effect=capture_spawn), \
             mock.patch.object(og.os, "killpg", side_effect=fail_resume):
            with self.assertRaisesRegex(OSError, "simulated resume failure"):
                og.guarded_popen(
                    [sys.executable, "-c", "import time; time.sleep(60)"],
                    10000,
                    label="resume-failure-test",
                )
        self.assertEqual(len(spawned), 1)
        self.assertIsNotNone(spawned[0].returncode)

    def test_group_anchor_leases_pgid_after_leader_is_reaped(self):
        proc, guard = og.guarded_popen(
            [sys.executable, "-c", "pass"],
            10000,
            label="pgid-anchor-test",
        )
        pgid = os.getpgid(proc.pid)
        try:
            self.assertEqual(proc.wait(timeout=5), 0)
            # The leader is reaped, but the anchor keeps this exact group ID
            # live until cleanup; killpg cannot hit a newly recycled group.
            os.killpg(pgid, 0)
        finally:
            og._terminate_process_group(proc, pgid)
            guard.stop()

    def test_watchdog_tracks_descendant_after_group_leader_exits(self):
        descendant = (
            "import time; time.sleep(0.2); "
            "b=bytearray(96*1024*1024); time.sleep(60)"
        )
        leader = (
            "import subprocess,sys; "
            f"subprocess.Popen([sys.executable,'-c',{descendant!r}])"
        )
        proc, guard = og.guarded_popen(
            [sys.executable, "-c", leader],
            32,
            label="post-leader-descendant-test",
            poll_s=0.01,
        )
        pgid = os.getpgid(proc.pid)
        try:
            self.assertEqual(proc.wait(timeout=5), 0)
            deadline = time.monotonic() + 10
            while not guard.breached and time.monotonic() < deadline:
                time.sleep(0.01)
            self.assertTrue(
                guard.breached,
                "watchdog disarmed when the leader exited but a descendant remained",
            )
        finally:
            og._terminate_process_group(proc, pgid)
            guard.stop()

    def test_run_captured_returns_output_and_forwards_env_and_input(self):
        result = og.run_captured(
            [
                sys.executable,
                "-c",
                "import os,sys; print(os.environ['AY_CAPTURE_TEST']); "
                "print(sys.stdin.read(), end='')",
            ],
            10000,
            timeout_s=5,
            label="captured-success-test",
            env=dict(os.environ, AY_CAPTURE_TEST="envelope"),
            input_text="payload\n",
        )
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "envelope\npayload\n")
        self.assertFalse(result.timed_out)
        self.assertFalse(result.memout)
        self.assertFalse(result.output_truncated)
        self.assertGreaterEqual(result.wall_sec, 0)

    def test_run_captured_bounds_noisy_child_output(self):
        result = og.run_captured(
            [
                sys.executable,
                "-c",
                "import os; os.write(1, b'x' * (3 * 1024 * 1024)); "
                "os.write(2, b'y' * (3 * 1024 * 1024))",
            ],
            10000,
            timeout_s=10,
            label="captured-output-cap-test",
        )
        self.assertEqual(result.returncode, 0)
        self.assertTrue(result.stdout_truncated)
        self.assertTrue(result.stderr_truncated)
        self.assertTrue(result.output_truncated)
        self.assertLessEqual(len(result.stdout.encode()), og.CAPTURE_LIMIT_BYTES)
        self.assertLessEqual(len(result.stderr.encode()), og.CAPTURE_LIMIT_BYTES)

    def test_run_captured_timeout_kills_the_process_group(self):
        result = og.run_captured(
            [sys.executable, "-c", "import time; time.sleep(60)"],
            10000,
            timeout_s=0.1,
            label="captured-timeout-test",
        )
        self.assertTrue(result.timed_out)
        self.assertFalse(result.memout)
        self.assertNotEqual(result.returncode, 0)

    def test_run_captured_rejects_unbounded_runs(self):
        with self.assertRaises(ValueError):
            og.run_captured(["solver"], 0, timeout_s=1)
        with self.assertRaises(ValueError):
            og.run_captured(["solver"], 100, timeout_s=None)

    def test_run_cli_forwards_command_after_separator(self):
        with mock.patch.object(og, "run_guarded", return_value=17) as run:
            rc = og._cli([
                "run", "--limit-mb", "123", "--timeout-s", "4", "--",
                "solver", "input.smt2",
            ])
        self.assertEqual(rc, 17)
        run.assert_called_once_with(
            ["solver", "input.smt2"], 123, timeout_s=4.0,
            label="shell-harness",
        )

    def test_watch_and_run_cli_reject_zero_limits(self):
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit):
                og._cli(["watch", "--pid", "123", "--limit-mb", "0"])
            with self.assertRaises(SystemExit):
                og._cli(["run", "--limit-mb", "0", "--", "solver"])

    def test_cli_rejects_invalid_timing_and_planner_values(self):
        invalid_commands = [
            ["watch", "--pid", "123", "--limit-mb", "1", "--poll-s", "nan"],
            ["run", "--limit-mb", "1", "--timeout-s", "0", "--", "true"],
            ["plan", "--jobs", "1", "--headroom-mb", "-1"],
            ["plan", "--jobs", "1", "--mem-floor-mb", "0"],
        ]
        for command in invalid_commands:
            with self.subTest(command=command), \
                    contextlib.redirect_stderr(io.StringIO()), \
                self.assertRaises(SystemExit):
                og._cli(command)

    def test_run_guarded_kills_descendants_after_clean_wrapper_exit(self):
        with tempfile.TemporaryDirectory() as td:
            pid_file = Path(td, "pid")
            code = (
                "import subprocess\n"
                "p=subprocess.Popen(['sleep','60'])\n"
                f"open({str(pid_file)!r},'w').write(str(p.pid))\n"
            )
            rc = og.run_guarded(
                [sys.executable, "-c", code], 10000, timeout_s=5,
                label="descendant-cleanup-test",
            )
            self.assertEqual(rc, 0)
            pid = int(pid_file.read_text())
            for _ in range(100):
                if not Path(f"/proc/{pid}").exists():
                    break
                time.sleep(0.01)
            self.assertFalse(Path(f"/proc/{pid}").exists())

    def test_zero_limit_is_noop(self):
        proc = self._spawn("import time; time.sleep(0.2)")
        guard = og.rss_watchdog(proc, 0, label="test")
        rc = proc.wait(timeout=30)
        guard.stop()
        self.assertFalse(guard.breached)
        self.assertEqual(rc, 0)

    def test_process_group_rss_nonnegative(self):
        self.assertGreaterEqual(og.process_group_rss_mb(os.getpgid(0)), 0)

    def test_concurrent_watchdogs_share_one_bounded_proc_scan(self):
        workers = 16
        barrier = threading.Barrier(workers)
        results = []
        errors = []
        with og._RSS_SNAPSHOT_LOCK:
            og._RSS_SNAPSHOT_AT = 0.0
            og._RSS_SNAPSHOT = None
            og._RSS_SNAPSHOT_READY = False
            before = og._RSS_SNAPSHOT_SCAN_COUNT

        def inspect():
            try:
                barrier.wait(timeout=5)
                results.append(og.process_group_rss_mb(os.getpgid(0)))
            except Exception as error:
                errors.append(error)

        with mock.patch.object(og, "_RSS_SNAPSHOT_TTL_S", 60.0):
            threads = [threading.Thread(target=inspect) for _ in range(workers)]
            for thread in threads:
                thread.start()
            for thread in threads:
                thread.join(timeout=10)
        self.assertFalse(any(thread.is_alive() for thread in threads))
        self.assertEqual(errors, [])
        self.assertEqual(len(results), workers)
        self.assertTrue(all(result is not None for result in results))
        self.assertEqual(
            og._RSS_SNAPSHOT_SCAN_COUNT - before,
            1,
            "all watchdog threads in one campaign server must share one /proc scan",
        )

    def test_slow_proc_scan_does_not_trigger_one_rescan_per_waiter(self):
        workers = 16
        barrier = threading.Barrier(workers)
        results = []
        errors = []
        with og._RSS_SNAPSHOT_LOCK:
            og._RSS_SNAPSHOT_AT = 0.0
            og._RSS_SNAPSHOT = None
            og._RSS_SNAPSHOT_READY = False
            before = og._RSS_SNAPSHOT_SCAN_COUNT

        def slow_empty_proc(_path):
            time.sleep(0.1)
            return ["not-a-pid"]

        def inspect(index):
            try:
                barrier.wait(timeout=5)
                # Stagger arrivals across several TTLs while the first thread
                # holds the scan lock. Freshness must be measured after that
                # wait, not from each thread's stale pre-lock timestamp.
                time.sleep(index * 0.004)
                results.append(og.process_group_rss_mb(os.getpgid(0)))
            except Exception as error:
                errors.append(error)

        with mock.patch.object(og.os, "listdir", side_effect=slow_empty_proc):
            threads = [
                threading.Thread(target=inspect, args=(index,))
                for index in range(workers)
            ]
            for thread in threads:
                thread.start()
            for thread in threads:
                thread.join(timeout=10)
        self.assertFalse(any(thread.is_alive() for thread in threads))
        self.assertEqual(errors, [])
        self.assertEqual(results, [None] * workers)
        self.assertEqual(og._RSS_SNAPSHOT_SCAN_COUNT - before, 1)

    def test_measurement_failure_is_none_not_zero(self):
        """A failed measurement must be UNKNOWN, never 0.

        Regression: this returned 0 on every exception path (including the
        `ps` call's timeout=10), so the watchdog's `rss > kill_mb` silently
        never fired. Under a swap storm a full `ps -ax` walk is exactly what
        blocks — so the guard disarmed itself in the one regime it exists for.
        """
        with mock.patch.object(
                og.os.path, "exists", return_value=False), \
             mock.patch.object(
                og.subprocess, "run", side_effect=OSError("simulated ps hang")):
            self.assertIsNone(og.process_group_rss_mb(os.getpgid(0)))

    def test_nonzero_or_empty_ps_is_measurement_failure(self):
        failed = types.SimpleNamespace(returncode=1, stdout="", stderr="boom")
        empty = types.SimpleNamespace(returncode=0, stdout="", stderr="")
        with mock.patch.object(og.os.path, "exists", return_value=False), \
             mock.patch.object(og.subprocess, "run", return_value=failed):
            self.assertIsNone(og.process_group_rss_mb(123))
        with mock.patch.object(og.os.path, "exists", return_value=False), \
             mock.patch.object(og.subprocess, "run", return_value=empty):
            self.assertIsNone(og.process_group_rss_mb(123))

    def test_fails_closed_when_measurement_fails(self):
        """Unmeasurable child => SIGKILL, not an unbounded run."""
        proc = self._spawn(self.HOG)
        stderr = io.StringIO()
        with mock.patch.object(og, "process_group_rss_mb",
                                        return_value=None):
            with contextlib.redirect_stderr(stderr):
                guard = og.rss_watchdog(proc, 32, label="test", poll_s=0.01)
                try:
                    rc = proc.wait(timeout=30)
                finally:
                    guard.stop()
        self.assertTrue(guard.breached)
        self.assertEqual(rc, -signal.SIGKILL)
        self.assertIn("fail-closed", stderr.getvalue())

    def test_default_poll_interval_bounds_gb_scale_growth(self):
        """z3 peaks at 20.2 GiB/s (measured 2026-07-15), so the old 1.0s
        default could miss 20 GiB between samples. Anything at or below 20ms
        keeps the miss under ~500 MB."""
        self.assertLessEqual(og.POLL_DEFAULT, 0.02)
        missed_mb = og.POLL_DEFAULT * 20.2 * 1024
        self.assertLess(missed_mb, 500)

    def test_failed_spawn_cleanup_kills_group_after_leader_was_reaped(self):
        proc = mock.Mock(pid=4242, returncode=1)
        with mock.patch.object(og, "_kill_and_reap_group") as cleanup:
            og._kill_reap_failed_spawn(proc, 4242)
        cleanup.assert_called_once_with(proc, 4242, "failed guarded spawn")

    def test_run_guarded_preserves_wait_error_after_cleanup(self):
        proc = mock.Mock(pid=4242, returncode=None)
        proc.wait.side_effect = OSError("simulated wait failure")
        guard = mock.Mock(breach_time_ns=None)
        with mock.patch.object(og, "guarded_popen", return_value=(proc, guard)), \
             mock.patch.object(og, "_kill_and_reap_group"):
            with self.assertRaisesRegex(OSError, "simulated wait failure"):
                og.run_guarded(["solver"], 128, timeout_s=1)
        guard.stop.assert_called_once_with()

    def test_first_terminal_cause_uses_monotonic_trigger_order(self):
        self.assertEqual(
            og._first_termination_cause(
                breach_time_ns=100, timeout_time_ns=101, cancel_time_ns=None
            ),
            "memout",
        )
        self.assertEqual(
            og._first_termination_cause(
                breach_time_ns=101, timeout_time_ns=100, cancel_time_ns=None
            ),
            "timeout",
        )
        self.assertEqual(
            og._first_termination_cause(
                breach_time_ns=102, timeout_time_ns=None, cancel_time_ns=100
            ),
            "cancel",
        )

    def test_watchdog_stop_fails_if_thread_does_not_terminate(self):
        guard = object.__new__(og._RssWatchdog)
        guard._stop_evt = mock.Mock()
        guard._thread = mock.Mock()
        guard._thread.is_alive.return_value = True
        guard._label = "stuck-watchdog-test"
        with self.assertRaisesRegex(RuntimeError, "did not stop"):
            guard.stop()
        guard._stop_evt.set.assert_called_once_with()
        guard._thread.join.assert_called_once_with(timeout=10)


class SmtcompEnvelopeTest(unittest.TestCase):
    """smtcomp_harness governed TIME and nothing else until 2026-07-15: --jobs N
    puts N concurrent children in flight for the full --timeout with no memory
    bound. Six unbounded z3 is the shape that panicked this machine on 07-14."""

    HOG = ("import time\n"
           "b = bytearray(400 * 1024 * 1024)\n"
           "time.sleep(60)\n")

    def test_run_process_memout_is_not_timeout(self):
        """A memout kill must not be recorded as a timeout. Both SIGKILL the
        group; only one means 'needed more RAM than the envelope'."""
        inv = smtcomp_harness.Invocation([sys.executable, "-c", self.HOG])
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr):
            res = smtcomp_harness.run_process(inv, timeout_s=60, memlimit_mb=32)
        self.assertTrue(res.memout)
        self.assertFalse(res.timed_out)      # 60s budget was nowhere near spent
        self.assertLess(res.wall_sec, 30)

    def test_run_process_without_envelope_fails_closed(self):
        """A caller that forgets the envelope cannot launch an unbounded child."""
        inv = smtcomp_harness.Invocation([sys.executable, "-c",
                                          "import time; time.sleep(0.2)"])
        with self.assertRaises(ValueError):
            smtcomp_harness.run_process(inv, timeout_s=30, memlimit_mb=0)

    def test_record_carries_envelope(self):
        """Results taken under different envelopes are not comparable, so the
        complete canonical envelope travels with the record."""
        self.assertIn("resource_envelope",
                      smtcomp_harness.run_one.__code__.co_varnames)


class PbSweepMemoutTest(unittest.TestCase):
    """pb_sweep.run_one labels a watchdog kill as 'memout' — the envelope is
    enforced externally because the default ./target/release/ay `pb`
    subcommand ignores the exported MEMLIMIT env."""

    def test_hog_child_reported_as_memout(self):
        with tempfile.NamedTemporaryFile("w", suffix=".py", delete=False) as fh:
            fh.write(RssWatchdogTest.HOG)
            hog = fh.name
        try:
            # Non-"ay" solver name => cmd is [cmd_tmpl, f]; use the python
            # interpreter as the "solver" and the hog script as the instance.
            rec = pb_sweep.run_one("hog", sys.executable, hog, 30.0,
                                   env=None, memlimit_mb=32)
        finally:
            os.unlink(hog)
        self.assertEqual(rec["status"], "memout")


class PbBenchEnvelopeTest(unittest.TestCase):
    """The shell PB harness must use the shared watchdog even at jobs=1 and
    persist the actual envelope in its CSV."""

    def test_shell_harness_records_guarded_envelope(self):
        with tempfile.TemporaryDirectory() as td:
            script = os.path.join(td, "pb_bench.sh")
            shutil.copyfile(os.path.join(SCRIPTS_DIR, "pb_bench.sh"), script)
            os.chmod(script, 0o755)
            guard_log = os.path.join(td, "guard.log")
            guard = os.path.join(td, "_oom_guard.py")
            Path(guard).write_text(
                """\
import os
import subprocess
import sys

with open(os.environ["AY_TEST_GUARD_LOG"], "a", encoding="utf-8") as log:
    log.write(" ".join(sys.argv[1:]) + "\\n")
if sys.argv[1] == "plan":
    print("PLAN_JOBS=1")
    print("PLAN_MEMLIMIT_MB=64")
    print("PLAN_NBCORE=1")
    print("PLAN_HEADROOM_MB=128")
elif sys.argv[1] == "run":
    command = sys.argv[sys.argv.index("--") + 1:]
    raise SystemExit(subprocess.run(command, check=False).returncode)
else:
    raise SystemExit(f"unexpected guard command: {sys.argv[1]}")
"""
            )
            solver = os.path.join(td, "solver")
            with open(solver, "w") as fh:
                fh.write("#!/bin/sh\nprintf 's SATISFIABLE\\n'\n")
            os.chmod(solver, 0o755)
            corpus = os.path.join(td, "DEC-LIN")
            os.makedirs(corpus)
            Path(corpus, "tiny.opb").write_text("* #variable= 0 #constraint= 0\n")
            output = os.path.join(td, "results.csv")
            environment = os.environ.copy()
            environment["AY_TEST_GUARD_LOG"] = guard_log
            proc = subprocess.run(
                [script, solver, "1", corpus, output, "1"],
                capture_output=True,
                text=True,
                timeout=30,
                env=environment,
            )
            self.assertEqual(proc.returncode, 0, proc.stderr)
            rows = Path(output).read_text().splitlines()
            self.assertIn("resource_memlimit_mb", rows[0])
            self.assertIn("resource_enforcement", rows[0])
            self.assertTrue(rows[1].endswith("|rss_watchdog"), rows[1])
            guard_calls = Path(guard_log).read_text().splitlines()
            self.assertIn("--warn-concurrent-build", guard_calls[0])
            self.assertIn("run --limit-mb 64", guard_calls[1])


class WindTunnelMemoutTest(unittest.TestCase):
    """wind_tunnel.run_instance enforces the MEMLIMIT envelope externally:
    a --bin that ignores MEMLIMIT (e.g. the main ay binary's `pb` subcommand,
    which sets no memory limit at all) is killed at the backstop and the row
    is recorded as MEMOUT rather than silently running unbounded."""

    def test_run_instance_memout_backstop(self):
        with tempfile.TemporaryDirectory() as td:
            inst = os.path.join(td, "t.opb.xz")
            with lzma.open(inst, "wt") as fh:
                fh.write("* #variable= 1 #constraint= 1\n+1 x1 >= 1;\n")
            hog = os.path.join(td, "hogbin")  # ignores MEMLIMIT, hogs RAM
            with open(hog, "w") as fh:
                fh.write("#!/bin/sh\nexec %s -c 'import time; "
                         "b = bytearray(400*1024*1024); time.sleep(60)'\n"
                         % sys.executable)
            os.chmod(hog, 0o755)
            workdir = os.path.join(td, "work")
            os.makedirs(workdir)
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                row = wind_tunnel.run_instance(hog, Path(inst), 60000, 45.0,
                                               {"MEMLIMIT": "32", "NBCORE": "1"},
                                               Path(workdir))
            self.assertEqual(row["status"], "MEMOUT")
            self.assertIn("memout", stderr.getvalue())


class PbcompChildEnvTest(unittest.TestCase):
    """child_solver_env applies authoritative budgets at jobs == 1 too."""

    def test_jobs1_injects_memlimit_and_nbcore(self):
        with mock.patch.dict(os.environ, {}, clear=False):
            os.environ.pop("MEMLIMIT", None)
            with mock.patch.object(pbcomp_harness, "physical_core_count",
                                   return_value=8):
                env = pbcomp_harness.child_solver_env(
                    1, None, memlimit_mb=8576
                )
        self.assertIsNotNone(env)
        self.assertEqual(env["MEMLIMIT"], "8576")
        self.assertEqual(env["NBCORE"], "8")

    def test_jobs1_without_memory_still_has_core_budget(self):
        with mock.patch.object(pbcomp_harness, "physical_core_count",
                               return_value=8):
            env = pbcomp_harness.child_solver_env(1, None, 0)
        self.assertEqual(env["NBCORE"], "8")
        self.assertNotIn("MEMLIMIT", env)

    def test_plan_memlimit_wins_over_inherited_value(self):
        with mock.patch.dict(os.environ, {"MEMLIMIT": "123"}):
            env = pbcomp_harness.child_solver_env(1, None, memlimit_mb=500)
        self.assertEqual(env["MEMLIMIT"], "500")

    def test_jobs_gt1_sets_both(self):
        with mock.patch.dict(os.environ, {}, clear=False):
            os.environ.pop("MEMLIMIT", None)
            env = pbcomp_harness.child_solver_env(4, None, memlimit_mb=2000)
        self.assertEqual(env["MEMLIMIT"], "2000")
        self.assertIn("NBCORE", env)

    def test_result_envelope_field_roundtrip(self):
        # Old JSONL records (pre-envelope) must load with memlimit_mb == 0 so
        # cmd_score can flag cross-envelope comparisons instead of crashing.
        old = {"instance": "a.opb", "category": "OPT-LIN", "status": "TIMEOUT",
               "objective": None, "wall_s": 1.0, "exit_code": 0,
               "verified": None, "wrong_answer": False}
        r = pbcomp_harness.Result(**old)
        self.assertEqual(r.memlimit_mb, 0)
        r2 = pbcomp_harness.Result(**dict(old, memlimit_mb=1072))
        self.assertEqual(r2.memlimit_mb, 1072)


class ChccompHarnessEnvelopeTest(unittest.TestCase):
    """chccomp_harness cmd_run wiring: ay children get --memory and every
    record carries the enforced envelope (resumable JSONL files can span
    runs, so the envelope must live per record)."""

    def test_ay_argv_carries_memory_flag(self):
        old = chccomp_harness._AY_MEMLIMIT_MB
        try:
            chccomp_harness._AY_MEMLIMIT_MB = 512
            argv = chccomp_harness._ay_argv("x.smt2", 10)
            self.assertIn("--memory", argv)
            self.assertEqual(argv[argv.index("--memory") + 1], "512")
            chccomp_harness._AY_MEMLIMIT_MB = 0
            self.assertNotIn("--memory", chccomp_harness._ay_argv("x.smt2", 10))
        finally:
            chccomp_harness._AY_MEMLIMIT_MB = old

    def test_run_one_record_carries_memlimit(self):
        chccomp_harness.SOLVERS["truebin"] = lambda f, t: [str(TRUE_BIN)]
        try:
            task = chccomp_harness.Task(rel_id="fam/x.yml", smt2=os.devnull,
                                        verdict=None, placeholder=False)
            rec = chccomp_harness.run_one("truebin", task, 5, memlimit_mb=777)
        finally:
            del chccomp_harness.SOLVERS["truebin"]
        self.assertEqual(rec["memlimit_mb"], 777)


class WindTunnelBuildGuardTest(unittest.TestCase):
    """wind_tunnel refuses to start while a cargo build is active."""

    def _run_main(self, build_active):
        old_guard, old_plan, old_argv = (
            wind_tunnel.warn_concurrent_build,
            wind_tunnel.plan_solver_resources,
            sys.argv,
        )
        try:
            def guard():
                if build_active:
                    message = ("[oom-guard] REFUSING: cargo/rustc active; "
                               "see scripts/_oom_guard.py and incidents "
                               "2026-06-19 / 2026-07-11")
                    print(message, file=sys.stderr)
                    raise RuntimeError(message)

            wind_tunnel.warn_concurrent_build = guard
            wind_tunnel.plan_solver_resources = lambda *args, **kwargs: (
                og.ResourcePlan(1, 1024, 1, 16000)
            )
            with tempfile.TemporaryDirectory() as td:
                sys.argv = ["wind_tunnel.py", "--corpus", td,
                            "--bin", "/usr/bin/false",
                            "--out", os.path.join(td, "out")]
                stderr = io.StringIO()
                with contextlib.redirect_stderr(stderr):
                    rc = wind_tunnel.main()
            return rc, stderr.getvalue()
        finally:
            wind_tunnel.warn_concurrent_build = old_guard
            wind_tunnel.plan_solver_resources = old_plan
            sys.argv = old_argv

    def test_refuses_when_build_active(self):
        rc, err = self._run_main(build_active=True)
        self.assertEqual(rc, 2)
        self.assertIn("REFUSING", err)
        # The error must reference both watchdog panics and the guard module.
        self.assertIn("2026-06-19", err)
        self.assertIn("2026-07-11", err)
        self.assertIn("scripts/_oom_guard.py", err)

    def test_no_build_no_refusal(self):
        rc, err = self._run_main(build_active=False)
        self.assertNotIn("REFUSING", err)
        self.assertIn("no instances found", err)


if __name__ == "__main__":
    unittest.main()
