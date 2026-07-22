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
import signal
import subprocess
import sys
import tempfile
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

    def test_unknown_ram_is_safe_noop(self):
        # RAM undetectable: don't second-guess the caller; memlimit 0 means
        # "don't set" (module's safe-no-op philosophy).
        plan = og.plan_solver_resources(6, ram_mb=0, cores=14)
        self.assertEqual(plan.jobs, 6)
        self.assertEqual(plan.memlimit_mb, 0)
        self.assertEqual(plan.nbcore, 2)

    def test_automatic_unknown_ram_fails_closed(self):
        with mock.patch.object(og, "physical_ram_mb", return_value=0), \
             mock.patch.object(og, "cgroup_memory_mb", return_value=None):
            with self.assertRaisesRegex(RuntimeError, "effective RAM ceiling"):
                og.plan_solver_resources(2)

    def test_cgroup_limit_and_current_usage_bound_automatic_plan(self):
        cgroup = og.CgroupMemory(limit_mb=8192, current_mb=2048)
        with mock.patch.object(og, "physical_ram_mb", return_value=8192), \
             mock.patch.object(og, "cgroup_memory_mb", return_value=cgroup):
            plan = og.plan_solver_resources(2, cores=4)
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

    def test_count_active_rustc_returns_count(self):
        self.assertIsInstance(og.count_active_rustc(), int)
        self.assertGreaterEqual(og.count_active_rustc(), 0)


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


@unittest.skipUnless(os.path.exists("/usr/bin/true"), "needs /usr/bin/true")
class ChcEnvelopeRecordingTest(unittest.TestCase):
    """The CHC harnesses must record the enforced per-child --memory envelope:
    baselines/sweeps were measured under ay's 85%-of-RAM default, so results
    taken under different envelopes are not comparable and a solved->unknown
    flip under a tight cap must be attributable to the cap."""

    def test_track_sweep_record_carries_memlimit(self):
        task = types.SimpleNamespace(smt2=os.devnull, verdict=None,
                                     rel_id="fam/x.smt2")
        rec = chccomp_track_sweep.run_one(task, 5, "/usr/bin/true",
                                          memlimit_mb=777)
        self.assertEqual(rec["memlimit_mb"], 777)
        self.assertEqual(rec["status"], "unknown")

    def test_track_sweep_record_zero_means_solver_default(self):
        # RAM undetectable => plan memlimit 0 => no --memory flag; the record
        # still says so explicitly (0 = solver default envelope).
        task = types.SimpleNamespace(smt2=os.devnull, verdict=None,
                                     rel_id="fam/x.smt2")
        rec = chccomp_track_sweep.run_one(task, 5, "/usr/bin/true")
        self.assertEqual(rec["memlimit_mb"], 0)

    def test_regression_record_carries_memlimit(self):
        entry = {"year": "2025", "track": "LIA-Lin", "instance": "i.yml",
                 "verdict": "sat", "wall": 1.0}
        with mock.patch.object(chccomp_regression, "resolve_smt2",
                               return_value=os.devnull):
            rec = chccomp_regression.run(entry, 1, "/usr/bin/true",
                                         memlimit_mb=777)
        self.assertEqual(rec["memlimit_mb"], 777)
        self.assertEqual(rec["status"], "unknown")


@unittest.skipUnless(hasattr(os, "getpgid"), "needs POSIX process groups")
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

    def test_watch_cli_has_distinct_memout_exit(self):
        with mock.patch.object(og, "watch_existing_process", return_value=True):
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


@unittest.skipUnless(hasattr(os, "getpgid"), "needs POSIX process groups")
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

    def test_run_process_without_envelope_is_unbounded(self):
        """memlimit_mb=0 keeps the pre-2026-07-15 behaviour (no backstop), so a
        caller that forgets the envelope gets no memout — which is exactly why
        cmd_run computes it from plan_solver_resources rather than the CLI."""
        inv = smtcomp_harness.Invocation([sys.executable, "-c",
                                          "import time; time.sleep(0.2)"])
        res = smtcomp_harness.run_process(inv, timeout_s=30, memlimit_mb=0)
        self.assertFalse(res.memout)
        self.assertEqual(res.exit_code, 0)

    def test_record_carries_envelope(self):
        """Results taken under different envelopes are not comparable, so the
        complete canonical envelope travels with the record."""
        self.assertIn("resource_envelope",
                      smtcomp_harness.run_one.__code__.co_varnames)


@unittest.skipUnless(hasattr(os, "getpgid"), "needs POSIX process groups")
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


@unittest.skipUnless(hasattr(os, "getpgid"), "needs POSIX process groups")
class PbBenchEnvelopeTest(unittest.TestCase):
    """The shell PB harness must use the shared watchdog even at jobs=1 and
    persist the actual envelope in its CSV."""

    def test_shell_harness_records_guarded_envelope(self):
        script = os.path.join(SCRIPTS_DIR, "pb_bench.sh")
        with tempfile.TemporaryDirectory() as td:
            solver = os.path.join(td, "solver")
            with open(solver, "w") as fh:
                fh.write("#!/bin/sh\nprintf 's SATISFIABLE\\n'\n")
            os.chmod(solver, 0o755)
            corpus = os.path.join(td, "DEC-LIN")
            os.makedirs(corpus)
            Path(corpus, "tiny.opb").write_text("* #variable= 0 #constraint= 0\n")
            output = os.path.join(td, "results.csv")
            proc = subprocess.run(
                [script, solver, "1", corpus, output, "1"],
                capture_output=True,
                text=True,
                timeout=30,
            )
            self.assertEqual(proc.returncode, 0, proc.stderr)
            rows = Path(output).read_text().splitlines()
            self.assertIn("resource_memlimit_mb", rows[0])
            self.assertIn("resource_enforcement", rows[0])
            self.assertTrue(rows[1].endswith("|rss_watchdog"), rows[1])


@unittest.skipUnless(hasattr(os, "getpgid"), "needs POSIX process groups")
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


@unittest.skipUnless(os.path.exists("/usr/bin/true"), "needs /usr/bin/true")
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
        chccomp_harness.SOLVERS["truebin"] = lambda f, t: ["/usr/bin/true"]
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
