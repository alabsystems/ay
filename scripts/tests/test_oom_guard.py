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
import ctypes
import ctypes.util
import errno
import io
import json
import lzma
import os
import queue
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
import smtcomp_harness  # noqa: E402
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


def plan_detected_host_with_scratch_lease(test, label):
    """One 256 MiB-floor plan from the REAL planner on detected RAM, holding a
    scratch lease instead of the host's.

    The host lease belongs to real campaigns: a differential gate admitted on
    this machine holds it for its whole run, and must neither turn the suite red
    nor be refused because the suite took it.
    """
    plan = og.plan_solver_resources(1, mem_floor_mb=256, label=label, acquire_lease=False)
    lease_dir = tempfile.TemporaryDirectory()
    test.addCleanup(lease_dir.cleanup)
    og.acquire_harness_lease(label, _lock_path=os.path.join(lease_dir.name, "host.lock"))
    test.addCleanup(og._release_harness_lease)
    return plan


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

    def test_live_free_memory_trims_a_plan_sized_for_an_idle_host(self):
        # The 2026-07-30 panic shape: a second campaign is already resident, so
        # `RAM - headroom` describes a machine that no longer exists. The plan
        # must size against what is free NOW, keeping one child's worth spare.
        idle = og.plan_solver_resources(4, ram_mb=24576, cores=14)
        busy = og.plan_solver_resources(4, ram_mb=24576, cores=14,
                                        available_mb=6000)
        self.assertLess(busy.memlimit_mb, idle.memlimit_mb)
        self.assertLessEqual(busy.jobs * busy.memlimit_mb, 6000 - 1024)

    def test_live_free_memory_can_only_shrink_a_plan(self):
        # A host reporting more free memory than the static policy allows must
        # NOT widen the envelope — headroom still binds.
        idle = og.plan_solver_resources(4, ram_mb=24576, cores=14)
        roomy = og.plan_solver_resources(4, ram_mb=24576, cores=14,
                                         available_mb=24576)
        self.assertEqual(roomy.memlimit_mb, idle.memlimit_mb)
        self.assertEqual(roomy.jobs, idle.jobs)

    def test_no_free_memory_fails_closed(self):
        # A machine with nothing left must refuse to plan, not hand out a
        # budget it cannot back.
        with self.assertRaisesRegex(RuntimeError, "remains after effective"):
            og.plan_solver_resources(4, ram_mb=24576, cores=14,
                                     available_mb=512)

    def test_unknown_free_memory_leaves_the_static_plan_intact(self):
        # 0 means "could not read the counter". That must not refuse every run
        # on a platform whose counters we cannot parse.
        idle = og.plan_solver_resources(4, ram_mb=24576, cores=14)
        unknown = og.plan_solver_resources(4, ram_mb=24576, cores=14,
                                           available_mb=0)
        self.assertEqual(unknown.memlimit_mb, idle.memlimit_mb)

    def test_negative_available_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "available_mb must be"):
            og.plan_solver_resources(4, ram_mb=24576, cores=14,
                                     available_mb=-1)

    def test_host_available_ram_is_readable_and_bounded_by_physical(self):
        # Detection itself must never raise; on a supported host it returns a
        # positive figure that cannot exceed physical RAM.
        available = og.host_available_ram_mb()
        self.assertIsInstance(available, int)
        self.assertGreaterEqual(available, 0)
        if sys.platform in ("darwin", "linux"):
            self.assertGreater(available, 0)
            self.assertLessEqual(available, og._host_physical_ram_mb())

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
        # The automatic plan also reads the host's live free memory. Pin it to
        # 0, the reading's "unknown", so that only the cgroup bounds this plan:
        # the live trim has its own tests above, and left unpinned this one
        # failed whenever the host running the suite was short of memory
        # ("only 0MiB remains", measured 2026-10-08 under a parallel build).
        with mock.patch.object(og, "physical_ram_mb", return_value=8192), \
             mock.patch.object(og, "cgroup_memory_mb", return_value=cgroup), \
             mock.patch.object(og, "host_available_ram_mb", return_value=0):
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
        # `create=True`: macOS's os module has no sched_getaffinity at all.
        # physical_core_count() guards its call with (AttributeError, OSError),
        # so injecting the attribute here exercises the affinity-honoring
        # branch on every platform.
        with mock.patch.object(og, "_host_physical_core_count", return_value=16), \
             mock.patch.object(og.os, "sched_getaffinity",
                               return_value=set(range(4)), create=True), \
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
        # Hang detectors: a sidecar's lease record, and its reading of the owner's, wait
        # up to _GROUP_SETTLE_S on `ps`.
        hang_s = 2 * og._GROUP_SETTLE_S
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
                reader.join(timeout=hang_s)
                self.assertFalse(reader.is_alive(), "first lease sidecar did not arm")
                self.assertEqual(ready, [b"AY_OOM_HARNESS_LEASE_READY_V1\n"])

                blocked = subprocess.run(
                    command,
                    input=b"",
                    capture_output=True,
                    timeout=hang_s,
                    env=second_env,
                    check=False,
                )
                self.assertNotEqual(blocked.returncode, 0)
                self.assertNotIn(
                    b"AY_OOM_HARNESS_LEASE_READY_V1", blocked.stdout
                )

                first.stdin.close()
                self.assertEqual(first.wait(timeout=hang_s), 0)
                replacement = subprocess.run(
                    command,
                    input=b"",
                    capture_output=True,
                    timeout=hang_s,
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

    # A helper that takes the flock on a lease path, writes an arbitrary owner
    # record into it, and then stays alive holding the descriptor. This is the
    # shape of the 2026-08-24 leak: the flock outlived the harness that planned
    # the campaign, so the recorded owner was dead while the lock was still held.
    _LEASE_HOLDER_SOURCE = (
        "import fcntl, os, sys\n"
        "path, record = sys.argv[1], sys.argv[2]\n"
        "fd = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)\n"
        "fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)\n"
        "os.ftruncate(fd, 0)\n"
        "os.write(fd, record.encode())\n"
        "sys.stdout.write('HELD\\n')\n"
        "sys.stdout.flush()\n"
        "sys.stdin.read()\n"
    )

    @contextlib.contextmanager
    def _leaked_lease(self, lock_path, record):
        holder = subprocess.Popen(
            [sys.executable, "-c", self._LEASE_HOLDER_SOURCE, str(lock_path), record],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        try:
            # Never read holder.stderr here: the holder stays alive for the
            # whole test, so reading its pipe to completion would deadlock.
            ready = holder.stdout.readline()
            self.assertEqual(ready, b"HELD\n", "lease holder did not take the flock")
            yield holder
        finally:
            if holder.poll() is None:
                holder.kill()
                holder.wait(timeout=10)
            for stream in (holder.stdin, holder.stdout, holder.stderr):
                if stream is not None:
                    stream.close()

    @staticmethod
    def _definitely_dead_pid():
        """A PID that has been observed to exit, i.e. `kill -0` must fail."""
        corpse = subprocess.Popen([sys.executable, "-c", "pass"])
        corpse.wait(timeout=30)
        return corpse.pid

    def test_lease_with_dead_recorded_owner_is_reclaimed_and_logged(self):
        # Regression (#32): a leaked /tmp/ay-oom-guard-<uid>.lock naming a DEAD
        # pid made every later chc_baseline_compare run refuse before writing
        # evidence, which read as a CHC regression rather than as a stuck lock.
        dead = self._definitely_dead_pid()
        with tempfile.TemporaryDirectory() as td:
            lock_path = Path(td) / "stale-owner-host-lease.lock"
            record = f"pid={dead} label=chc_baseline_compare.py\n"
            with self._leaked_lease(lock_path, record):
                self.assertTrue(lock_path.exists())
                stale_ino = lock_path.stat().st_ino
                stderr = io.StringIO()
                with contextlib.redirect_stderr(stderr):
                    lease = og.acquire_harness_lease(
                        "reclaim-test", _lock_path=str(lock_path)
                    )
                try:
                    logged = stderr.getvalue()
                    self.assertIn("reclaimed the host resource lease", logged)
                    self.assertIn(str(lock_path), logged)
                    self.assertIn(f"pid={dead}", logged)
                    self.assertIn("chc_baseline_compare.py", logged)
                    # A fresh inode, owned by this process, is what makes the
                    # next run's flock meaningful again.
                    self.assertNotEqual(lock_path.stat().st_ino, stale_ino)
                    self.assertIn(
                        f"pid={os.getpid()}", lock_path.read_text(encoding="utf-8")
                    )
                finally:
                    og._release_harness_lease()

    def test_lease_with_live_recorded_owner_is_still_refused(self):
        # The guard's purpose is refusing to run a heavy job beside another
        # campaign. Only stale-OWNER leases may be reclaimed, never a live one.
        with tempfile.TemporaryDirectory() as td:
            lock_path = Path(td) / "live-owner-host-lease.lock"
            record = f"pid={os.getpid()} label=live-campaign\n"
            with self._leaked_lease(lock_path, record):
                held_ino = lock_path.stat().st_ino
                stderr = io.StringIO()
                with contextlib.redirect_stderr(stderr):
                    with self.assertRaisesRegex(
                        RuntimeError, "already owns the host resource lease"
                    ):
                        og.acquire_harness_lease(
                            "refuse-test", _lock_path=str(lock_path)
                        )
                self.assertNotIn("reclaimed", stderr.getvalue())
                # Not unlinked, not rewritten: the live owner still owns it.
                self.assertEqual(lock_path.stat().st_ino, held_ino)
                self.assertIn(
                    f"pid={os.getpid()} label=live-campaign",
                    lock_path.read_text(encoding="utf-8"),
                )
        self.assertIsNone(og._ACTIVE_HARNESS_LEASE)

    def test_lease_refusal_names_the_owner_it_is_refusing_for(self):
        with tempfile.TemporaryDirectory() as td:
            lock_path = Path(td) / "named-owner-host-lease.lock"
            record = f"pid={os.getpid()} acquired=1 label=long-running-race\n"
            with self._leaked_lease(lock_path, record):
                with self.assertRaises(RuntimeError) as caught:
                    og.acquire_harness_lease("named-test", _lock_path=str(lock_path))
        message = str(caught.exception)
        self.assertIn(f"pid={os.getpid()}", message)
        self.assertIn("long-running-race", message)
        self.assertIn("held=", message)

    def test_unreadable_lease_record_is_never_reclaimed(self):
        # An owner that has taken the flock but not yet written its record is
        # alive. "Owner unknown" must fail closed, not reclaim.
        with tempfile.TemporaryDirectory() as td:
            lock_path = Path(td) / "empty-record-host-lease.lock"
            with self._leaked_lease(lock_path, ""):
                held_ino = lock_path.stat().st_ino
                with self.assertRaisesRegex(
                    RuntimeError, "already owns the host resource lease"
                ):
                    og.acquire_harness_lease("empty-test", _lock_path=str(lock_path))
                self.assertEqual(lock_path.stat().st_ino, held_ino)

    def test_lease_owner_liveness_rejects_a_recycled_pid(self):
        record = og._parse_harness_lease_record(
            f"pid={os.getpid()} acquired=1 start=Some_Other_Boot_Time label=old\n"
        )
        self.assertIsNotNone(record)
        self.assertEqual(record["pid"], os.getpid())
        # This PID is alive, but it is not the process that wrote the record.
        self.assertFalse(og._harness_lease_owner_is_alive(record))
        current = og._parse_harness_lease_record(
            og._harness_lease_record(os.getpid(), "self")
        )
        self.assertTrue(og._harness_lease_owner_is_alive(current))

    def test_unmeasurable_start_token_counts_the_owner_as_live(self):
        # `kill -0` already said the PID exists, so a failed start-time lookup
        # is a measurement failure, not evidence of death. Reclaiming a live
        # campaign's lease is the one outcome this guard must never produce.
        record = og._parse_harness_lease_record(
            f"pid={os.getpid()} acquired=1 start=Recorded_Boot_Time label=live\n"
        )
        with mock.patch.object(og, "_watch_process_identity", return_value=None):
            self.assertTrue(og._harness_lease_owner_is_alive(record))

    def test_count_active_rustc_returns_count(self):
        # Contract (count_active_rustc docstring): hosts without a procfs
        # (macOS) use an equivalent bounded `ps` scan so the concurrent-build
        # refusal keeps protecting sweeps on every supported platform instead
        # of crashing.
        count = og.count_active_rustc()
        self.assertIsInstance(count, int)
        self.assertGreaterEqual(count, 0)
        if not Path("/proc").is_dir():
            with mock.patch.object(
                og, "_count_active_rustc_ps", return_value=3
            ) as fallback:
                self.assertEqual(og.count_active_rustc(), 3)
            fallback.assert_called_once_with(None)

    def test_warn_concurrent_build_preserves_process_scan_failure(self):
        with mock.patch.object(
            og,
            "count_active_rustc",
            side_effect=RuntimeError("process scan unavailable"),
        ):
            with self.assertRaisesRegex(RuntimeError, "process scan unavailable"):
                og.warn_concurrent_build()

    def _count_builds_with_process_read_error(self, leaf, phase, number):
        # Inject the real open/read boundary, not the detector's result. The
        # second live driver must still be detected after the first disappears.
        root = "/mock-proc"
        entries = mock.MagicMock()
        entries.__iter__.return_value = iter([
            types.SimpleNamespace(name="1966920"),
            types.SimpleNamespace(name="100"),
        ])
        error = OSError(number, "injected per-process read failure")

        def open_proc(path, mode):
            self.assertEqual(mode, "rb")
            if path == f"{root}/1966920/{leaf}":
                if phase == "open":
                    raise error
                stream = mock.MagicMock()
                stream.__enter__.return_value.read.side_effect = error
                return stream
            if path.endswith("/comm"):
                return io.BytesIO(b"targo\n")
            self.assertTrue(path.endswith("/cmdline"))
            return io.BytesIO(b"targo\0--unverified\0build\0")

        with mock.patch.object(og.os.path, "isdir", return_value=True), \
                mock.patch.object(og.os, "scandir", return_value=entries), \
                mock.patch.object(og, "_process_state", return_value="S"), \
                mock.patch("builtins.open", side_effect=open_proc):
            return og.count_active_rustc(proc_root=root, ancestor_pids=set())

    def test_build_detection_ignores_only_vanished_process_reads(self):
        for leaf in ("comm", "cmdline"):
            for phase in ("open", "read"):
                for number in (errno.ENOENT, errno.ESRCH):
                    with self.subTest(leaf=leaf, phase=phase, errno=number):
                        self.assertEqual(
                            self._count_builds_with_process_read_error(
                                leaf, phase, number
                            ),
                            1,
                        )

    def test_build_detection_preserves_non_exit_process_read_errors(self):
        for leaf in ("comm", "cmdline"):
            for phase in ("open", "read"):
                for number in (errno.EACCES, errno.EPERM, errno.EIO, errno.EINVAL):
                    with self.subTest(leaf=leaf, phase=phase, errno=number):
                        with self.assertRaisesRegex(RuntimeError, "cannot inspect"):
                            self._count_builds_with_process_read_error(
                                leaf, phase, number
                            )

    def test_build_process_directory_errors_are_not_exit_races(self):
        for number in (errno.ENOENT, errno.ESRCH, errno.EACCES, errno.EIO):
            with self.subTest(errno=number), \
                    mock.patch.object(og.os.path, "isdir", return_value=True), \
                    mock.patch.object(
                        og.os, "scandir", side_effect=OSError(number, "scan failed")
                    ):
                with self.assertRaisesRegex(RuntimeError, "cannot inspect build processes"):
                    og._named_build_processes("/mock-proc")

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
            # `targo tippy` is the Trust lint lane (stock `cargo clippy`), and
            # `targo --unverified build` names its lane before the subcommand.
            process(107, "targo", ["targo", "tippy", "--workspace"])
            process(108, "targo", ["targo", "--unverified", "build"])

            self.assertEqual(
                og.count_active_rustc(proc_root=td, ancestor_pids={103}),
                4,
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


class RssWatchdogTest(unittest.TestCase):
    """rss_watchdog: the external backstop for solver children that do not
    enforce their envelope themselves (the main ay binary's `pb` subcommand
    ignores MEMLIMIT; external solvers have no knob)."""

    HOG = ("import time\n"
           "b = bytearray(400 * 1024 * 1024)\n"  # ~400 MiB RSS
           "time.sleep(60)\n")

    # A target that exits on a TIMER races the watchdog's arming: under load
    # the arming (a `ps` scan that authenticates the group) can start after a
    # 0.2 s child has already exited, and rss_watchdog then refuses, correctly,
    # to arm on a group that is gone ("cannot authenticate process-group
    # identity"). The targets below exit on an EVENT that exists only once
    # the watchdog is armed, so arming precedes exit by construction. Their
    # 60 s bound is a hang guard, never the expected path: it exits 3.
    #
    # Exits once the file named by argv[1] exists: the armed sidecar's
    # ready signal.
    EXIT_AFTER_READY_FILE = (
        "import os, sys, time\n"
        "deadline = time.monotonic() + 60\n"
        "while not os.path.exists(sys.argv[1]):\n"
        "    if time.monotonic() > deadline:\n"
        "        sys.exit(3)\n"
        "    time.sleep(0.01)\n"
    )
    # Exits 0.5 s after stdin reaches EOF, which the test causes only once
    # rss_watchdog has returned an armed guard; the 0.5 s keeps the child
    # live across several armed polls.
    EXIT_AFTER_STDIN_EOF = (
        "import select, sys, time\n"
        "if not select.select([sys.stdin], [], [], 60)[0]:\n"
        "    sys.exit(3)\n"
        "sys.stdin.read()\n"
        "time.sleep(0.5)\n"
    )
    # How long the stall tests keep the sidecar off the CPU between spawning
    # (or attaching to) the target and arming. A timer-bound target is gone
    # well inside it; an event-bound one cannot be.
    ARMING_STALL_S = 2.0

    def _spawn(self, code, *args, stdin=None):
        proc = subprocess.Popen([sys.executable, "-c", code, *args],
                                stdin=stdin,
                                stdout=subprocess.DEVNULL,
                                stderr=subprocess.DEVNULL,
                                start_new_session=True)
        self.addCleanup(self._kill_if_running, proc)
        return proc

    @staticmethod
    def _kill_if_running(proc):
        """Cleanup for a test that failed before its target exited."""
        if proc.stdin is not None:
            proc.stdin.close()
        if proc.poll() is None:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait(timeout=5)

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

    def _assert_child_within_envelope_untouched(self, arming_stall_s):
        proc = self._spawn(self.EXIT_AFTER_STDIN_EOF, stdin=subprocess.PIPE)
        if arming_stall_s:
            # The harness loses the CPU before arming; the target runs on.
            with contextlib.suppress(subprocess.TimeoutExpired):
                proc.wait(timeout=arming_stall_s)
        guard = og.rss_watchdog(proc, 10000, label="test", poll_s=0.1)
        proc.stdin.close()  # armed: let the child finish inside its envelope
        rc = proc.wait(timeout=30)
        guard.stop()
        self.assertFalse(guard.breached)
        self.assertEqual(rc, 0)

    def test_child_within_envelope_untouched(self):
        self._assert_child_within_envelope_untouched(arming_stall_s=0)

    def test_child_within_envelope_untouched_when_arming_is_descheduled(self):
        self._assert_child_within_envelope_untouched(
            arming_stall_s=self.ARMING_STALL_S
        )

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
            og, "_process_group_exists", return_value=True
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

            def check_enforcement(self):
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

    def _assert_ready_after_arming(self, arming_stall_s):
        with tempfile.TemporaryDirectory() as td:
            ready = Path(td, "ready")
            proc = self._spawn(self.EXIT_AFTER_READY_FILE, str(ready))
            reaper = threading.Thread(target=proc.wait)
            reaper.start()
            arm = og.rss_watchdog

            def descheduled_arm(*args, **kwargs):
                # The sidecar has attached but loses the CPU before arming;
                # the target runs on, and a timer-bound one exits (and is
                # reaped) inside this stall.
                reaper.join(timeout=arming_stall_s)
                return arm(*args, **kwargs)

            with mock.patch.object(og, "rss_watchdog", side_effect=descheduled_arm):
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

    def test_watch_existing_process_signals_ready_after_arming(self):
        self._assert_ready_after_arming(arming_stall_s=0)

    def test_watch_existing_process_signals_ready_when_arming_is_descheduled(self):
        self._assert_ready_after_arming(arming_stall_s=self.ARMING_STALL_S)

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
            if kwargs.get("start_new_session"):
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
            # Record only session leaders: guarded_popen owns exactly one
            # (start_new_session=True). On procfs-less hosts (macOS) the
            # identity checks and RSS polls shell out to `ps` through this
            # same patched subprocess module at watchdog-poll cadence;
            # counting those helper spawns would make this reap assertion
            # both platform- and timing-dependent.
            if kwargs.get("start_new_session"):
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

        # Synthesize a one-process /proc so the Linux snapshot path (the code
        # that implements the shared-scan contract) runs on procfs-less hosts
        # (macOS) too, and so the observed value is exact rather than whatever
        # a loaded benchmark host happens to be doing.
        pgid = os.getpgid(0)
        page_kb = os.sysconf("SC_PAGE_SIZE") // 1024
        resident_pages = (7 * 1024) // page_kb
        expected_mb = resident_pages * page_kb // 1024
        real_exists = os.path.exists
        real_listdir = os.listdir
        real_open = open

        def fake_exists(path):
            return True if path == "/proc/self/stat" else real_exists(path)

        def fake_listdir(path):
            return ["4242"] if path == "/proc" else real_listdir(path)

        def fake_open(path, *args, **kwargs):
            if path == "/proc/4242/stat":
                return io.StringIO(f"4242 (fake-solver) S 1 {pgid} 0 0 0\n")
            if path == "/proc/4242/statm":
                return io.StringIO(
                    f"{2 * resident_pages} {resident_pages} 0 0 0 0 0\n"
                )
            return real_open(path, *args, **kwargs)

        def inspect():
            try:
                barrier.wait(timeout=5)
                results.append(og.process_group_rss_mb(pgid))
            except Exception as error:
                errors.append(error)

        with mock.patch.object(og, "_RSS_SNAPSHOT_TTL_S", 60.0), \
             mock.patch.object(og.os.path, "exists", new=fake_exists), \
             mock.patch.object(og.os, "listdir", new=fake_listdir), \
             mock.patch.object(og, "open", new=fake_open, create=True):
            threads = [threading.Thread(target=inspect) for _ in range(workers)]
            for thread in threads:
                thread.start()
            for thread in threads:
                thread.join(timeout=10)
        self.assertFalse(any(thread.is_alive() for thread in threads))
        self.assertEqual(errors, [])
        self.assertEqual(
            results,
            [expected_mb] * workers,
            "every waiter must observe the one shared snapshot's value",
        )
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
        real_exists = os.path.exists

        def fake_exists(path):
            # Force the Linux snapshot path (the code under test) on
            # procfs-less hosts (macOS) too.
            return True if path == "/proc/self/stat" else real_exists(path)

        def slow_empty_proc(_path):
            time.sleep(0.1)
            return ["not-a-pid"]

        def inspect(index):
            try:
                barrier.wait(timeout=5)
                # Stagger arrivals while the first thread holds the scan lock:
                # every waiter must reuse that in-flight scan's result. The
                # guarded regression decided staleness before acquiring the
                # lock, which turned one slow scan into one rescan per waiter
                # (and would fail the scan-count assertion below ~16-fold).
                time.sleep(index * 0.004)
                results.append(og.process_group_rss_mb(os.getpgid(0)))
            except Exception as error:
                errors.append(error)

        # The TTL is pinned far above any scheduling delay: on a loaded host a
        # waiter can be descheduled past the real 0.02s TTL after the scan
        # completes, which would make a second scan legitimate and the
        # scan-count assertion flaky. The pre-lock-staleness regression is
        # TTL-independent (the buggy decision happens while the snapshot is
        # still unpublished), so pinning loses no coverage.
        with mock.patch.object(og, "_RSS_SNAPSHOT_TTL_S", 60.0), \
             mock.patch.object(og.os.path, "exists", new=fake_exists), \
             mock.patch.object(og.os, "listdir", side_effect=slow_empty_proc):
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
        # None (measurement failure) for every waiter — never 0, and never a
        # per-waiter retry.
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
        guard = mock.Mock(breach_time_ns=None)
        with mock.patch.object(og, "guarded_popen", return_value=(proc, guard)), \
             mock.patch.object(og, "wait_guarded_exit", side_effect=OSError("simulated wait failure")):
            with self.assertRaisesRegex(OSError, "simulated wait failure"):
                og.run_guarded(["solver"], 128, timeout_s=1)
        guard.finish.assert_called_once_with(proc, "harness")

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
        with mock.patch.object(og.threading, "Thread"), \
             mock.patch.object(og.threading.Event, "wait", return_value=True):
            guard = og._RssWatchdog(mock.Mock(pid=4242), 4242, 128, 0.02,
                                    "stuck-watchdog-test", (4243, "anchor"))
        guard._phase = og._WatchPhase.QUIESCED
        guard._stop_evt = mock.Mock()
        guard._thread.is_alive.return_value = True
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


class GroupExitTest(unittest.TestCase):
    """`_group_has_exited` on real process groups."""

    def test_an_exited_unreaped_child_has_exited_and_a_live_one_has_not(self):
        exited = subprocess.Popen(["/bin/sh", "-c", "exit 0"], start_new_session=True)
        live = subprocess.Popen(["/bin/sh", "-c", "sleep 30"], start_new_session=True)
        try:
            deadline = time.monotonic() + 5
            while not og._group_has_exited(exited.pid) and time.monotonic() < deadline:
                time.sleep(0.02)
            self.assertTrue(og._group_has_exited(exited.pid))
            self.assertTrue(og._process_group_exists(exited.pid), "the zombie holds its group")
            self.assertFalse(og._group_has_exited(live.pid))
        finally:
            exited.wait()
            live.kill()
            live.wait()
        self.assertFalse(og._group_has_exited(exited.pid), "no members is not an exit")

    def test_an_unreadable_process_listing_is_not_an_exit(self):
        with mock.patch.object(og.subprocess, "run", side_effect=OSError("no ps")):
            self.assertFalse(og._group_has_exited(os.getpid()))

    def test_a_group_reaped_after_the_probe_has_ended(self):
        # A real child its parent reaps at once: whatever moment the reap
        # lands at, the group has ended once it is reaped, and a live group
        # has not.
        exited = subprocess.Popen(["/bin/sh", "-c", "exit 0"], start_new_session=True)
        live = subprocess.Popen(["/bin/sh", "-c", "sleep 30"], start_new_session=True)
        try:
            exited.wait()
            self.assertTrue(og._group_has_ended(exited.pid))
            self.assertFalse(og._group_has_ended(live.pid))
        finally:
            live.kill()
            live.wait()

    def test_ended_needs_the_group_gone_after_an_empty_listing(self):
        # Probe finds the group, the listing finds no member (it was reaped in
        # between), the second probe no longer finds it: ended. The same
        # listing with the group still found is not an exit (fail-closed).
        with mock.patch.object(og, "_group_has_exited", return_value=False):
            with mock.patch.object(og, "_process_group_exists", side_effect=[True, False]):
                self.assertTrue(og._group_has_ended(4242))
            with mock.patch.object(og, "_process_group_exists", side_effect=[True, True]):
                self.assertFalse(og._group_has_ended(4242))


class GuardCompletionModelTest(unittest.TestCase):
    """Deterministic lifecycle controls: no real process or watchdog thread."""

    @contextlib.contextmanager
    def model(self):
        proc = mock.Mock(pid=4242, returncode=0, args=["modeled-child"])
        proc.poll.return_value = 0
        proc.wait.return_value = 0
        guard = og._RssWatchdog.__new__(og._RssWatchdog)
        guard.armed = True
        guard.breached = False
        guard.breach_time_ns = None
        guard.peak_rss_mb = 7
        guard._proc = guard._owned_proc = proc
        guard._pgid = 4242
        guard._kill_mb = 128
        guard._poll_s = 0.02
        guard._label = "completion-model"
        guard._group_identity = (4243, "original-anchor")
        guard._stop_evt = threading.Event()
        guard._ready_evt = threading.Event()
        guard._terminal_evt = threading.Event()
        guard._lifecycle_lock = threading.RLock()
        guard._phase = og._WatchPhase.ACTIVE
        guard._events = []
        guard._worker_error = None
        guard._kill_sent = False
        guard._frozen_members = None
        guard.identity_lost = False
        guard.identity_lost_time_ns = None
        state = {"alive": True, "stopped": False, "joined": False, "trace": []}

        def join(timeout=None):
            state["trace"].append("join")
            state["joined"] = True
            guard._terminal_evt.set()

        guard._thread = mock.Mock()
        guard._thread.is_alive.side_effect = lambda: not state["joined"]
        guard._thread.join.side_effect = join

        def signal_group(pgid, signum):
            self.assertEqual(pgid, 4242)
            self.assertTrue(state["alive"], "must not signal an absent/recycled group")
            state["trace"].append(signum)
            if signum == signal.SIGSTOP:
                self.assertFalse(state["joined"], "must keep monitoring through stop delivery")
                state["stopped"] = True
            elif signum == signal.SIGKILL:
                state["alive"] = False
            else:
                self.fail("unexpected group signal")

        def snapshot(pgid, identity):
            state["trace"].append("snapshot")
            self.assertEqual(identity, guard._group_identity)
            if state["alive"] and state["stopped"]:
                return ((4243, "original-anchor"), (4244, "original-child"))
            return None

        with contextlib.ExitStack() as stack:
            stack.enter_context(mock.patch.object(og, "_group_identity_is_current", side_effect=lambda *_: state["alive"]))
            stack.enter_context(mock.patch.object(og, "_process_group_exists", side_effect=lambda *_: state["alive"]))
            stack.enter_context(mock.patch.object(og.os, "killpg", side_effect=signal_group))
            stack.enter_context(mock.patch.object(og, "_stopped_group_snapshot", side_effect=snapshot))
            stack.enter_context(mock.patch.object(og.time, "sleep"))
            yield proc, guard, state

    def test_finish_stops_and_observes_group_before_join_then_kills_once(self):
        with self.model() as (proc, guard, state):
            evidence = guard.finish(proc)
            self.assertEqual(evidence["phase"], "reaped")
            self.assertFalse(evidence["identity_lost"])
            self.assertIsNone(evidence["worker_error"])
            trace = state["trace"]
            self.assertGreaterEqual(trace.count("snapshot"), 3)
            self.assertLess(trace.index(signal.SIGSTOP), trace.index("join"))
            self.assertLess(trace.index("snapshot"), trace.index("join"))
            self.assertLess(trace.index("join"), trace.index(signal.SIGKILL))
            self.assertEqual(trace.count(signal.SIGKILL), 1)
            self.assertNotIn(signal.SIGCONT, trace)

    def test_finish_refuses_a_different_process_owner_before_signalling(self):
        with self.model() as (_, guard, state):
            with self.assertRaisesRegex(og.GuardEnforcementError, "different process owner"):
                guard.finish(mock.Mock(pid=4242))
            self.assertEqual(state["trace"], [])

    def test_launch_does_not_resume_if_monitor_failed_before_sigcont(self):
        with self.model() as (proc, guard, state):
            guard._worker_error = "monitor failed during launch"
            guard._phase = og._WatchPhase.ERROR
            with mock.patch.object(og.subprocess, "Popen", return_value=proc), \
                 mock.patch.object(og.os, "getpgid", return_value=4242), \
                 mock.patch.object(og, "_watch_process_identity", return_value=(4242, "leader")), \
                 mock.patch.object(og, "_group_watch_identity", return_value=guard._group_identity), \
                 mock.patch.object(og, "_wait_for_guard_stop"), \
                 mock.patch.object(og, "rss_watchdog", return_value=guard):
                with self.assertRaises(og.GuardEnforcementError):
                    og.guarded_popen(["modeled-child"], 128)
            self.assertNotIn(signal.SIGCONT, state["trace"])
            self.assertFalse(state["alive"])

    def test_early_monitor_stop_stays_refused_after_successful_cleanup(self):
        with self.model() as (proc, guard, state):
            guard.stop()
            with self.assertRaises(og.GuardEnforcementError):
                guard.finish(proc)
            self.assertIsNotNone(guard.evidence()["worker_error"])
            self.assertFalse(state["alive"])
            self.assertNotIn(signal.SIGSTOP, state["trace"])

    def test_direct_stop_accepts_fresh_whole_group_absence_without_prior_error(self):
        with self.model() as (proc, guard, state):
            state["alive"] = False
            guard.stop()
            guard.check_enforcement()
            self.assertEqual(guard._phase, og._WatchPhase.GROUP_GONE)
            self.assertIsNone(guard._worker_error)
            self.assertEqual(guard.finish(proc)["phase"], "reaped")

    def test_pre_resume_memout_returns_terminal_guard_without_sigcont(self):
        with self.model() as (proc, guard, state):
            state["alive"] = False
            guard._phase = og._WatchPhase.KILL_SENT
            guard._kill_sent = guard.breached = True
            guard.breach_time_ns = 1
            with mock.patch.object(og.subprocess, "Popen", return_value=proc), \
                 mock.patch.object(og.os, "getpgid", return_value=4242), \
                 mock.patch.object(og, "_watch_process_identity", return_value=(4242, "leader")), \
                 mock.patch.object(og, "_group_watch_identity", return_value=guard._group_identity), \
                 mock.patch.object(og, "_wait_for_guard_stop"), \
                 mock.patch.object(og, "rss_watchdog", return_value=guard):
                self.assertEqual(og.guarded_popen(["modeled-child"], 128), (proc, guard))
            self.assertNotIn(signal.SIGCONT, state["trace"])
            self.assertEqual(guard.finish(proc)["phase"], "reaped")
            self.assertTrue(guard.breached)
            self.assertFalse(guard.identity_lost)

    def test_identity_loss_stays_refused_if_same_identity_recovers_for_cleanup(self):
        with self.model() as (proc, guard, state):
            with mock.patch.object(og, "_group_identity_is_current", return_value=False):
                with guard._lifecycle_lock:
                    self.assertFalse(guard._retain_authenticated_group())
            with self.assertRaises(og.GuardEnforcementError):
                guard.finish(proc)
            self.assertTrue(guard.identity_lost)
            self.assertIsNotNone(guard.identity_lost_time_ns)
            self.assertFalse(state["alive"])

    def test_recycled_group_is_never_signalled_or_accepted(self):
        with self.model() as (proc, guard, state):
            with mock.patch.object(og, "_group_identity_is_current", return_value=False), \
                 mock.patch.object(og, "_reap_group_without_signalling", side_effect=og.GuardEnforcementError("foreign group")):
                with guard._lifecycle_lock:
                    guard._retain_authenticated_group()
                with self.assertRaises(og.GuardEnforcementError):
                    guard.finish(proc)
            self.assertNotIn(signal.SIGSTOP, state["trace"])
            self.assertNotIn(signal.SIGKILL, state["trace"])

    def test_monitor_exception_is_sticky_even_with_child_exit_zero(self):
        with self.model() as (proc, guard, state):
            with mock.patch.object(guard._stop_evt, "wait", return_value=False), \
                 mock.patch.object(og, "process_group_rss_mb", side_effect=OSError("sampler broken")):
                guard._watch()
            with self.assertRaises(og.GuardEnforcementError):
                guard.finish(proc)
            self.assertIn("sampler broken", guard.evidence()["worker_error"])
            self.assertFalse(state["alive"])

    def test_watchdog_memout_uses_own_terminal_kill_without_identity_loss(self):
        with self.model() as (proc, guard, state):
            with mock.patch.object(guard._stop_evt, "wait", return_value=False), \
                 mock.patch.object(og, "process_group_rss_mb", return_value=129):
                guard._watch()
            evidence = guard.finish(proc)
            self.assertTrue(guard.breached)
            self.assertFalse(guard.identity_lost)
            self.assertEqual(evidence["phase"], "reaped")
            self.assertEqual(state["trace"].count(signal.SIGKILL), 1)
            self.assertNotIn(signal.SIGSTOP, state["trace"])

    def test_observed_whole_group_absence_is_not_nonempty_identity_loss(self):
        with self.model() as (proc, guard, state):
            state["alive"] = False
            with mock.patch.object(guard._stop_evt, "wait", return_value=False):
                guard._watch()
            evidence = guard.finish(proc)
            self.assertEqual(evidence["phase"], "reaped")
            self.assertFalse(evidence["identity_lost"])
            self.assertNotIn(signal.SIGKILL, state["trace"])
            self.assertTrue(any(e["kind"] == "whole-group-absent" for e in evidence["events"]))

    def test_exited_unreaped_child_is_whole_group_exit_not_identity_loss(self):
        # macOS: getpgid(zombie) is ESRCH, so the identity check fails while
        # the unreaped zombie still holds the group. That is the child's exit.
        with self.model() as (proc, guard, state):
            state["zombie"] = True

            def reap(timeout=None):
                state["zombie"] = False
                return 0

            proc.wait.side_effect = reap
            with mock.patch.object(og, "_group_identity_is_current", return_value=False), \
                 mock.patch.object(og, "_process_group_exists", side_effect=lambda *_: state["zombie"]), \
                 mock.patch.object(og, "_group_has_exited", side_effect=lambda *_: state["zombie"]), \
                 mock.patch.object(guard._stop_evt, "wait", return_value=False):
                guard._watch()
                evidence = guard.finish(proc)
            self.assertEqual(evidence["phase"], "reaped")
            self.assertFalse(evidence["identity_lost"])
            self.assertNotIn(signal.SIGSTOP, state["trace"])
            self.assertNotIn(signal.SIGKILL, state["trace"])
            self.assertTrue(any(e["kind"] == "whole-group-exited" for e in evidence["events"]))

    def test_group_reaped_between_probe_and_listing_is_gone_not_identity_loss(self):
        # The parent reaps the last zombie after the existence probe found the
        # group and before the member listing: the listing finds no member,
        # and the probe no longer finds the group. That is the child's exit.
        with self.model() as (proc, guard, state):
            state["zombie"] = True

            def probe(*_):
                present = state["zombie"]
                if present:
                    state["zombie"] = False  # reaped right after this probe
                return present

            with mock.patch.object(og, "_group_identity_is_current", return_value=False), \
                 mock.patch.object(og, "_process_group_exists", side_effect=probe), \
                 mock.patch.object(og, "_group_has_exited", return_value=False), \
                 mock.patch.object(guard._stop_evt, "wait", return_value=False):
                guard._watch()
                evidence = guard.finish(proc)
            self.assertEqual(evidence["phase"], "reaped")
            self.assertFalse(evidence["identity_lost"])
            self.assertNotIn(signal.SIGSTOP, state["trace"])
            self.assertNotIn(signal.SIGKILL, state["trace"])
            self.assertTrue(any(e["kind"] == "whole-group-reaped" for e in evidence["events"]))

    def test_group_still_found_after_an_empty_listing_is_identity_loss(self):
        # NEGATIVE CONTROL: an empty listing alone decides nothing. A group the
        # probe still finds after it keeps the loss fail-closed.
        with self.model() as (proc, guard, state):
            with mock.patch.object(og, "_group_identity_is_current", return_value=False), \
                 mock.patch.object(og, "_process_group_exists", return_value=True), \
                 mock.patch.object(og, "_group_has_exited", return_value=False), \
                 mock.patch.object(guard._stop_evt, "wait", return_value=False):
                guard._watch()
                self.assertTrue(guard.identity_lost)
                with self.assertRaisesRegex(og.GuardEnforcementError, "enforcement lost"):
                    guard.finish(proc)
            self.assertNotIn(signal.SIGKILL, state["trace"])

    def test_late_runnable_member_prevents_quiescent_completion(self):
        with self.model() as (proc, guard, state):
            members = ((4243, "original-anchor"), (4244, "original-child"))
            with mock.patch.object(og, "_stopped_group_snapshot", side_effect=[members, members, None]):
                with self.assertRaisesRegex(og.GuardEnforcementError, "stopped group changed"):
                    guard.finish(proc)
            self.assertFalse(state["alive"], "authenticated abort still cleans the changed group")

    def test_a_stalled_host_delays_the_stop_and_finish_still_quiesces(self):
        """On a shared host under load the stop of a finished solver can take seconds to
        show: here four listings of 3 s each see a runnable member before the group shows
        stopped. finish waits for it and completes; it used to give up after 5 s with
        `cannot confirm whole-group quiescence`, which cancels a differential campaign."""
        clock = [1000.0]
        with self.model() as (proc, guard, state), \
                mock.patch.object(og.time, "monotonic", side_effect=lambda: clock[0]):
            settled = og._stopped_group_snapshot  # the model's: stopped members once SIGSTOP landed

            def stalled(pgid, identity):
                if clock[0] < 1012.0:
                    clock[0] += 3.0
                    return None
                return settled(pgid, identity)

            with mock.patch.object(og, "_stopped_group_snapshot", side_effect=stalled):
                evidence = guard.finish(proc)
        self.assertEqual(evidence["phase"], "reaped")
        self.assertEqual(state["trace"].count(signal.SIGKILL), 1)

    def test_a_listing_slower_than_five_seconds_is_waited_for(self):
        """A `ps` listing that takes 12 s on a stalled host is waited for; it used to time
        out at 5 s, and the guard refused the run (`cannot inspect stopped group`)."""
        identity = (4243, "original-anchor")

        def listing(argv, timeout=None, **_):
            if timeout is not None and timeout < 12:
                raise subprocess.TimeoutExpired(argv, timeout)
            return types.SimpleNamespace(stdout="4243 4242 T\n")

        with mock.patch.object(og.subprocess, "run", side_effect=listing), \
             mock.patch.object(og, "_watch_process_identity", side_effect=lambda pid: (pid, "original-anchor")), \
             mock.patch.object(og, "_safe_getpgid", return_value=4242):
            self.assertEqual(og._stopped_group_snapshot(4242, identity), (identity,))

    def test_an_identity_listing_slower_than_ten_seconds_is_waited_for(self):
        """The `ps` listing that picks a new group's identity, at spawn and again when its
        monitor arms, is waited for when it takes 12 s; it used to time out at 10 s, and
        the spawn failed `cannot authenticate process-group identity`."""
        def listing(argv, timeout=None, **_):
            if timeout is not None and timeout < 12:
                raise subprocess.TimeoutExpired(argv, timeout)
            return types.SimpleNamespace(returncode=0, stdout="4242 4242\n4243 4242\n4300 4300\n")

        def exists(path):
            return False if path == "/proc/self/stat" else os.path.exists(path)

        with mock.patch.object(og.os.path, "exists", side_effect=exists), \
             mock.patch.object(og.subprocess, "run", side_effect=listing), \
             mock.patch.object(og, "_watch_process_identity", side_effect=lambda pid: (pid, "anchor")), \
             mock.patch.object(og, "_safe_getpgid", return_value=4242):
            self.assertEqual(og._group_watch_identity(4242, 4242), (4243, "anchor"))

    def test_a_guarded_child_slower_than_ten_seconds_to_stop_is_waited_for(self):
        """The exec-stopped wrapper of a new guarded child stops itself before it runs the
        command; on a stalled host that can take 12 s, and the guard waits for it. It used
        to give up at 10 s with `guarded child did not stop for attach`."""
        clock = [1000.0]
        stopped = (signal.SIGSTOP << 8) | 0x7F  # the wait status of a SIGSTOPped child

        def waitpid(pid, _options):
            return (pid, stopped) if clock[0] >= 1012.0 else (0, 0)

        with mock.patch.object(og.os, "waitpid", side_effect=waitpid), \
             mock.patch.object(og.time, "monotonic", side_effect=lambda: clock[0]), \
             mock.patch.object(og.time, "sleep", side_effect=lambda s: clock.__setitem__(0, clock[0] + 1.0)):
            og._wait_for_guard_stop(types.SimpleNamespace(pid=4242), 4242, "stalled-spawn-test")
        self.assertGreaterEqual(clock[0], 1012.0)

    @staticmethod
    def bounded_clock(what):
        """A fake clock whose sleep moves it 1 s, and which fails the test, rather than
        hanging it, once ten settle bounds have passed: a wait with no bound."""
        clock = [1000.0]

        def tick(_seconds):
            clock[0] += 1.0
            if clock[0] > 1000.0 + 10 * og._GROUP_SETTLE_S:
                raise AssertionError(f"{what} has no bound")

        return clock, tick

    def test_a_group_that_never_shows_quiescent_fails_once_the_settle_bound_passes(self):
        """The settle bound is a hang detector, not a licence to wait: a group that never
        shows the same stopped members twice fails `cannot confirm whole-group quiescence`
        once `_GROUP_SETTLE_S` has passed, and the authenticated abort still kills it once."""
        clock, tick = self.bounded_clock("the quiescence wait")
        with self.model() as (proc, guard, state), \
                mock.patch.object(og.time, "monotonic", side_effect=lambda: clock[0]), \
                mock.patch.object(og.time, "sleep", side_effect=tick), \
                mock.patch.object(og, "_stopped_group_snapshot", return_value=None):
            with self.assertRaisesRegex(og.GuardEnforcementError, "cannot confirm whole-group quiescence"):
                guard.finish(proc)
        self.assertGreaterEqual(clock[0], 1000.0 + og._GROUP_SETTLE_S)
        self.assertFalse(state["alive"])
        self.assertEqual(state["trace"].count(signal.SIGKILL), 1)

    def test_a_guarded_child_that_never_stops_fails_once_the_settle_bound_passes(self):
        """A new guarded child that never stops itself for attach fails `guarded child did
        not stop for attach` once `_GROUP_SETTLE_S` has passed."""
        clock, tick = self.bounded_clock("the wait for the stop")
        with mock.patch.object(og.os, "waitpid", return_value=(0, 0)), \
             mock.patch.object(og.time, "monotonic", side_effect=lambda: clock[0]), \
             mock.patch.object(og.time, "sleep", side_effect=tick):
            with self.assertRaisesRegex(og.GuardEnforcementError, "did not stop for attach"):
                og._wait_for_guard_stop(types.SimpleNamespace(pid=4242), 4242, "never-stops-test")
        self.assertGreaterEqual(clock[0], 1000.0 + og._GROUP_SETTLE_S)

    def test_a_killed_group_is_waited_for_until_it_disappears_and_no_longer(self):
        """After the final kill the reap waits for the group to leave the process table: on
        a stalled host for 12 s, and it used to give up at 5 s (`could not confirm
        whole-group disappearance`). A group that never leaves still fails that way once
        `_GROUP_SETTLE_S` has passed."""
        for leaves_at, fails in ((1012.0, False), (float("inf"), True)):
            with self.subTest(leaves_at=leaves_at):
                clock, tick = self.bounded_clock("the wait for the group to disappear")
                proc = mock.Mock(pid=4242)
                proc.wait.return_value = 0
                with mock.patch.object(og, "_process_group_exists", side_effect=lambda _pgid: clock[0] < leaves_at), \
                     mock.patch.object(og.time, "monotonic", side_effect=lambda: clock[0]), \
                     mock.patch.object(og.time, "sleep", side_effect=tick):
                    if fails:
                        with self.assertRaisesRegex(og.GuardEnforcementError, "whole-group disappearance"):
                            og._reap_group_without_signalling(proc, 4242, "never-leaves-test")
                        self.assertGreaterEqual(clock[0], 1000.0 + og._GROUP_SETTLE_S)
                    else:
                        og._reap_group_without_signalling(proc, 4242, "slow-to-leave-test")
                        self.assertGreaterEqual(clock[0], leaves_at)
                proc.wait.assert_called_once_with(timeout=og._GROUP_SETTLE_S)

    def test_the_exit_and_identity_listings_are_waited_for_on_a_stalled_host(self):
        """Two more `ps` listings take 12 s on a stalled host and are waited for. The one
        that tells an all-zombie group from a live one used to time out at 5 s, and a
        finished group read as still running; the one that reads a member's start time
        used to time out at 5 s too, and the monitor read a lost identity, which ends its
        enforcement of the group for good."""
        def listing(argv, timeout=None, **_):
            if timeout is not None and timeout < 12:
                raise subprocess.TimeoutExpired(argv, timeout)
            if argv[:2] == ["ps", "-axo"]:
                return types.SimpleNamespace(returncode=0, stdout="4243 4242 Z\n")
            return types.SimpleNamespace(returncode=0, stdout="Thu Oct  8 10:00:00 2026\n")

        with mock.patch.object(og.subprocess, "run", side_effect=listing), \
             mock.patch.object(og, "_process_identity", side_effect=lambda pid: (pid, None)):
            self.assertTrue(og._group_has_exited(4242))
            self.assertEqual(og._watch_process_identity(4243), (4243, "Thu Oct  8 10:00:00 2026"))

    def test_snapshot_refuses_runnable_missing_anchor_unknown_and_duplicate_rows(self):
        identity = (4243, "original-anchor")
        for rows in ("4243 4242 R\n", "4244 4242 T\n", "4243 4242 ?\n"):
            with self.subTest(rows=rows), \
                 mock.patch.object(og.subprocess, "run", return_value=types.SimpleNamespace(stdout=rows)), \
                 mock.patch.object(og, "_watch_process_identity", side_effect=lambda pid: (pid, "original-anchor")), \
                 mock.patch.object(og, "_safe_getpgid", return_value=4242):
                self.assertIsNone(og._stopped_group_snapshot(4242, identity))
        for rows in ("malformed\n", "4243 4242 T\n4243 4242 T\n"):
            with self.subTest(rows=rows), \
                 mock.patch.object(og.subprocess, "run", return_value=types.SimpleNamespace(stdout=rows)), \
                 mock.patch.object(og, "_watch_process_identity", return_value=identity), \
                 mock.patch.object(og, "_safe_getpgid", return_value=4242):
                with self.assertRaises(og.GuardEnforcementError):
                    og._stopped_group_snapshot(4242, identity)

    def test_wait_refuses_failed_monitor_before_accepting_zero_exit(self):
        with self.model() as (proc, guard, _):
            guard._worker_error = "monitor unavailable"
            with self.assertRaises(og.GuardEnforcementError):
                og.wait_guarded_exit(proc, guard, 1)
            proc.poll.assert_not_called()

    def test_run_guarded_does_not_return_success_when_completion_refuses(self):
        proc = mock.Mock(pid=4242, returncode=0)
        guard = mock.Mock(breach_time_ns=None)
        guard.finish.side_effect = og.GuardEnforcementError("identity lost")
        with mock.patch.object(og, "guarded_popen", return_value=(proc, guard)), \
             mock.patch.object(og, "wait_guarded_exit", return_value=0):
            with self.assertRaisesRegex(og.GuardEnforcementError, "identity lost"):
                og.run_guarded(["modeled-child"], 128, timeout_s=1)
        guard.finish.assert_called_once_with(proc, "harness")

    def test_run_captured_does_not_return_success_when_completion_refuses(self):
        proc = mock.Mock(pid=4242, returncode=0, stdout=io.BytesIO(b"ok"), stderr=io.BytesIO())
        proc.poll.return_value = 0
        guard = mock.Mock()
        guard.finish.side_effect = og.GuardEnforcementError("monitor failed")
        with mock.patch.object(og, "guarded_popen", return_value=(proc, guard)):
            with self.assertRaisesRegex(og.GuardEnforcementError, "monitor failed"):
                og.run_captured(["modeled-child"], 128, timeout_s=1)
        guard.finish.assert_called_once_with(proc, "harness")

    def test_a_slow_spawn_does_not_spend_the_childs_budget(self):
        """The spawn's waits are hang detectors (`_GROUP_SETTLE_S`), so on a stalled host
        the spawn alone can outlast a solver's whole budget. The budget, and run_captured's
        wall time, start at the authenticated resume: a 30 s spawn and then a 2 s solve in
        a 5 s budget is an answer. Both used to start before the spawn, so the solver was
        killed as it resumed, recorded as a time-out, and its printed answer thrown away
        (the differential gate then read the posture as undecided)."""
        for runner in ("run_captured", "run_guarded"):
            with self.subTest(runner=runner):
                clock = [1000.0]
                proc = mock.Mock(pid=4242, returncode=0,
                                 stdout=io.BytesIO(b"unsat\n"), stderr=io.BytesIO())
                proc.poll.side_effect = lambda: 0 if clock[0] >= 1032.0 else None
                guard = mock.Mock(breach_time_ns=None)
                guard._owned_proc = proc
                guard.finish.return_value = {"phase": "reaped"}

                def slow_spawn(*_args, **_kwargs):
                    clock[0] += 30.0
                    return proc, guard

                def tick(_seconds):
                    clock[0] += 0.5
                    if clock[0] > 1100.0:
                        raise AssertionError("the modeled child never finished")

                with mock.patch.object(og, "guarded_popen", side_effect=slow_spawn), \
                     mock.patch.object(og.time, "monotonic", side_effect=lambda: clock[0]), \
                     mock.patch.object(og.time, "sleep", side_effect=tick):
                    if runner == "run_captured":
                        result = og.run_captured(["modeled-child"], 128, timeout_s=5)
                        self.assertFalse(result.timed_out)
                        self.assertEqual(result.stdout, "unsat\n")
                        self.assertLess(result.wall_sec, 5.0)
                    else:
                        self.assertEqual(og.run_guarded(["modeled-child"], 128, timeout_s=5), 0)

    def test_attached_watch_does_not_report_done_on_identity_loss(self):
        guard = mock.Mock(armed=True)
        guard.wait_terminal.return_value = True
        guard.check_enforcement.side_effect = og.GuardEnforcementError("identity lost")
        with mock.patch.object(og, "_AttachedProcess", return_value=mock.Mock(pid=4242)), \
             mock.patch.object(og, "rss_watchdog", return_value=guard):
            with self.assertRaisesRegex(og.GuardEnforcementError, "identity lost"):
                og.watch_existing_process(4242, 128)
        guard.terminate_if_authenticated.assert_called_once_with()

    def test_failed_launch_never_learns_a_replacement_group_identity(self):
        proc = mock.Mock(pid=4242, _guard_group_identity=(4243, "original-anchor"), _guard_kill_sent=False)
        with mock.patch.object(og, "_group_identity_is_current", return_value=False), \
             mock.patch.object(og, "_process_group_exists", return_value=True), \
             mock.patch.object(og.os, "killpg") as send:
            with self.assertRaises(og.GuardEnforcementError):
                og._kill_and_reap_group(proc, 4242, "failed-launch")
        send.assert_not_called()

    def test_unarmed_guard_cleanup_uses_launch_identity_without_completion(self):
        with self.model() as (proc, guard, state):
            proc._guard_group_identity = guard._group_identity
            proc._guard_kill_sent = False
            unarmed = og._NoopWatchdog()
            with mock.patch.object(unarmed, "stop") as stop:
                og._kill_reap_failed_spawn(proc, 4242, unarmed)
            self.assertFalse(state["alive"])
            self.assertEqual(state["trace"].count(signal.SIGKILL), 1)
            proc.wait.assert_called_once_with(timeout=og._GROUP_SETTLE_S)
            stop.assert_called_once_with()
            self.assertFalse(hasattr(unarmed, "finish"))


class CapturedSetupCleanupTest(unittest.TestCase):
    """Post-spawn setup failures must retain authenticated cleanup ownership."""

    @contextlib.contextmanager
    def setup_model(self, *, fail_start=None, fail_construct=None,
                    started_before_error=False, stuck=None, finish_error=None):
        proc = mock.Mock(pid=4242, returncode=0)
        proc.stdout = io.BytesIO(b"output")
        proc.stderr = io.BytesIO()
        proc.stdin = io.BytesIO()
        proc.poll.return_value = 0
        guard = mock.Mock(breach_time_ns=None)
        guard.finish.side_effect = finish_error
        original = RuntimeError("injected capture setup failure")
        threads = []
        owner = self

        class CaptureThread:
            def __init__(self, *, target, args=(), name, daemon):
                self.name = name
                self.target = target
                self.args = args
                self.ident = None
                self.joined = False
                self.alive = False
                if name == fail_construct:
                    raise original
                threads.append(self)

            def start(self):
                if self.name != fail_start or started_before_error:
                    self.ident = len(threads)
                    self.alive = True
                if self.name == fail_start:
                    raise original

            def join(self, timeout):
                owner.assertIsNotNone(self.ident, "never join an unstarted thread")
                owner.assertTrue(guard.finish.called, "finish must precede pipe joining")
                owner.assertEqual(timeout, 5)
                self.joined = True
                if self.name != stuck:
                    self.target(*self.args)
                    self.alive = False

            def is_alive(self):
                return self.alive

        with mock.patch.object(og, "guarded_popen", return_value=(proc, guard)), \
             mock.patch.object(og.threading, "Thread", CaptureThread):
            yield proc, guard, threads, original

    def test_invalid_utf8_input_is_rejected_before_spawn(self):
        with mock.patch.object(og, "guarded_popen") as spawn:
            with self.assertRaises(UnicodeEncodeError):
                og.run_captured(["modeled-child"], 128, 1, input_text="\ud800")
        spawn.assert_not_called()

    def test_each_partial_thread_start_failure_finishes_and_closes_streams(self):
        for name in ("harness-stdout", "harness-stderr", "harness-stdin"):
            for started_before_error in (False, True):
                with self.subTest(name=name, started=started_before_error), \
                     self.setup_model(fail_start=name,
                                      started_before_error=started_before_error) as state:
                    proc, guard, threads, original = state
                    with self.assertRaises(RuntimeError) as caught:
                        og.run_captured(["modeled-child"], 128, 1, input_text="input")
                    self.assertIs(caught.exception, original)
                    guard.finish.assert_called_once_with(proc, "harness")
                    proc.poll.assert_not_called()
                    for thread in threads:
                        self.assertEqual(thread.joined, thread.ident is not None)
                    self.assertTrue(all(s.closed for s in (proc.stdout, proc.stderr, proc.stdin)))

    def test_each_thread_constructor_failure_also_finishes_and_closes_streams(self):
        for name in ("harness-stdout", "harness-stderr", "harness-stdin"):
            with self.subTest(name=name), self.setup_model(fail_construct=name) as state:
                proc, guard, threads, original = state
                with self.assertRaises(RuntimeError) as caught:
                    og.run_captured(["modeled-child"], 128, 1, input_text="input")
                self.assertIs(caught.exception, original)
                guard.finish.assert_called_once_with(proc, "harness")
                proc.poll.assert_not_called()
                for thread in threads:
                    self.assertEqual(thread.joined, thread.ident is not None)
                self.assertTrue(all(s.closed for s in (proc.stdout, proc.stderr, proc.stdin)))

    def test_setup_exception_survives_failed_authenticated_finish(self):
        finish_error = og.GuardEnforcementError("injected identity loss")
        with self.setup_model(fail_start="harness-stderr", finish_error=finish_error) as state:
            proc, guard, threads, original = state
            with self.assertRaises(RuntimeError) as caught:
                og.run_captured(["modeled-child"], 128, 1, input_text="input")
            self.assertIs(caught.exception, original)
            guard.finish.assert_called_once_with(proc, "harness")
            self.assertTrue(threads[0].joined)
            self.assertTrue(all(s.closed for s in (proc.stdout, proc.stderr, proc.stdin)))
            if hasattr(original, "add_note"):
                self.assertIn("injected identity loss", "\n".join(original.__notes__))

    def test_signal_setup_failure_restores_handlers_after_finish(self):
        for failing_signal in (signal.SIGINT, signal.SIGTERM):
            with self.subTest(signum=failing_signal), self.setup_model() as state:
                proc, guard, threads, original = state
                previous = {signal.SIGINT: object(), signal.SIGTERM: object()}

                def install(signum, handler):
                    if handler is previous[signum]:
                        self.assertTrue(guard.finish.called)
                    elif signum == failing_signal:
                        raise original

                with mock.patch.object(og.signal, "getsignal", side_effect=previous.__getitem__) as get, \
                     mock.patch.object(og.signal, "signal", side_effect=install) as set_handler:
                    with self.assertRaises(RuntimeError) as caught:
                        og.run_captured(["modeled-child"], 128, 1, input_text="input")
                self.assertIs(caught.exception, original)
                guard.finish.assert_called_once_with(proc, "harness")
                proc.poll.assert_not_called()
                for call in get.call_args_list:
                    signum = call.args[0]
                    set_handler.assert_any_call(signum, previous[signum])
                self.assertTrue(all(thread.joined for thread in threads))
                self.assertTrue(all(s.closed for s in (proc.stdout, proc.stderr, proc.stdin)))

    def test_real_stderr_start_failure_reaps_guarded_child(self):
        plan = plan_detected_host_with_scratch_lease(self, "capture-setup-test")
        limit = min(256, plan.memlimit_mb)
        self.assertGreaterEqual(limit, 256)
        self.assertEqual(plan.jobs, 1)
        label = "capture-setup-real-test"
        original = RuntimeError("injected real stderr start failure")
        captured = []
        capture_threads = []
        real_spawn = og.guarded_popen
        real_start = threading.Thread.start

        def spawn(*args, **kwargs):
            pair = real_spawn(*args, **kwargs)
            captured.append(pair)
            return pair

        def start(thread):
            if thread.name == f"{label}-stderr":
                raise original
            if thread.name == f"{label}-stdout":
                capture_threads.append(thread)
            return real_start(thread)

        try:
            with mock.patch.object(og, "guarded_popen", side_effect=spawn), \
                 mock.patch.object(threading.Thread, "start", start):
                with self.assertRaises(RuntimeError) as caught:
                    og.run_captured(
                        [sys.executable, "-c", "import time; time.sleep(30)"],
                        limit, timeout_s=5, label=label, input_text="input",
                    )
            self.assertIs(caught.exception, original)
            self.assertEqual(len(captured), 1)
            proc, guard = captured[0]
            evidence = guard.evidence()
            self.assertEqual(evidence["phase"], "reaped")
            self.assertFalse(evidence["identity_lost"])
            self.assertIsNone(evidence["worker_error"])
            self.assertEqual(evidence["kill_threshold_mib"], limit)
            self.assertIsNotNone(proc.returncode)
            self.assertFalse(og._process_group_exists(proc.pid), evidence)
            self.assertEqual(len(capture_threads), 1)
            self.assertIsNotNone(capture_threads[0].ident)
            self.assertFalse(capture_threads[0].is_alive())
            self.assertTrue(all(s.closed for s in (proc.stdout, proc.stderr, proc.stdin)))
        finally:
            # A failing regression must still discharge the real child owner.
            for proc, guard in captured:
                try:
                    if guard.evidence()["phase"] != "reaped":
                        guard.finish(proc, label)
                finally:
                    for thread in capture_threads:
                        if thread.ident is not None:
                            thread.join(timeout=5)
                    if not any(thread.is_alive() for thread in capture_threads):
                        for stream in (proc.stdout, proc.stderr, proc.stdin):
                            stream.close()

    def test_cleanup_does_not_close_a_stream_still_owned_by_a_live_thread(self):
        with self.setup_model(fail_start="harness-stderr", stuck="harness-stdout") as state:
            proc, guard, threads, original = state
            with self.assertRaises(RuntimeError) as caught:
                og.run_captured(["modeled-child"], 128, 1, input_text="input")
            self.assertIs(caught.exception, original)
            guard.finish.assert_called_once_with(proc, "harness")
            self.assertTrue(threads[0].joined)
            self.assertFalse(proc.stdout.closed)
            self.assertTrue(proc.stderr.closed)
            self.assertTrue(proc.stdin.closed)
            if hasattr(original, "add_note"):
                self.assertIn("pipes did not close", "\n".join(original.__notes__))
            proc.stdout.close()  # This test models the thread; none was spawned.


class LegacyGuardedCallerTest(unittest.TestCase):
    """The PB and wait4 owners must never turn a lost monitor into an answer."""

    def model(self, stdout=b"sat\n", returncode=0):
        proc = mock.Mock(pid=4242, returncode=returncode)
        proc.poll.return_value = returncode
        proc.stdout = io.BytesIO(stdout)
        proc.stderr = io.BytesIO()
        guard = mock.Mock(armed=True, breached=False, peak_rss_mb=12)
        guard._owned_proc = proc
        guard.check_enforcement.return_value = None
        guard.finish.return_value = {
            "phase": "reaped", "identity_lost": False, "worker_error": None,
        }
        return proc, guard

    def invoke_pb(self, lane):
        if lane == "solver":
            return pbcomp_harness.run_one(
                "modeled-child", Path("instance.opb"), 5, "python",
                memlimit_mb=256, nbcore=1,
            )
        return pbcomp_harness.check_solution_via_ay(
            "modeled-child", Path("instance.opb"), None, ["x1"], {}, 256,
        )

    def test_pb_callers_refuse_monitor_loss_before_accepting_child_zero(self):
        for lane in ("solver", "checker"):
            with self.subTest(lane=lane):
                proc, guard = self.model()
                guard.check_enforcement.side_effect = og.GuardEnforcementError("lost monitor")
                with mock.patch.object(pbcomp_harness, "guarded_popen", return_value=(proc, guard)), \
                     mock.patch.object(pbcomp_harness, "parse_solver_output_stream") as parse:
                    with self.assertRaisesRegex(og.GuardEnforcementError, "lost monitor"):
                        self.invoke_pb(lane)
                proc.poll.assert_not_called()
                guard.finish.assert_called_once()
                guard.stop.assert_not_called()
                parse.assert_not_called()

    def test_pb_callers_refuse_failed_completion_after_child_zero(self):
        for lane in ("solver", "checker"):
            with self.subTest(lane=lane):
                proc, guard = self.model()
                guard.finish.side_effect = og.GuardEnforcementError("completion refused")
                with mock.patch.object(pbcomp_harness, "guarded_popen", return_value=(proc, guard)), \
                     mock.patch.object(pbcomp_harness, "parse_solver_output_stream") as parse:
                    with self.assertRaisesRegex(og.GuardEnforcementError, "completion refused"):
                        self.invoke_pb(lane)
                self.assertTrue(proc.poll.called)
                guard.finish.assert_called_once()
                parse.assert_not_called()

    def test_pb_timeout_and_memout_precedence_is_preserved(self):
        for lane in ("solver", "checker"):
            for breached in (False, True):
                with self.subTest(lane=lane, breached=breached):
                    proc, guard = self.model(returncode=-signal.SIGKILL)
                    guard.breached = breached
                    with mock.patch.object(pbcomp_harness, "guarded_popen", return_value=(proc, guard)), \
                         mock.patch.object(pbcomp_harness, "wait_guarded_exit",
                                           side_effect=subprocess.TimeoutExpired("modeled-child", 5)):
                        result = self.invoke_pb(lane)
                    guard.finish.assert_called_once()
                    if lane == "solver":
                        self.assertEqual(result.status, "MEMOUT" if breached else "TIMEOUT")
                        self.assertEqual(result.memout, breached)
                        self.assertTrue(result.timed_out)  # historical PB records retain both facts
                    else:
                        self.assertEqual(result, (False, None, "ay verify exceeded memory envelope"
                                                  if breached else "ay verify timed out"))

    def test_pb_output_limit_remains_a_refusal_after_completion(self):
        proc, guard = self.model()
        with mock.patch.object(pbcomp_harness, "guarded_popen", return_value=(proc, guard)), \
             mock.patch.object(pbcomp_harness, "stream_reached_limit", return_value=True), \
             mock.patch.object(pbcomp_harness, "parse_solver_output_stream") as parse:
            result = self.invoke_pb("solver")
        self.assertEqual(result.status, "ERROR")
        self.assertIn("capture limit", result.note)
        parse.assert_not_called()
        guard.finish.assert_called_once()

    @contextlib.contextmanager
    def smt_model(self, proc, guard, wait_results):
        thread = mock.Mock()
        thread.is_alive.return_value = False
        with mock.patch.object(smtcomp_harness, "guarded_popen", return_value=(proc, guard)), \
             mock.patch.object(smtcomp_harness.threading, "Thread", return_value=thread), \
             mock.patch.object(smtcomp_harness.os, "wait4", side_effect=wait_results) as wait4:
            yield wait4

    def invoke_smt(self):
        return smtcomp_harness.run_process(
            smtcomp_harness.Invocation(["modeled-child"]), timeout_s=5, memlimit_mb=256,
        )

    def test_smt_checks_enforcement_before_reaping_child(self):
        proc, guard = self.model()
        guard.check_enforcement.side_effect = og.GuardEnforcementError("lost monitor")
        with self.smt_model(proc, guard, []) as wait4:
            with self.assertRaisesRegex(og.GuardEnforcementError, "lost monitor"):
                self.invoke_smt()
        wait4.assert_not_called()
        guard.finish.assert_called_once()
        guard.stop.assert_not_called()

    def test_smt_checks_enforcement_after_reap_and_before_result(self):
        proc, guard = self.model()
        guard.check_enforcement.side_effect = [None, og.GuardEnforcementError("lost at reap")]
        usage = types.SimpleNamespace(ru_utime=1.25, ru_stime=0.75)
        with self.smt_model(proc, guard, [(4242, 7 << 8, usage)]):
            with self.assertRaisesRegex(og.GuardEnforcementError, "lost at reap"):
                self.invoke_smt()
        self.assertEqual(proc.returncode, 7)
        guard.finish.assert_called_once()

    def test_smt_refuses_failed_completion_after_recording_wait4_status(self):
        proc, guard = self.model()
        guard.finish.side_effect = og.GuardEnforcementError("completion refused")
        usage = types.SimpleNamespace(ru_utime=1.25, ru_stime=0.75)
        with self.smt_model(proc, guard, [(4242, 0, usage)]):
            with self.assertRaisesRegex(og.GuardEnforcementError, "completion refused"):
                self.invoke_smt()
        guard.finish.assert_called_once()
        proc.wait.assert_not_called()

    def test_smt_preserves_exact_wait4_cpu_and_nonzero_exit_before_finish(self):
        proc, guard = self.model()
        usage = types.SimpleNamespace(ru_utime=1.25, ru_stime=0.75)

        def finish(owner, label):
            self.assertIs(owner, proc)
            self.assertEqual(owner.returncode, 7)

        guard.finish.side_effect = finish
        with self.smt_model(proc, guard, [(4242, 7 << 8, usage)]):
            result = self.invoke_smt()
        self.assertEqual(result.exit_code, 7)
        self.assertEqual(result.cpu_sec, 2.0)
        self.assertFalse(result.timed_out)
        guard.finish.assert_called_once()
        proc.poll.assert_not_called()
        proc.wait.assert_not_called()

    def test_smt_timeout_kill_uses_guard_and_keeps_wait4_accounting(self):
        for breached in (False, True):
            with self.subTest(breached=breached):
                proc, guard = self.model(returncode=None)
                guard.breached = breached
                usage = types.SimpleNamespace(ru_utime=0.2, ru_stime=0.3)
                with self.smt_model(proc, guard, [(0, 0, None), (4242, signal.SIGKILL, usage)]), \
                     mock.patch.object(smtcomp_harness, "GRACE_SEC", 0), \
                     mock.patch.object(smtcomp_harness.time, "monotonic", side_effect=[0, 6, 7]), \
                     mock.patch.object(smtcomp_harness.time, "sleep"), \
                     mock.patch.object(smtcomp_harness.os, "killpg") as raw_kill:
                    result = self.invoke_smt()
                guard.terminate_if_authenticated.assert_called_once()
                guard.finish.assert_called_once()
                raw_kill.assert_not_called()
                self.assertEqual(result.cpu_sec, 0.5)
                self.assertEqual(result.exit_code, -signal.SIGKILL)
                self.assertEqual(result.memout, breached)
                self.assertEqual(result.timed_out, not breached)

    def test_smt_stolen_wait4_child_is_refused_not_fabricated_zero(self):
        proc, guard = self.model(returncode=None)
        with self.smt_model(proc, guard, ChildProcessError("already reaped")):
            with self.assertRaisesRegex(og.GuardEnforcementError, "wait4 lost its owned child"):
                self.invoke_smt()
        guard.finish.assert_called_once()

    def test_failed_spawn_keeps_oserror_result_and_guard_refusal_distinct(self):
        for lane in ("solver", "checker", "smt"):
            module = smtcomp_harness if lane == "smt" else pbcomp_harness
            with self.subTest(lane=lane):
                with mock.patch.object(module, "guarded_popen", side_effect=OSError("missing executable")):
                    result = self.invoke_smt() if lane == "smt" else self.invoke_pb(lane)
                if lane == "solver":
                    self.assertEqual(result.status, "ERROR")
                    self.assertIn("spawn:", result.note)
                elif lane == "checker":
                    self.assertEqual(result, (False, None, "ay verify spawn failed: missing executable"))
                else:
                    self.assertEqual(result.spawn_error, "missing executable")
                with mock.patch.object(module, "guarded_popen",
                                       side_effect=og.GuardEnforcementError("attach refused")):
                    with self.assertRaisesRegex(og.GuardEnforcementError, "attach refused"):
                        self.invoke_smt() if lane == "smt" else self.invoke_pb(lane)

    def test_all_three_callers_reap_real_post_leader_descendants(self):
        # Tiny Python subjects only, run sequentially. The real planner caps
        # their explicit zero-grace group budget; no solver/compiler is used.
        plan = plan_detected_host_with_scratch_lease(self, "legacy-caller-descendant-test")
        limit = min(256, plan.memlimit_mb)
        self.assertGreaterEqual(limit, 256)
        self.assertEqual(plan.jobs, 1)
        for lane in ("solver", "checker", "smt"):
            with self.subTest(lane=lane), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                ready = root / "descendant-ready"
                pidfile = root / "descendant-pid"
                script = root / "child.py"
                child_code = (
                    "import pathlib,time; "
                    f"pathlib.Path({str(ready)!r}).write_text('ready'); "
                    "time.sleep(30)"
                )
                script.write_text(
                    f"#!{sys.executable}\n"
                    "import pathlib,subprocess,sys,time\n"
                    f"p = subprocess.Popen([sys.executable, '-c', {child_code!r}])\n"
                    f"pathlib.Path({str(pidfile)!r}).write_text(str(p.pid))\n"
                    "deadline = time.monotonic() + 5\n"
                    f"while not pathlib.Path({str(ready)!r}).exists():\n"
                    "    if time.monotonic() >= deadline: raise RuntimeError('descendant did not start')\n"
                    "    time.sleep(0.01)\n"
                    "print('s UNKNOWN' if sys.argv[1:3] == ['pb', 'solve'] else 'computed=0', flush=True)\n"
                )
                script.chmod(0o755)
                captured = []

                def spawn(*args, **kwargs):
                    pair = og.guarded_popen(*args, **kwargs)
                    captured.append(pair)
                    return pair

                module = smtcomp_harness if lane == "smt" else pbcomp_harness
                with mock.patch.object(module, "guarded_popen", side_effect=spawn):
                    if lane == "solver":
                        result = pbcomp_harness.run_one(str(script), root / "unused.opb", 5,
                                                       "python", memlimit_mb=limit, nbcore=1)
                        self.assertEqual(result.status, "UNKNOWN")
                    elif lane == "checker":
                        result = pbcomp_harness.check_solution_via_ay(
                            str(script), root / "unused.opb", None, ["x1"], {}, limit,
                        )
                        self.assertEqual(result, (True, 0, ""))
                    else:
                        result = smtcomp_harness.run_process(
                            smtcomp_harness.Invocation([str(script)]), timeout_s=5, memlimit_mb=limit,
                        )
                        self.assertEqual(result.exit_code, 0)
                        self.assertIsNotNone(result.cpu_sec)
                self.assertTrue(ready.is_file())
                self.assertGreater(int(pidfile.read_text()), 0)
                self.assertEqual(len(captured), 1)
                proc, guard = captured[0]
                evidence = guard.evidence()
                self.assertEqual(evidence["phase"], "reaped")
                self.assertFalse(evidence["identity_lost"])
                self.assertIsNone(evidence["worker_error"])
                self.assertEqual(evidence["kill_threshold_mib"], limit)
                self.assertFalse(og._process_group_exists(proc.pid), evidence)


class WatchServerCommandReaderTest(unittest.TestCase):
    """Use real buffered pipes: BytesIO cannot expose fd/read-ahead bugs."""

    @contextlib.contextmanager
    def reader(self, initial=b""):
        read_fd, write_fd = os.pipe()
        source = os.fdopen(read_fd, "rb")
        writer = [write_fd]
        closing = threading.Event()
        consumed = threading.Event()
        lines = queue.Queue()
        errors = []
        real_read = os.read

        def observe_read(fd, count):
            data = real_read(fd, count)
            if fd == read_fd and data:
                consumed.set()
            return data

        def close_writer():
            if writer[0] is not None:
                os.close(writer[0])
                writer[0] = None

        def collect():
            try:
                for line in og._watch_server_command_lines(source, closing):
                    lines.put(line)
            except BaseException as error:
                errors.append(error)

        worker = threading.Thread(target=collect, daemon=True)
        with mock.patch.object(og.os, "read", side_effect=observe_read):
            try:
                if initial:
                    self.assertEqual(os.write(write_fd, initial), len(initial))
                worker.start()
                yield types.SimpleNamespace(
                    writer=write_fd, close_writer=close_writer, closing=closing,
                    consumed=consumed, lines=lines, worker=worker, errors=errors,
                )
            finally:
                # Release even an old buffered readline on assertion failure.
                # Tests assert cancellation BEFORE this EOF-producing cleanup.
                closing.set()
                close_writer()
                if worker.ident is not None:
                    worker.join(timeout=3)
                if not worker.is_alive():
                    source.close()
                self.assertFalse(worker.is_alive(), "reader survived cleanup EOF")
        self.assertEqual(errors, [])

    def test_coalesced_lines_arrive_before_another_write_or_eof(self):
        with self.reader(b"first\nsecond\n") as reader:
            self.assertEqual(reader.lines.get(timeout=2), b"first\n")
            self.assertEqual(reader.lines.get(timeout=2), b"second\n")
            self.assertTrue(reader.worker.is_alive())
            self.assertTrue(reader.lines.empty())

    def test_partial_input_cancels_before_writer_closes(self):
        with self.reader(b"WATCH") as reader:
            self.assertTrue(reader.consumed.wait(2), "partial input was never read")
            reader.closing.set()
            reader.worker.join(timeout=1)
            self.assertFalse(reader.worker.is_alive(), "partial readline ignored cancellation")
            self.assertTrue(reader.lines.empty())

    def test_quiet_input_cancels_before_writer_closes(self):
        with self.reader() as reader:
            reader.closing.set()
            reader.worker.join(timeout=1)
            self.assertFalse(reader.worker.is_alive())
            self.assertTrue(reader.lines.empty())

    def test_fragmented_lines_preserve_bytes(self):
        with self.reader(b"fir") as reader:
            self.assertTrue(reader.consumed.wait(2))
            with self.assertRaises(queue.Empty):
                reader.lines.get(timeout=0.05)
            os.write(reader.writer, b"st\nsec")
            self.assertEqual(reader.lines.get(timeout=2), b"first\n")
            os.write(reader.writer, b"ond\n")
            self.assertEqual(reader.lines.get(timeout=2), b"second\n")

    def test_maximum_line_preserves_following_command(self):
        maximum = b"x" * (og.WATCH_SERVER_MAX_COMMAND_BYTES - 1) + b"\n"
        with self.reader(maximum + b"next\n") as reader:
            self.assertEqual(reader.lines.get(timeout=2), maximum)
            self.assertEqual(reader.lines.get(timeout=2), b"next\n")

    def test_overlong_unterminated_line_returns_without_eof(self):
        overlong = b"x" * (og.WATCH_SERVER_MAX_COMMAND_BYTES + 1)
        with self.reader(overlong) as reader:
            self.assertEqual(reader.lines.get(timeout=2), overlong)
            reader.worker.join(timeout=1)
            self.assertFalse(reader.worker.is_alive())
            self.assertTrue(reader.lines.empty())

    def test_partial_eof_preserves_tail_for_protocol_refusal(self):
        with self.reader(b"WATCH") as reader:
            reader.close_writer()
            self.assertEqual(reader.lines.get(timeout=2), b"WATCH")
            self.assertEqual(reader.lines.get(timeout=2), b"")
            reader.worker.join(timeout=1)
            self.assertFalse(reader.worker.is_alive())

    def test_complete_eof_drains_all_lines(self):
        with self.reader(b"first\nsecond\n") as reader:
            reader.close_writer()
            self.assertEqual([reader.lines.get(timeout=2) for _ in range(3)],
                             [b"first\n", b"second\n", b""])

    def test_empty_eof_is_reported(self):
        with self.reader() as reader:
            reader.close_writer()
            self.assertEqual(reader.lines.get(timeout=2), b"")

    def test_finite_bytesio_fallback_preserves_lines_and_cancellation(self):
        closing = threading.Event()
        self.assertEqual(
            list(og._watch_server_command_lines(io.BytesIO(b"first\nsecond\n"), closing)),
            [b"first\n", b"second\n", b""],
        )
        closing.set()
        self.assertEqual(list(og._watch_server_command_lines(io.BytesIO(b"unread\n"), closing)), [])

    def assert_server_io_failure(self, operation):
        read_fd, write_fd = os.pipe()
        source = os.fdopen(read_fd, "rb")
        force_output_failure = threading.Event()
        errors = []

        class Output(io.BytesIO):
            def write(self, data):
                if force_output_failure.is_set():
                    raise BrokenPipeError("test teardown")
                return super().write(data)

        output = Output()
        error = OSError("injected command " + operation + " failure")

        def serve():
            try:
                og.serve_watchdog_requests(source, output)
            except BaseException as failure:
                errors.append(failure)

        module = og.select if operation == "select" else og.os
        worker = threading.Thread(target=serve, daemon=True)
        with mock.patch.object(module, operation, side_effect=error):
            try:
                os.write(write_fd, b"WATCH")
                worker.start()
                worker.join(timeout=2)
                self.assertFalse(worker.is_alive(), "server hid reader failure behind heartbeats")
                self.assertEqual(errors, [error])
                self.assertTrue(output.getvalue().startswith(og.WATCH_SERVER_READY))
            finally:
                # A regressed server can still be stopped by heartbeat output
                # failure, so a failing assertion does not leak its threads.
                force_output_failure.set()
                os.close(write_fd)
                if worker.ident is not None:
                    worker.join(timeout=3)
                if not worker.is_alive():
                    source.close()
                self.assertFalse(worker.is_alive(), "server survived test cleanup")

    def test_server_propagates_select_failure(self):
        self.assert_server_io_failure("select")

    def test_server_propagates_read_failure(self):
        self.assert_server_io_failure("read")


NORMAL = {"source": "fake", "raw": 1, "state": "normal"}
CRITICAL = {"source": "fake", "raw": 4, "state": "critical"}
# A 128 GiB host: margin max(16384, ceil(0.12 * 131072) = 15729) = 16384 MiB.
HOST_MB = 131072


def fake_window(*available, pressure=NORMAL):
    return [{"index": i, "t_unix": 0.0, "t_offset_s": 15.0 * i, "available_mb": value,
             "pressure": pressure} for i, value in enumerate(available)]


# vm_stat output in the shape this host prints (16 KiB pages). Every row is a
# whole number of MiB (a multiple of 64 pages) and no two rows are equal, so
# adding any row to the formula, or dropping one, moves the answer.
VM_STAT_MIB = {
    "Pages free": 15625, "Pages active": 30000, "Pages inactive": 4700,
    "Pages speculative": 625, "Pages throttled": 3, "Pages wired down": 5000,
    "Pages purgeable": 91, "Pages purged": 280, "File-backed pages": 39000,
    "Anonymous pages": 27000, "Pages stored in compressor": 1800,
    "Pages occupied by compressor": 700,
}
VM_STAT_TEXT = "Mach Virtual Memory Statistics: (page size of 16384 bytes)\n" + "".join(
    f"{key + ':':<40}{mib * 64:>14}.\n" for key, mib in VM_STAT_MIB.items()
) + '"Translation faults":                    68532362807.\nPageouts:      6371.\n'

# sysctlbyname(3): int sysctlbyname(const char *name, void *oldp, size_t *oldlenp,
#                                   void *newp, size_t newlen);
SYSCTLBYNAME = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.c_char_p, ctypes.POINTER(ctypes.c_uint32),
                                ctypes.POINTER(ctypes.c_size_t), ctypes.c_void_p, ctypes.c_size_t)


def fake_sysctlbyname(value, rc=0, size=None):
    """A sysctlbyname stand-in that answers ``value`` (and ``size``) with ``rc``."""
    calls = []

    def call(name, oldp, oldlenp, newp, newlen):
        calls.append((name, oldlenp[0], newp, newlen))
        if rc == 0:
            oldp[0] = value
            if size is not None:
                oldlenp[0] = size
        return rc

    return SYSCTLBYNAME(call), calls


class AvailableMemoryProbeTest(unittest.TestCase):
    """The figure admission compares against the envelope, pinned to its formula."""

    def darwin_available(self, **vm_stat):
        with mock.patch.object(og.sys, "platform", "darwin"), \
                mock.patch.object(og.subprocess, "check_output", **vm_stat) as run:
            return og.host_available_ram_reading(), run

    def test_darwin_available_is_free_speculative_inactive_purgeable_only(self):
        available, run = self.darwin_available(return_value=VM_STAT_TEXT)
        self.assertEqual(run.call_args.args[0], ["vm_stat"])
        # Active pages (excluded on purpose: the docstring says why), wired,
        # throttled and compressor pages never count as room; the 16 KiB page
        # size comes from the header, not the 4 KiB default.
        self.assertEqual(available, 15625 + 625 + 4700 + 91)

    def test_darwin_available_is_none_when_vm_stat_fails_or_has_no_rows(self):
        for vm_stat in (dict(side_effect=subprocess.CalledProcessError(1, ["vm_stat"])),
                        dict(side_effect=FileNotFoundError("vm_stat")),
                        dict(side_effect=subprocess.TimeoutExpired(["vm_stat"], 30)),
                        dict(return_value="Mach Virtual Memory Statistics: "
                                          "(page size of 16384 bytes)\n"),
                        dict(return_value="")):
            with self.subTest(vm_stat=vm_stat):
                self.assertIsNone(self.darwin_available(**vm_stat)[0])
                with mock.patch.object(og.sys, "platform", "darwin"), \
                        mock.patch.object(og.subprocess, "check_output", **vm_stat):
                    # The planner's soft clamp reads unknown as 0 (no clamp).
                    self.assertEqual(og.host_available_ram_mb(), 0)

    def test_linux_available_is_memavailable_and_none_without_it(self):
        meminfo = ("MemTotal:       134217728 kB\nMemFree:          1048576 kB\n"
                   "MemAvailable:    50331648 kB\nCached:         41943040 kB\n")
        for text, expected in ((meminfo, 49152),
                               (meminfo.replace("MemAvailable", "MemAvail"), None)):
            with self.subTest(expected=expected), \
                    mock.patch.object(og.sys, "platform", "linux"), \
                    mock.patch.object(og, "open", create=True,
                                      return_value=io.StringIO(text)) as opened:
                self.assertEqual(og.host_available_ram_reading(), expected)
                self.assertEqual(opened.call_args.args[0], "/proc/meminfo")
        with mock.patch.object(og.sys, "platform", "linux"), \
                mock.patch.object(og, "open", create=True, side_effect=OSError("no proc")):
            self.assertIsNone(og.host_available_ram_reading())


class MeasuredRamAdmissionTest(unittest.TestCase):
    """admit_campaign: measured headroom, not "no compiler anywhere". Fakes only."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.lock = os.path.join(self.tmp.name, "lease.lock")
        self.sleeps = []

    def tearDown(self):
        og._release_harness_lease()
        self.tmp.cleanup()

    def admit(self, available, pressure=None, rss=40, builds=0, jobs=2, ram_mb=HOST_MB):
        readings = iter(available)
        pressures = iter(pressure or [NORMAL] * len(available))
        return og.admit_campaign(
            jobs, label="admission-test", ram_mb=ram_mb, cores=18,
            available_probe=lambda: next(readings), pressure_probe=lambda: next(pressures),
            rss_probe=lambda: rss, build_probe=lambda: builds,
            sleep=self.sleeps.append, _lock_path=self.lock)

    def assert_lease_free(self):
        self.assertIsNone(og._ACTIVE_HARNESS_LEASE)
        og.acquire_harness_lease("probe", _lock_path=self.lock)
        og._release_harness_lease()

    def test_busy_but_roomy_host_admits_with_compilers_running(self):
        # Five compiler/build processes are running and 60 GiB is free: the old
        # veto refused this host for hours; measured headroom admits it.
        plan, record = self.admit([61440, 60000, 62000], builds=5)
        self.assertEqual(record["decision"], "admit")
        self.assertEqual(record["active_build_processes"], 5)
        self.assertEqual(record["margin_mb"], 16384)
        # harness = peak RSS 40 + 2 jobs x 2 streams x 1 MiB of bounded capture
        self.assertEqual(record["harness_mb"], 44)
        # The enforced caps were sized into the measured room, and they fit.
        self.assertEqual(record["envelope_mb"], plan.jobs * plan.memlimit_mb + 44)
        self.assertLessEqual(record["envelope_mb"] + record["margin_mb"],
                             record["min_available_mb"])
        self.assertEqual(plan.jobs, 2)
        self.assertGreaterEqual(plan.memlimit_mb, 1024)
        self.assertIsNotNone(og._ACTIVE_HARNESS_LEASE)

    def test_tight_host_refuses_and_releases_the_lease(self):
        # 17 GiB free: after the 16 GiB peer margin and the harness, not one
        # 1 GiB child fits.
        with self.assertRaises(og.AdmissionRefused) as caught:
            self.admit([17408, 17408, 17408])
        record = caught.exception.record
        self.assertEqual(record["decision"], "refuse")
        self.assertIn("tight host", record["reason"])
        self.assert_lease_free()

    def test_tight_host_decision_counts_the_whole_enforced_envelope_and_margin(self):
        # 2 x 8192 MiB caps + 100 MiB harness + 16384 margin = 32868 > 32000.
        record = og.ram_admission_decision(fake_window(32000, 32000, 32000), 2, 8192, 100,
                                           HOST_MB)
        self.assertEqual(record["required_mb"], 32868)
        self.assertEqual(record["decision"], "refuse")
        self.assertIn("tight host", record["reason"])
        record = og.ram_admission_decision(fake_window(32868, 32868, 32868), 2, 8192, 100,
                                           HOST_MB)
        self.assertEqual(record["decision"], "admit")

    def test_margin_is_an_eighth_of_the_host_with_no_absolute_floor(self):
        # 128 GiB keeps the 16 GiB the policy was measured with (DR-12); every
        # other host gets the same share, rounded up, and nothing sized for one host.
        self.assertEqual(og.admission_margin_mb(HOST_MB), 16384)
        self.assertEqual(og.admission_margin_mb(262144), 32768)
        self.assertEqual(og.admission_margin_mb(24576), 3072)
        self.assertEqual(og.admission_margin_mb(24577), 3073)
        self.assertEqual(og.admission_margin_mb(8192), 1024)
        for bad in (0, -1):
            with self.assertRaises(ValueError):
                og.admission_margin_mb(bad)

    # The three readings of one refused try on a 14-core, 24 GiB host, from the
    # 2026-10-14 landing log (try 1 of 36 consecutive COULD NOT RUN; pressure
    # normal throughout).
    SMALL_HOST_MB = 24576
    SMALL_HOST_WINDOW = [10370, 10732, 15888]

    def test_small_host_admits_into_the_room_it_measured(self):
        plan, record = self.admit(self.SMALL_HOST_WINDOW, builds=4, ram_mb=self.SMALL_HOST_MB)
        self.assertEqual(record["decision"], "admit")
        self.assertEqual(record["margin_mb"], 3072)
        self.assertEqual(record["min_available_mb"], 10370)
        # Never oversubscribed: the enforced envelope plus the margin fits the
        # minimum reading, and each child keeps at least the floor.
        self.assertLessEqual(plan.jobs * plan.memlimit_mb + record["harness_mb"]
                             + record["margin_mb"], record["min_available_mb"])
        self.assertEqual(record["required_mb"],
                         plan.jobs * plan.memlimit_mb + record["harness_mb"] + 3072)
        self.assertGreaterEqual(plan.memlimit_mb, 1024)
        self.assertEqual(plan.jobs, 2)

    def test_small_host_refused_under_the_old_floor(self):
        # The mutant: the 16 GiB floor sized for a 128 GiB host. On the same
        # readings not one 1 GiB child fits, which is the starvation DR-43 ends.
        def old_rule(physical_mb):
            return max(16 * 1024, -(-12 * int(physical_mb) // 100))
        with mock.patch.object(og, "admission_margin_mb", side_effect=old_rule), \
                self.assertRaises(og.AdmissionRefused) as caught:
            self.admit(self.SMALL_HOST_WINDOW, ram_mb=self.SMALL_HOST_MB)
        self.assertIn("tight host", caught.exception.record["reason"])
        self.assert_lease_free()

    def test_small_host_still_refuses_when_one_child_does_not_fit(self):
        # 3072 margin + 44 harness + one 1024 floor child = 4140 MiB.
        with self.assertRaises(og.AdmissionRefused) as caught:
            self.admit([4139, 9000, 9000], ram_mb=self.SMALL_HOST_MB)
        self.assertIn("tight host", caught.exception.record["reason"])
        self.assert_lease_free()
        plan, record = self.admit([4140, 9000, 9000], ram_mb=self.SMALL_HOST_MB)
        self.assertEqual(record["decision"], "admit")
        self.assertEqual((plan.jobs, plan.memlimit_mb), (1, 1024))

    def test_unreadable_measurement_refuses(self):
        cases = (
            dict(available=[60000, None, 60000]),
            dict(available=[60000, 60000, 60000], pressure=[NORMAL, None, NORMAL]),
            dict(available=[60000, 60000, 60000], rss=None),
        )
        for case in cases:
            with self.subTest(case=case):
                self.sleeps.clear()
                with self.assertRaises(og.AdmissionRefused) as caught:
                    self.admit(**case)
                self.assertIn("cannot measure", caught.exception.record["reason"])
                self.assertEqual(caught.exception.record["decision"], "refuse")
                self.assert_lease_free()
        # A probe that raises is unmeasurable too, never "free".
        record = og.ram_admission_decision(
            og.sample_admission_window(1, 0, lambda: 1 / 0, lambda: NORMAL, sleep=None),
            2, 1024, 10, HOST_MB)
        self.assertEqual(record["decision"], "refuse")

    def test_critical_pressure_at_admission_refuses(self):
        with self.assertRaises(og.AdmissionRefused) as caught:
            self.admit([90000, 90000, 90000], pressure=[NORMAL, CRITICAL, NORMAL])
        self.assertIn("critical", caught.exception.record["reason"])

    def test_window_takes_the_minimum_of_its_samples(self):
        # The dip in the middle decides: first, last or max would all admit.
        envelope = dict(jobs=2, memlimit_mb=10000, harness_mb=100, physical_mb=HOST_MB)
        record = og.ram_admission_decision(fake_window(90000, 30000, 80000), **envelope)
        self.assertEqual(record["min_available_mb"], 30000)
        self.assertEqual(record["decision"], "refuse")
        # The window itself: three readings, two 15 s waits (~30 s), all recorded.
        values = iter([90000, 30000, 80000])
        window = og.sample_admission_window(available_probe=lambda: next(values),
                                            pressure_probe=lambda: NORMAL,
                                            sleep=self.sleeps.append)
        self.assertEqual([row["available_mb"] for row in window], [90000, 30000, 80000])
        self.assertEqual(self.sleeps, [15.0, 15.0])
        # And the planner sizes the caps from the minimum, not a lucky reading.
        plan, record = self.admit([90000, 30000, 80000])
        self.assertEqual(record["min_available_mb"], 30000)
        self.assertLessEqual(plan.jobs * plan.memlimit_mb, 30000 - 16384 - 44)

    def test_admission_record_lists_every_sample_envelope_margin_and_decision(self):
        _plan, record = self.admit([61440, 60000, 62000], builds=3)
        text = "\n".join(og.format_admission(record))
        for needle in ("admission: ADMIT", "sample 0", "sample 1", "sample 2", "envelope",
                       "margin 16384 MiB", "active build processes: 3 (recorded, not a veto)"):
            self.assertIn(needle, text)
        json.dumps(record)  # it goes into the run's record as JSON


class LandingBuildPlanTest(unittest.TestCase):
    """A landing's cargo job count fits the room measured now (DR-44). Pure."""

    def test_the_measured_small_host_gets_the_jobs_that_fit(self) -> None:
        # Two readings on the 24 GiB host on 2026-10-14, less the 3072 MiB
        # margin, at 9216 MiB per 14 jobs (658 MiB a job).
        plan = og.landing_build_plan(10370, 24576, 14)
        self.assertEqual((plan["margin_mb"], plan["room_mb"], plan["jobs"]), (3072, 7298, 11))
        self.assertEqual(og.landing_build_plan(9550, 24576, 14)["jobs"], 9)

    def test_a_roomy_host_is_bounded_by_its_cores(self) -> None:
        self.assertEqual(og.landing_build_plan(61440, HOST_MB, 18)["jobs"], 18)
        self.assertEqual(og.landing_build_plan(12288 + 3072, 24576, 14)["jobs"], 14)

    def test_no_room_or_no_reading_is_one_job_never_a_refusal(self) -> None:
        for available, physical, cores in ((1000, 24576, 14), (3500, 24576, 14), (None, 24576, 14),
                                           (9000, 0, 14), (9000, 24576, 0)):
            with self.subTest(available=available, physical=physical, cores=cores):
                self.assertEqual(og.landing_build_plan(available, physical, cores)["jobs"], 1)

    def test_never_oversubscribed_over_a_grid(self) -> None:
        for physical in (8192, 24576, HOST_MB, 262144):
            for available in range(0, physical + 1, max(1, physical // 37)):
                for cores in (1, 4, 14, 64):
                    for peak, jobs_at in ((og.BUILD_PEAK_MB, og.BUILD_PEAK_JOBS), (4096, 8), (512, 1)):
                        plan = og.landing_build_plan(available, physical, cores, peak, jobs_at)
                        jobs = plan["jobs"]
                        self.assertTrue(1 <= jobs <= cores, plan)
                        if jobs > 1:
                            self.assertLessEqual(jobs * peak, (available - og.admission_margin_mb(physical)) * jobs_at,
                                                 plan)

    def test_an_oversubscribing_plan_is_caught(self) -> None:
        # The mutant: a job per core, whatever the room holds.
        original = og.landing_build_plan

        def per_core(available_mb=None, physical_mb=None, cores=None, peak_mb=og.BUILD_PEAK_MB,
                     peak_jobs=og.BUILD_PEAK_JOBS):
            plan = dict(original(available_mb, physical_mb, cores, peak_mb, peak_jobs))
            plan["jobs"] = cores or 1
            return plan
        with mock.patch.object(og, "landing_build_plan", side_effect=per_core):
            result = unittest.TestResult()
            unittest.TestSuite([LandingBuildPlanTest("test_never_oversubscribed_over_a_grid"),
                                LandingBuildPlanTest("test_the_measured_small_host_gets_the_jobs_that_fit")]).run(result)
        self.assertTrue(result.failures, "a plan of one job per core must fail the room check")

    def test_a_caller_s_job_count_bounds_the_plan(self) -> None:
        # build-slot (or the lander) sets CARGO_BUILD_JOBS to its share of the
        # machine; the landing never plans above it, and never below the room.
        roomy = og.landing_build_plan(16358, 24576, 14)
        self.assertEqual(roomy["jobs"], 14)
        bounded = og.landing_build_plan(16358, 24576, 14, cap=4)
        self.assertEqual(bounded["jobs"], 4)
        self.assertIn("at most the caller's 4", bounded["why"])
        self.assertEqual(og.landing_build_plan(9550, 24576, 14, cap=12)["jobs"], 9, "the room still governs")
        for cap in (None, 0, -3):
            self.assertEqual(og.landing_build_plan(16358, 24576, 14, cap=cap)["jobs"], 14, cap)

    def test_land_sh_bounds_every_round_by_what_its_caller_set(self) -> None:
        scripts = Path(og.__file__).resolve().parent
        for script in ("land.sh",):
            text = (scripts / script).read_text(encoding="utf-8")
            self.assertIn("capture_build_cap", text,
                          f"{script} distinguishes generated allocations from caller caps")
        land = (scripts / "land.sh").read_text(encoding="utf-8").splitlines()
        start = land.index("plan_builds() {")
        body = "\n".join(land[start:land.index("}", start) + 1])
        with tempfile.TemporaryDirectory() as out:
            for caller, most in (("2", 2), ("", os.cpu_count())):
                done = subprocess.run(
                    ["/bin/bash", "-c", body + '\nnote() { printf "%s\\n" "$*"; }\nplan_builds\n'
                     'printf "jobs=%s\\n" "$CARGO_BUILD_JOBS"'],
                    cwd=scripts.parent, capture_output=True, text=True, timeout=60, check=False,
                    env={**os.environ, "OUT": out, "LAND_CALLER_JOBS": caller, "CARGO_BUILD_JOBS": "99"})
                with self.subTest(caller=caller):
                    self.assertEqual(done.returncode, 0, done.stderr)
                    jobs = int(done.stdout.split("jobs=")[-1])
                    self.assertTrue(1 <= jobs <= most, done.stdout)

    def test_generated_budget_does_not_become_an_explicit_cap(self) -> None:
        land = (Path(og.__file__).resolve().parent / "land.sh").read_text().splitlines()
        start = land.index("capture_build_cap() {")
        body = "\n".join(land[start:land.index("}", start) + 1])
        cases = [
            ({"CARGO_BUILD_JOBS": "14"}, "14"),
            ({"CARGO_BUILD_JOBS": "14", "TARGO_PLANNED_JOBS": "14"}, ""),
            ({"CARGO_BUILD_JOBS": "4", "TARGO_PLANNED_JOBS": "14"}, "4"),
            ({"CARGO_BUILD_JOBS": "14", "BUILD_SLOT_CPU_SOURCE": "available-slots",
              "BUILD_SLOT_CPU_BUDGET": "14"}, ""),
            ({"CARGO_BUILD_JOBS": "14", "TARGO_PLANNED_JOBS": "14",
              "TARGO_CALLER_JOBS": "3"}, "3"),
        ]
        clean = {k: v for k, v in os.environ.items()
                 if k not in {"LAND_CALLER_JOBS", "CARGO_BUILD_JOBS", "TARGO_CALLER_JOBS",
                              "TARGO_PLANNED_JOBS", "BUILD_SLOT_CPU_SOURCE", "BUILD_SLOT_CPU_BUDGET"}}
        for extra, expected in cases:
            with self.subTest(extra=extra):
                done = subprocess.run(
                    ["/bin/bash", "-c", body + '\ncapture_build_cap\n'
                     'printf "%s:%s" "$LAND_CALLER_JOBS" "${TARGO_CALLER_JOBS-}"'],
                    env={**clean, **extra}, capture_output=True, text=True, check=True)
                self.assertEqual(done.stdout, expected + ":" + expected)

    def test_the_cli_prints_the_plan_a_landing_evals(self) -> None:
        done = subprocess.run([sys.executable, str(Path(og.__file__)), "landing-plan"], capture_output=True,
                              text=True, timeout=60, check=False)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertRegex(done.stdout, r"(?m)^LAND_BUILD_JOBS=[1-9][0-9]*$")
        memory = dict(line.split("=", 1) for line in done.stdout.splitlines()
                      if line.startswith(("LAND_JOB_MEMORY_BYTES=", "LAND_MEMORY_RESERVE_BYTES=")))
        self.assertEqual(int(memory["LAND_JOB_MEMORY_BYTES"]),
                         (og.BUILD_PEAK_MB * 1048576 + og.BUILD_PEAK_JOBS - 1) // og.BUILD_PEAK_JOBS)
        if og.physical_ram_mb():
            self.assertEqual(int(memory["LAND_MEMORY_RESERVE_BYTES"]),
                             og.admission_margin_mb(og.physical_ram_mb()) * 1048576)
        self.assertRegex(done.stdout, r"(?m)^LAND_HOST_PLAN='cores \d+ ram \d+ MiB available .* build jobs \d+ = .*'$")
        done = subprocess.run([sys.executable, str(Path(og.__file__)), "landing-plan", "--cap", "1"],
                              capture_output=True, text=True, timeout=60, check=False)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertRegex(done.stdout, r"(?m)^LAND_BUILD_JOBS=1$")


class MemoryPressureWatchTest(unittest.TestCase):
    """Pressure going critical mid-run stops the children; nothing real is pressured."""

    def run_stopped_child(self, script, grace_s):
        with tempfile.TemporaryDirectory() as td:
            ready = Path(td, "ready")
            marker = Path(td, "terminated")
            cancel = threading.Event()
            # Critical only once the child is up and has installed its handler.
            watch = og.MemoryPressureWatch(
                label="pressure-test", probe=lambda: CRITICAL if ready.exists() else NORMAL,
                poll_s=0.05, on_critical=cancel.set, trace_path=os.path.join(td, "trace.jsonl"))
            watch.start()
            try:
                result = og.run_captured(
                    ["/bin/sh", "-c", script.format(ready=ready, marker=marker)], 10000,
                    timeout_s=20, label="pressure-test", cancel_event=cancel,
                    terminate_grace_s=grace_s)
            finally:
                summary = watch.stop()
            trace = [json.loads(line) for line in Path(td, "trace.jsonl").read_text().splitlines()]
            return result, watch, summary, trace, marker.exists()

    def test_critical_pressure_mid_run_terminates_children_and_trips(self):
        result, watch, summary, trace, terminated = self.run_stopped_child(
            'trap "echo term > {marker}; exit 143" TERM; : > {ready}; '
            'while :; do sleep 0.05; done', grace_s=5.0)
        self.assertTrue(watch.tripped)
        self.assertIn("critical", watch.trip_reason)
        self.assertTrue(summary["tripped"])
        self.assertTrue(result.cancelled)
        self.assertFalse(result.timed_out)
        self.assertTrue(terminated, "the child never saw SIGTERM")
        kinds = [event["kind"] for event in result.guard_evidence["events"]]
        self.assertIn("authenticated-terminate", kinds)
        self.assertIn("group-reaped", kinds)
        self.assertEqual(result.guard_evidence["phase"], "reaped")
        self.assertLess(result.wall_sec, 15)
        states = [row["pressure"]["state"] for row in trace]
        self.assertEqual(states[0], "normal")
        self.assertIn("critical", states)

    def test_child_ignoring_sigterm_is_killed_after_the_grace(self):
        result, watch, _summary, _trace, terminated = self.run_stopped_child(
            'trap "" TERM; : > {ready}; while :; do sleep 0.05; done', grace_s=0.5)
        self.assertTrue(watch.tripped)
        self.assertTrue(result.cancelled)
        self.assertFalse(terminated)
        kinds = [event["kind"] for event in result.guard_evidence["events"]]
        self.assertIn("authenticated-terminate", kinds)
        self.assertIn("authenticated-kill", kinds)
        self.assertEqual(result.guard_evidence["phase"], "reaped")
        self.assertGreaterEqual(result.wall_sec, 0.5)

    def test_unmeasurable_pressure_mid_run_fails_closed(self):
        readings = iter([NORMAL, NORMAL])
        cancel = threading.Event()
        watch = og.MemoryPressureWatch(label="pressure-test", probe=lambda: next(readings, None),
                                       poll_s=0.01, on_critical=cancel.set, max_unknown=3)
        with watch:
            self.assertTrue(cancel.wait(10))
        self.assertTrue(watch.tripped)
        self.assertIn("unmeasurable for 3", watch.trip_reason)
        self.assertEqual(watch.summary()["counts"]["normal"], 2)

    def test_normal_and_warn_pressure_never_trip(self):
        readings = iter([NORMAL, dict(NORMAL, raw=2, state="warn")] * 10)
        cancel = threading.Event()
        watch = og.MemoryPressureWatch(label="pressure-test", probe=lambda: next(readings, NORMAL),
                                       poll_s=0.01, on_critical=cancel.set)
        with watch:
            time.sleep(0.3)
        self.assertFalse(watch.tripped)
        self.assertFalse(cancel.is_set())
        self.assertGreater(watch.summary()["polls"], 5)

    def test_darwin_levels_follow_the_kernel_constants(self):
        # NOTE_MEMORYSTATUS_PRESSURE_{NORMAL,WARN,CRITICAL} = 0x1, 0x2, 0x4.
        for raw, state in ((1, "normal"), (2, "warn"), (4, "critical"), (0, None), (3, None)):
            with self.subTest(raw=raw), \
                    mock.patch.object(og.sys, "platform", "darwin"), \
                    mock.patch.object(og, "_darwin_pressure_raw", return_value=raw):
                reading = og.memory_pressure_reading()
                self.assertEqual(reading and reading["state"], state)

    def test_linux_psi_full_avg10_is_critical_from_sixty_percent(self):
        def psi(full):
            return io.StringIO("some avg10=70.00 avg60=1.00 avg300=0.50 total=9\n"
                               f"full avg10={full} avg60=0.00 avg300=0.00 total=1\n")

        for full, state in (("59.99", "normal"), ("60.00", "critical"), ("0.00", "normal")):
            with self.subTest(full=full), \
                    mock.patch.object(og.sys, "platform", "linux"), \
                    mock.patch("builtins.open", return_value=psi(full)):
                self.assertEqual(og.memory_pressure_reading()["state"], state)
        with mock.patch.object(og.sys, "platform", "linux"), \
                mock.patch("builtins.open", side_effect=OSError("no PSI")):
            self.assertIsNone(og.memory_pressure_reading())
        # A file without the `full` line (or with an unreadable one) is no
        # reading at all, never "normal".
        for text in ("some avg10=70.00 avg60=1.00 avg300=0.50 total=9\n",
                     "some avg10=0.00 avg60=0.00 avg300=0.00 total=9\nfull avg10=n/a\n"):
            with self.subTest(text=text), \
                    mock.patch.object(og.sys, "platform", "linux"), \
                    mock.patch.object(og, "open", create=True, return_value=io.StringIO(text)):
                self.assertIsNone(og.memory_pressure_reading())

    def test_darwin_probe_reads_the_level_through_sysctlbyname(self):
        # The kernel's answer, not a constant: each dispatch level comes back as
        # read, from one sysctlbyname call naming the sysctl, with no fork.
        # Select the guard's platform without changing stdlib sys.platform:
        # ctypes.util must still import the real host's native loader.
        for raw, state in ((1, "normal"), (2, "warn"), (4, "critical")):
            sysctlbyname, calls = fake_sysctlbyname(raw)
            with self.subTest(raw=raw), \
                    mock.patch.object(og, "sys", types.SimpleNamespace(platform="darwin")), \
                    mock.patch.object(og, "_DARWIN_SYSCTLBYNAME", [sysctlbyname]), \
                    mock.patch.object(og.subprocess, "run") as fallback:
                self.assertEqual(og.memory_pressure_reading(), {
                    "source": "sysctl kern.memorystatus_vm_pressure_level",
                    "raw": raw, "state": state})
                self.assertEqual(calls, [(b"kern.memorystatus_vm_pressure_level",
                                          ctypes.sizeof(ctypes.c_uint32), None, 0)])
                fallback.assert_not_called()
        if sys.platform == "darwin":
            # And the real call reads this kernel: a fresh libc binding, with the
            # fallback disabled, answers one of the three dispatch levels.
            with mock.patch.object(og, "_DARWIN_SYSCTLBYNAME", []), \
                    mock.patch.object(og.subprocess, "run",
                                      side_effect=OSError("fallback disabled")) as fallback:
                self.assertIn(og._darwin_pressure_raw(), og.DARWIN_PRESSURE_STATES)
                fallback.assert_not_called()

    def test_darwin_probe_falls_back_to_sysctl_and_otherwise_fails_closed(self):
        name = "kern.memorystatus_vm_pressure_level"
        sysctlbyname_failed = fake_sysctlbyname(0, rc=-1)[0]
        wrong_size = fake_sysctlbyname(4, size=8)[0]  # not the uint32 the kernel answers
        cases = (
            (sysctlbyname_failed, dict(return_value=subprocess.CompletedProcess(
                ["sysctl"], 0, stdout="4\n", stderr="")), 4),
            (wrong_size, dict(return_value=subprocess.CompletedProcess(
                ["sysctl"], 0, stdout="2\n", stderr="")), 2),
            (sysctlbyname_failed, dict(side_effect=subprocess.CalledProcessError(1, ["sysctl"])),
             None),
            (sysctlbyname_failed, dict(side_effect=subprocess.TimeoutExpired(["sysctl"], 5)),
             None),
            (wrong_size, dict(side_effect=FileNotFoundError("sysctl")), None),
            (sysctlbyname_failed, dict(return_value=subprocess.CompletedProcess(
                ["sysctl"], 0, stdout="", stderr="")), None),
        )
        for sysctlbyname, fallback_result, expected in cases:
            probe = mock.Mock(wraps=sysctlbyname)
            with self.subTest(fallback=fallback_result, expected=expected), \
                    mock.patch.object(og, "sys", types.SimpleNamespace(platform="darwin")), \
                    mock.patch.object(og, "_DARWIN_SYSCTLBYNAME", [probe]), \
                    mock.patch.object(og.subprocess, "run", **fallback_result) as fallback:
                self.assertEqual(og._darwin_pressure_raw(), expected)
                self.assertEqual(fallback.call_args.args[0], ["sysctl", "-n", name])
                reading = og.memory_pressure_reading()
                self.assertEqual(reading and reading["raw"], expected)
                self.assertEqual(probe.call_count, 2)
                self.assertEqual(fallback.call_count, 2)
        if sys.platform == "darwin":
            # The real fallback reads this kernel too.
            with mock.patch.object(og, "_DARWIN_SYSCTLBYNAME", [sysctlbyname_failed]):
                self.assertIn(og._darwin_pressure_raw(), og.DARWIN_PRESSURE_STATES)

    def test_watch_thread_failure_trips_instead_of_dying(self):
        # The trace disk fills after the first poll: the poll raises inside the
        # watch thread, which must stop the campaign, not leave it unwatched.
        class FullDisk(io.StringIO):
            writes = 0

            def write(self, text):
                self.writes += 1
                if self.writes > 1:
                    raise OSError(errno.ENOSPC, "No space left on device")
                return super().write(text)

        cancel = threading.Event()
        watch = og.MemoryPressureWatch(label="pressure-test", probe=lambda: NORMAL,
                                       poll_s=0.01, on_critical=cancel.set,
                                       trace_path="/nonexistent/pressure.jsonl")
        with mock.patch.object(og, "open", create=True, return_value=FullDisk()):
            watch.start()
        try:
            self.assertTrue(cancel.wait(10), "the watch thread died and nothing stopped the run")
        finally:
            summary = watch.stop()
        self.assertTrue(watch.tripped)
        self.assertTrue(summary["tripped"])
        self.assertIn("watch failed", watch.trip_reason)
        self.assertIn("No space left on device", watch.trip_reason)

    def test_default_probes_are_the_kernel_readings(self):
        # The gate passes no probes: the watch and the admission window must then
        # read the kernel functions, and an unmeasurable kernel refuses / trips.
        cancel = threading.Event()
        with mock.patch.object(og, "memory_pressure_reading", return_value=None) as pressure, \
                mock.patch.object(og, "host_available_ram_reading", return_value=None) as avail:
            watch = og.MemoryPressureWatch(label="pressure-test", poll_s=0.01,
                                           on_critical=cancel.set)
            with watch:
                self.assertTrue(cancel.wait(10))
            window = og.sample_admission_window(1, 0, sleep=None)
        self.assertIn("unmeasurable for 3", watch.trip_reason)
        # The watch's unmeasurable polls, then the window's one reading.
        self.assertGreaterEqual(pressure.call_count, og.PRESSURE_MAX_UNKNOWN + 1)
        avail.assert_called_once_with()
        self.assertEqual([(row["available_mb"], row["pressure"]) for row in window],
                         [(None, None)])
        self.assertEqual(og.ram_admission_decision(window, 2, 1024, 10, HOST_MB)["decision"],
                         "refuse")


if __name__ == "__main__":
    unittest.main()
