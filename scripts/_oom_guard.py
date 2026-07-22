# ay-script: oom-guard
"""OOM guard for the benchmark sweep harnesses.

Aggregate admission control for harness children: cap concurrency so N solver
processes cannot overcommit RAM, hand every child an explicit MEMLIMIT/NBCORE
budget, and refuse to start when a cargo build is running at the same time. WARNING:
unbounded concurrent sweeps and builds have overcommitted RAM to the point of
hard OOM / kernel watchdog panics — keep the budgets honest.

Pure stdlib, no third-party deps; automatic planning fails closed if RAM cannot
be detected.

Which solver actually enforces a planned envelope (verified against the crates):
  * `ay-pb pb solve` honors the MEMLIMIT env var (MiB) — apply_memory_limit in
    crates/ay-pb/src/bin/ay.rs:307, trips its guard at ~90% of the limit.
  * the main `ay` binary honors `--memory MB` on the solve path (incl. --chc);
    it does NOT read MEMLIMIT, and its `pb` subcommand (crates/ay/src/cmd_pb.rs)
    has no memory knob at all and sets NO process memory limit.
  * external solvers (roundingsat, kissat, golem, eld) have no envelope knob.
  * z3's `-memory:N` is NOT a bound (measured: silent overshoot well past the
    limit, exit 0 — z3 counts its own allocator's bytes, not footprint). Pass
    it for clean reporting if you like; never count it as enforcement.
For children with no honored envelope the plan alone is a false record: harnesses
must ALSO run `rss_watchdog(proc, memlimit_mb)`, or the printed envelope is not
enforced by anything. Note rss_watchdog is a SAMPLER and inherits a sampler's
limits — it cannot see a single huge mmap and it bounds nothing if the harness
itself dies; treat it as a backstop, not the primary bound.

Shell harnesses can consume the planner via the eval-able CLI:
    eval "$(python3 scripts/_oom_guard.py plan --jobs 8)"
    # sets PLAN_JOBS, PLAN_MEMLIMIT_MB, PLAN_NBCORE, PLAN_HEADROOM_MB
"""
import collections
import os
import re
import signal
import subprocess
import sys
import threading
import time


# Exit status used by the ``watch`` CLI when the attached process group crossed
# its RSS envelope.  Keep this distinct from conventional solver verdict exit
# codes (10/20) so native harnesses can persist ``memout`` rather than
# misclassifying the SIGKILL as a generic crash.
WATCHDOG_BREACH_EXIT = 86
WATCHDOG_TIMEOUT_EXIT = 124


def _host_physical_ram_mb():
    """Host physical RAM in MiB, ignoring container/cgroup ceilings."""
    try:  # macOS
        out = subprocess.check_output(["sysctl", "-n", "hw.memsize"], text=True,
                                      stderr=subprocess.DEVNULL)
        return int(out.strip()) // (1024 * 1024)
    except Exception:
        pass
    try:  # Linux / other POSIX
        return (os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES")) // (1024 * 1024)
    except Exception:
        return 0


CgroupMemory = collections.namedtuple("CgroupMemory", ["limit_mb", "current_mb"])


def _decode_mountinfo_path(value):
    """Decode the octal escapes used for mountinfo path fields."""
    return re.sub(
        r"\\([0-7]{3})",
        lambda match: chr(int(match.group(1), 8)),
        value,
    )


def _cgroup_memberships(cgroup_file):
    """Return (v2_path, {v1_controller: path}) from /proc/self/cgroup."""
    v2_path = None
    v1_paths = {}
    try:
        with open(cgroup_file) as fh:
            lines = list(fh)
    except OSError:
        return v2_path, v1_paths
    for raw in lines:
        parts = raw.rstrip("\n").split(":", 2)
        if len(parts) != 3:
            continue
        _, controllers, path = parts
        path = "/" + path.lstrip("/")
        if not controllers:
            v2_path = path
            continue
        for controller in controllers.split(","):
            if controller:
                v1_paths[controller] = path
    return v2_path, v1_paths


def _cgroup_mounts(mountinfo_file):
    """Parse cgroup v1/v2 mounts from /proc/self/mountinfo."""
    mounts = []
    try:
        with open(mountinfo_file) as fh:
            lines = list(fh)
    except OSError:
        return mounts
    for raw in lines:
        before, separator, after = raw.rstrip("\n").partition(" - ")
        if not separator:
            continue
        left = before.split()
        right = after.split()
        if len(left) < 6 or len(right) < 3:
            continue
        fs_type = right[0]
        if fs_type not in ("cgroup", "cgroup2"):
            continue
        controllers = set(right[2].split(",")) if fs_type == "cgroup" else set()
        mounts.append(
            {
                "type": fs_type,
                "root": _decode_mountinfo_path(left[3]),
                "mount": _decode_mountinfo_path(left[4]),
                "controllers": controllers,
            }
        )
    return mounts


def _mounted_cgroup_ancestors(mount, membership):
    """Map a hierarchy membership to its visible leaf and mount ancestors."""
    mountpoint = os.path.normpath(mount["mount"])
    mount_root = os.path.normpath(mount["root"])
    membership = os.path.normpath("/" + membership.lstrip("/"))
    if mount_root == "/":
        relative = membership.lstrip("/")
    elif membership == mount_root:
        relative = ""
    elif membership.startswith(mount_root.rstrip("/") + "/"):
        relative = membership[len(mount_root):].lstrip("/")
    else:
        # In a cgroup namespace /proc/self/cgroup can be relative to the
        # namespace while mountinfo's root reflects the underlying hierarchy.
        # The visible filesystem still maps membership below the mountpoint.
        relative = membership.lstrip("/")
    current = os.path.normpath(os.path.join(mountpoint, relative))
    ancestors = []
    while (mountpoint == "/" and current.startswith("/")) \
            or current == mountpoint or current.startswith(mountpoint + os.sep):
        ancestors.append(current)
        if current == mountpoint:
            break
        parent = os.path.dirname(current)
        if parent == current:
            break
        current = parent
    return ancestors


def _dynamic_cgroup_paths(controller, cgroup_file, mountinfo_file):
    """Visible leaf-to-root directories for one controller."""
    v2_path, v1_paths = _cgroup_memberships(cgroup_file)
    directories = []
    for mount in _cgroup_mounts(mountinfo_file):
        membership = None
        if mount["type"] == "cgroup2" and v2_path is not None:
            membership = v2_path
        elif mount["type"] == "cgroup" and controller in mount["controllers"]:
            membership = v1_paths.get(controller)
        if membership is not None:
            directories.extend(_mounted_cgroup_ancestors(mount, membership))
    # Preserve leaf-first ordering while eliminating combined-controller and
    # fallback duplicates.
    return list(dict.fromkeys(directories))


def _memory_candidates(cgroup_file, mountinfo_file, include_root_fallback):
    candidates = []
    for directory in _dynamic_cgroup_paths("memory", cgroup_file, mountinfo_file):
        candidates.extend([
            (os.path.join(directory, "memory.max"),
             os.path.join(directory, "memory.current")),
            (os.path.join(directory, "memory.limit_in_bytes"),
             os.path.join(directory, "memory.usage_in_bytes")),
        ])
    if include_root_fallback:
        candidates.extend([
            ("/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/memory.current"),
            ("/sys/fs/cgroup/memory/memory.limit_in_bytes",
             "/sys/fs/cgroup/memory/memory.usage_in_bytes"),
        ])
    return list(dict.fromkeys(candidates))


def cgroup_memory_mb(candidates=None, cgroup_file="/proc/self/cgroup",
                     mountinfo_file="/proc/self/mountinfo"):
    """Return the tightest finite cgroup memory limit/current pair in MiB.

    Resolves the process's nested membership through mountinfo for unified v2
    and v1, checking the leaf and every visible ancestor. The optional
    candidate pairs make filesystem behavior injectable in unit tests.
    Unlimited (`max` or kernel sentinel) and malformed controllers are ignored.
    """
    if candidates is None:
        candidates = _memory_candidates(
            cgroup_file,
            mountinfo_file,
            cgroup_file == "/proc/self/cgroup"
            and mountinfo_file == "/proc/self/mountinfo",
        )
    found = []
    for limit_path, current_path in candidates:
        try:
            with open(limit_path) as fh:
                raw_limit = fh.read().strip()
            if not raw_limit or raw_limit == "max":
                continue
            limit_bytes = int(raw_limit)
            # v1 uses a value near 2^63 as its unlimited sentinel.
            if limit_bytes <= 0 or limit_bytes >= (1 << 60):
                continue
            with open(current_path) as fh:
                current_bytes = max(0, int(fh.read().strip()))
            found.append(CgroupMemory(
                max(1, limit_bytes // (1024 * 1024)),
                current_bytes // (1024 * 1024),
            ))
        except (OSError, ValueError):
            continue
    # Parent usage matters even if the leaf has a smaller nominal limit: a
    # heavily used ancestor can leave less capacity for this process. Select
    # the controller with the tightest remaining headroom, then its limit.
    return min(
        found,
        key=lambda value: (value.limit_mb - value.current_mb, value.limit_mb),
    ) if found else None


def physical_ram_mb():
    """Effective physical RAM ceiling in MiB, including cgroup limits."""
    host_mb = _host_physical_ram_mb()
    cgroup = cgroup_memory_mb()
    if cgroup is None:
        return host_mb
    if not host_mb:
        return cgroup.limit_mb
    return min(host_mb, cgroup.limit_mb)


def _host_physical_core_count():
    """Host physical core count (not SMT threads).

    Used by multi-job harnesses to hand each concurrent solver process an
    honest NBCORE core budget, so N parallel-mode solvers (each sizing a worker
    pool from NBCORE / the machine) don't oversubscribe every core and turn
    wall-times into load noise.
    """
    try:  # macOS
        out = subprocess.check_output(["sysctl", "-n", "hw.physicalcpu"], text=True,
                                      stderr=subprocess.DEVNULL)
        n = int(out.strip())
        if n >= 1:
            return n
    except Exception:
        pass
    try:  # Linux: count unique (physical id, core id) pairs
        cores = set()
        phys = None
        with open("/proc/cpuinfo") as fh:
            for line in fh:
                if line.startswith("physical id"):
                    phys = line.split(":", 1)[1].strip()
                elif line.startswith("core id"):
                    cores.add((phys, line.split(":", 1)[1].strip()))
        if cores:
            return len(cores)
    except Exception:
        pass
    return os.cpu_count() or 1


def _parse_cpu_set(value):
    """Count CPUs in Linux cpuset syntax such as ``0-3,8,10-11``."""
    cpus = set()
    for raw_part in value.strip().split(","):
        part = raw_part.strip()
        if not part:
            continue
        try:
            if "-" in part:
                start, end = (int(piece) for piece in part.split("-", 1))
                if end < start:
                    return 0
                cpus.update(range(start, end + 1))
            else:
                cpus.add(int(part))
        except ValueError:
            return 0
    return len(cpus)


def _cpu_candidates(cgroup_file, mountinfo_file, include_root_fallback):
    cpuset_paths = []
    quota_pairs = []
    for directory in _dynamic_cgroup_paths("cpuset", cgroup_file, mountinfo_file):
        cpuset_paths.extend([
            os.path.join(directory, "cpuset.cpus.effective"),
            os.path.join(directory, "cpuset.cpus"),
        ])
    for directory in _dynamic_cgroup_paths("cpu", cgroup_file, mountinfo_file):
        quota_pairs.extend([
            (os.path.join(directory, "cpu.max"), None),
            (os.path.join(directory, "cpu.cfs_quota_us"),
             os.path.join(directory, "cpu.cfs_period_us")),
        ])
    if include_root_fallback:
        cpuset_paths.extend([
            "/sys/fs/cgroup/cpuset.cpus.effective",
            "/sys/fs/cgroup/cpuset/cpuset.cpus",
        ])
        quota_pairs.extend([
            ("/sys/fs/cgroup/cpu.max", None),
            ("/sys/fs/cgroup/cpu/cpu.cfs_quota_us",
             "/sys/fs/cgroup/cpu/cpu.cfs_period_us"),
        ])
    return list(dict.fromkeys(cpuset_paths)), list(dict.fromkeys(quota_pairs))


def cgroup_core_limit(cpuset_paths=None, quota_pairs=None,
                      cgroup_file="/proc/self/cgroup",
                      mountinfo_file="/proc/self/mountinfo"):
    """Tightest nested whole-core cgroup cpuset/quota limit, or ``None``."""
    if cpuset_paths is None and quota_pairs is None:
        cpuset_paths, quota_pairs = _cpu_candidates(
            cgroup_file,
            mountinfo_file,
            cgroup_file == "/proc/self/cgroup"
            and mountinfo_file == "/proc/self/mountinfo",
        )
    elif cpuset_paths is None:
        cpuset_paths = []
    elif quota_pairs is None:
        quota_pairs = []
    limits = []
    for path in cpuset_paths:
        try:
            with open(path) as fh:
                count = _parse_cpu_set(fh.read())
            if count > 0:
                limits.append(count)
        except OSError:
            continue
    for quota_path, period_path in quota_pairs:
        try:
            with open(quota_path) as fh:
                raw_quota = fh.read().strip()
            if period_path is None:
                quota, period = raw_quota.split()[:2]
                if quota == "max":
                    continue
                quota = int(quota)
                period = int(period)
            else:
                quota = int(raw_quota)
                with open(period_path) as fh:
                    period = int(fh.read().strip())
            if quota > 0 and period > 0:
                limits.append(max(1, quota // period))
        except (OSError, ValueError):
            continue
    return min(limits) if limits else None


def physical_core_count():
    """Effective physical-core budget after affinity and cgroup constraints.

    This value, rather than host-wide CPU count, is split into per-child
    NBCORE budgets by :func:`plan_solver_resources`.
    """
    limits = [_host_physical_core_count()]
    try:
        affinity = len(os.sched_getaffinity(0))
        if affinity > 0:
            limits.append(affinity)
    except (AttributeError, OSError):
        pass
    cgroup_limit = cgroup_core_limit()
    if cgroup_limit is not None:
        limits.append(cgroup_limit)
    return max(1, min(limits))


def cap_workers(requested, per_proc_mb, label="sweep"):
    """Cap concurrency so `requested * per_proc_mb` cannot overcommit RAM.

    Reserves generous headroom (>=16 GiB or 1/3 of RAM) for the OS, the editor,
    this/other agents, and — critically — a possible concurrent cargo build.
    Only ever *reduces* concurrency; a config that already fits is left alone.
    Returns the (possibly reduced) worker count.
    """
    ram_mb = physical_ram_mb()
    if not ram_mb or per_proc_mb <= 0:
        return requested  # unknown RAM: don't second-guess the caller
    headroom = max(16000, ram_mb // 3)
    budget = max(per_proc_mb, ram_mb - headroom)
    cap = max(1, budget // per_proc_mb)
    if requested > cap:
        print(
            f"[oom-guard] {label}: {requested} workers x {per_proc_mb}MB = "
            f"{requested * per_proc_mb}MB exceeds safe budget {budget}MB "
            f"(RAM {ram_mb}MB - headroom {headroom}MB). Capping to {cap} workers.",
            flush=True,
        )
    return min(requested, cap)


ResourcePlan = collections.namedtuple(
    "ResourcePlan", ["jobs", "memlimit_mb", "nbcore", "headroom_mb"]
)


def plan_solver_resources(jobs, ram_mb=None, cores=None, headroom_mb=None,
                          mem_floor_mb=1024, label="harness"):
    """Plan (jobs, memlimit_mb_per_job, nbcore_per_job) for a parallel harness.

    Pure given explicit `ram_mb`/`cores` (injectable for tests); otherwise they
    are detected. Policy:
      * reserve `headroom_mb` (default: max(16 GiB, RAM/3) — same policy as
        cap_workers) for the OS, agents, and a possible concurrent cargo build;
      * split the remaining budget evenly across jobs as a per-child MEMLIMIT
        (MiB), never below `mem_floor_mb` — jobs are REDUCED rather than
        starving each child below the floor;
      * split physical cores evenly across the final jobs as NBCORE (min 1).

    Solver context: without MEMLIMIT each ay-pb child self-limits at phys/2,
    and the main `ay` binary at 85% of RAM — both sibling-blind, so N parallel
    children multiply them (the 2026-06-19 / 2026-07-11 panic arithmetic).

    Automatically detected unknown/insufficient RAM fails closed. Explicit
    ``ram_mb=0`` remains a pure-test/diagnostic representation of an unknown
    envelope; production callers must never spawn from that zero plan.
    """
    jobs = max(1, int(jobs))
    detected_ram = ram_mb is None
    cgroup = None
    if detected_ram:
        ram_mb = physical_ram_mb()
        cgroup = cgroup_memory_mb()
    if cores is None:
        cores = physical_core_count()
    cores = max(1, int(cores))
    if mem_floor_mb <= 0:
        return ResourcePlan(jobs, 0, max(1, cores // jobs), 0)
    if not ram_mb:
        if detected_ram:
            raise RuntimeError(
                "cannot determine an effective RAM ceiling; refusing an unenveloped plan"
            )
        return ResourcePlan(jobs, 0, max(1, cores // jobs), 0)
    if headroom_mb is None:
        if cgroup is not None and cgroup.limit_mb <= ram_mb:
            # Host-wide 16 GiB headroom is nonsensical inside a smaller
            # container. Reserve 10% (at least 1 GiB) inside the controller,
            # and separately account for its current usage below.
            headroom_mb = max(1024, ram_mb // 10)
        else:
            headroom_mb = max(16000, ram_mb // 3)
    budget = ram_mb - headroom_mb
    if cgroup is not None:
        cgroup_remaining = cgroup.limit_mb - cgroup.current_mb
        budget = min(budget, cgroup_remaining - headroom_mb)
    # A detected controller with less than one minimum child left must fail
    # closed. Native and shell harnesses reject this zero plan before spawning.
    if budget < mem_floor_mb:
        if detected_ram:
            raise RuntimeError(
                f"only {max(0, budget)}MiB remains after effective memory limits and "
                f"headroom; need at least {mem_floor_mb}MiB for one child"
            )
        # Preserve deterministic explicit-ram semantics used by policy tests:
        # collapse to one floor-sized job. Automatic host planning above never
        # fabricates this capacity.
        budget = mem_floor_mb
    fit = max(1, budget // mem_floor_mb)
    if jobs > fit:
        print(
            f"[oom-guard] {label}: {jobs} jobs x {mem_floor_mb}MB floor exceeds "
            f"safe budget {budget}MB (RAM {ram_mb}MB - headroom {headroom_mb}MB). "
            f"Capping to {fit} jobs.",
            file=sys.stderr, flush=True,
        )
        jobs = fit
    memlimit_mb = max(mem_floor_mb, budget // jobs)
    nbcore = max(1, cores // jobs)
    return ResourcePlan(jobs, memlimit_mb, nbcore, headroom_mb)


def count_active_rustc():
    """Number of live rustc or build-driving cargo processes.

    `cargo metadata` and other non-building cargo commands are excluded, while
    an unrelated build/check/test/run/clippy process blocked between rustc
    children still counts. A cargo process supervising the current executable
    (`cargo test`/`cargo run`) is an ancestor, not a concurrent build, and is
    excluded once its rustc children have finished.
    """
    try:
        out = subprocess.run(["pgrep", "-x", "rustc"], capture_output=True, text=True)
        count = sum(
            1 for raw_pid in out.stdout.split()
            if raw_pid.isdigit() and _process_state(raw_pid) != "Z"
        )
        cargo = subprocess.run(["pgrep", "-x", "cargo"], capture_output=True, text=True)
        build_commands = {
            "build", "check", "test", "run", "clippy", "rustc", "bench",
            "doc", "install", "fix",
        }
        ancestors = _ancestor_pids()
        for raw_pid in cargo.stdout.split():
            if not raw_pid.isdigit():
                continue
            if int(raw_pid) in ancestors:
                continue
            command = ""
            try:
                with open(f"/proc/{raw_pid}/cmdline", "rb") as fh:
                    command = fh.read().replace(b"\0", b" ").decode(errors="replace")
            except OSError:
                try:
                    command = subprocess.check_output(
                        ["ps", "-p", raw_pid, "-o", "command="], text=True
                    )
                except Exception:
                    continue
            tokens = command.split()
            if any(token in build_commands for token in tokens[1:]):
                count += 1
        return count
    except Exception:
        return 0


def _ancestor_pids(pid=None):
    """Linux ancestor PID set, used to ignore the supervising cargo command."""
    current = os.getpid() if pid is None else int(pid)
    ancestors = set()
    visited = set()
    while current > 1 and current not in visited:
        visited.add(current)
        try:
            with open(f"/proc/{current}/stat") as fh:
                fields = fh.read().rsplit(")", 1)[1].split()
            parent = int(fields[1])  # field 4 (ppid); fields start at state/3.
        except (OSError, ValueError, IndexError):
            break
        if parent <= 0 or parent == current:
            break
        ancestors.add(parent)
        current = parent
    return ancestors


def _process_state(pid):
    """Return a Linux /proc process state, or None when unavailable."""
    try:
        with open(f"/proc/{int(pid)}/stat") as fh:
            return fh.read().rsplit(")", 1)[1].split()[0]
    except (OSError, ValueError, IndexError):
        return None


def process_group_rss_mb(pgid):
    """Aggregate RSS (MiB) of every process in group `pgid`; None if UNKNOWN.

    `ps -o rss` reports KiB on both macOS and Linux; filtering happens here
    rather than via ps flags because BSD and procps disagree on `-g`.

    Returns None — never 0 — when the measurement fails. This used to `return 0`
    on every exception path, including the `timeout=10` on the `ps` call, and the
    caller's `if rss > kill_mb` then silently never fired. Under a swap storm
    (79 swapfiles, compressor at 100% — the documented 07-11 conditions) a full
    `ps -ax` task-info walk is exactly what blocks, so the guard disarmed itself,
    quietly, precisely in the regime it exists for. Callers MUST treat None as
    "measurement failed" and escalate; see _RssWatchdog._watch.
    """
    # Linux fast path: avoid launching a full `ps -ax` process at 50 Hz for
    # every concurrently watched child. `/proc/<pid>/stat` field 5 is pgrp and
    # `/proc/<pid>/statm` field 2 is resident pages.
    if os.path.exists("/proc/self/stat"):
        try:
            page_kb = os.sysconf("SC_PAGE_SIZE") // 1024
            total_kb = 0
            group_seen = False
            process_seen = False
            for name in os.listdir("/proc"):
                if not name.isdigit():
                    continue
                try:
                    with open(f"/proc/{name}/stat") as fh:
                        stat = fh.read()
                    # comm is parenthesized and may contain spaces or ')'.
                    fields = stat.rsplit(")", 1)[1].split()
                    process_seen = True
                    if int(fields[2]) != int(pgid):
                        continue
                    with open(f"/proc/{name}/statm") as fh:
                        resident_pages = int(fh.read().split()[1])
                    group_seen = True
                    total_kb += resident_pages * page_kb
                except (FileNotFoundError, ProcessLookupError):
                    continue
                except (OSError, ValueError, IndexError):
                    # A matching process whose RSS cannot be read leaves the
                    # group unmeasured; fail closed rather than undercount.
                    return None
            if not process_seen:
                return None
            return total_kb // 1024 if group_seen else 0
        except (OSError, ValueError):
            return None

    try:
        out = subprocess.run(["ps", "-ax", "-o", "pgid=,rss="],
                             capture_output=True, text=True, timeout=10)
    except Exception:
        return None
    if out.returncode != 0 or not out.stdout.strip():
        return None
    want = str(pgid)
    total_kb = 0
    seen = False
    parsed_any = False
    for line in out.stdout.splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[0] == want:
            try:
                total_kb += int(parts[1])
                seen = True
            except ValueError:
                pass
        if len(parts) == 2:
            try:
                int(parts[0])
                int(parts[1])
                parsed_any = True
            except ValueError:
                pass
    # No rows for the group: the child is gone (the caller re-checks proc.poll()),
    # which is a real 0 rather than a failed measurement.
    if not parsed_any:
        return None
    return total_kb // 1024 if seen else 0


class _NoopWatchdog:
    """Placeholder guard when there is no envelope (or no process group)."""
    breached = False

    def stop(self):
        pass


class _RssWatchdog:
    """Poll a child process group's RSS and SIGKILL it past `kill_mb`.

    See rss_watchdog() for the contract. Daemon thread; .stop() is idempotent.
    """

    def __init__(self, proc, pgid, kill_mb, poll_s, label):
        self.breached = False
        self._proc = proc
        self._pgid = pgid
        self._kill_mb = kill_mb
        self._poll_s = poll_s
        self._label = label
        self._stop_evt = threading.Event()
        self._thread = threading.Thread(target=self._watch, daemon=True)
        self._thread.start()

    # Consecutive failed measurements before we assume the worst and kill. At
    # POLL_DEFAULT this is ~0.1s of blindness; the alternative (keep polling and
    # hope) is what disarmed the guard during the 07-11 swap storm.
    _MAX_UNKNOWN = 5

    def _watch(self):
        unknown = 0
        while not self._stop_evt.wait(self._poll_s):
            if self._proc.poll() is not None:
                return
            rss = process_group_rss_mb(self._pgid)

            if rss is None:
                # FAIL CLOSED. Measurement failure is not evidence of safety — under
                # memory pressure it is evidence of the opposite, since that is when
                # the `ps` walk blocks.
                unknown += 1
                if unknown < self._MAX_UNKNOWN:
                    continue
                self.breached = True
                print(f"[oom-guard] {self._label}: cannot measure pgid {self._pgid} "
                      f"({unknown} consecutive failures) — SIGKILLing the process "
                      f"group rather than run it unmeasured (fail-closed).",
                      file=sys.stderr, flush=True)
            else:
                unknown = 0
                if rss <= self._kill_mb:
                    continue
                self.breached = True
                print(f"[oom-guard] {self._label}: child pgid {self._pgid} RSS "
                      f"{rss}MB breached the {self._kill_mb}MB backstop — "
                      f"SIGKILLing the process group (memout).",
                      file=sys.stderr, flush=True)

            try:
                os.killpg(self._pgid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass
            return

    def stop(self):
        self._stop_evt.set()
        if self._thread.is_alive():
            self._thread.join(timeout=10)


# z3's peak allocation rate is 20.2 GiB/s (measured 2026-07-15 at ~800kHz via
# proc_pid_rusage). At the old 1.0s default this poller could miss 20 GiB between
# two samples — it could not bound anything at GB scale. Sampling is ~13,000x
# cheaper than the `ps` walk it triggers, so the interval is not cost-constrained;
# below ~10ms, SIGKILL delivery and page reclaim dominate anyway.
#   1.0s -> misses 20.2 GiB   |   0.10s -> 2.0 GiB   |   0.02s -> 414 MB
POLL_DEFAULT = 0.02


def rss_watchdog(proc, limit_mb, label="harness", poll_s=None, grace_mb=None):
    """External memory-envelope backstop for one solver child.

    `proc` must be a subprocess.Popen started with start_new_session=True (the
    kill and the accounting cover the whole process group). Returns a guard
    object: `.breached` flips to True if the group's RSS exceeded
    limit_mb + grace_mb and the group was SIGKILLed; call `.stop()` after the
    child is reaped.

    The kill threshold sits `grace_mb` (default max(256, limit/10)) ABOVE the
    envelope so a solver that self-enforces its envelope (ay-pb trips at ~90%
    of MEMLIMIT; `ay --memory` at 100%) always trips first and exits gracefully
    with its incumbent — the SIGKILL only fires for children that ignore the
    envelope (the main `ay` binary's `pb` subcommand, external solvers).

    Safe no-op (never breaches) when limit_mb is 0/None, on Windows, or when
    the child is already gone.
    """
    if not limit_mb or limit_mb <= 0:
        return _NoopWatchdog()
    try:
        pgid = os.getpgid(proc.pid)
    except Exception:
        return _NoopWatchdog()  # no POSIX process groups / child already reaped
    if grace_mb is None:
        grace_mb = max(256, limit_mb // 10)
    if poll_s is None:
        poll_s = POLL_DEFAULT
    return _RssWatchdog(proc, pgid, limit_mb + grace_mb, poll_s, label)


class _AttachedProcess:
    """Minimal ``Popen``-compatible view of an already-running process.

    Native Rust harnesses start solver children themselves so they can retain
    exact argv/stdout/exit-code handling.  The ``watch`` CLI attaches the same
    :func:`rss_watchdog` implementation to those children via this adapter.
    Remembering the original process group also makes PID reuse fail closed as
    "the watched child exited" rather than observing an unrelated process.
    """

    def __init__(self, pid):
        self.pid = int(pid)
        self.pgid = os.getpgid(self.pid)

    def poll(self):
        try:
            return None if os.getpgid(self.pid) == self.pgid else 0
        except (ProcessLookupError, PermissionError):
            return 0


def watch_existing_process(pid, limit_mb, label="harness", poll_s=None,
                           grace_mb=0):
    """Watch an existing process group; return whether its RSS limit breached.

    This is the bridge used by Rust benchmark tooling.  It deliberately calls
    :func:`rss_watchdog` instead of maintaining a second implementation whose
    accounting, grace, or fail-closed behavior could drift.
    """
    try:
        proc = _AttachedProcess(pid)
    except (AttributeError, OSError):
        # A very short-lived child may exit before the sidecar attaches.  It
        # consumed no persistent resources, so this is a clean completion. On
        # platforms without POSIX process groups the native memory mechanism
        # remains authoritative and the sidecar is an explicit no-op.
        return False
    guard = rss_watchdog(proc, limit_mb, label=label, poll_s=poll_s,
                         grace_mb=grace_mb)
    interval = POLL_DEFAULT if poll_s is None else max(0.001, poll_s)
    try:
        while proc.poll() is None and not guard.breached:
            time.sleep(interval)
        return guard.breached
    finally:
        guard.stop()


def _terminate_process_group(proc, pgid):
    """Best-effort whole-tree termination after the group leader exits."""
    if os.name == "nt":
        subprocess.run(
            ["taskkill", "/F", "/T", "/PID", str(proc.pid)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return
    try:
        os.killpg(pgid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def run_guarded(command, limit_mb, timeout_s=None, label="harness"):
    """Run one command under the shared RSS watchdog and whole-tree timeout.

    Stdout/stderr are inherited deliberately, making this suitable for shell
    harness command substitution and redirection without buffering potentially
    huge solver logs in the Python wrapper.
    """
    if not command:
        raise ValueError("guarded command must not be empty")
    if not limit_mb or limit_mb <= 0:
        raise ValueError("guarded command requires a positive memory limit")
    popen_kwargs = {}
    if os.name == "nt":
        popen_kwargs["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP
    else:
        popen_kwargs["start_new_session"] = True
    proc = subprocess.Popen(command, **popen_kwargs)
    pgid = proc.pid if os.name == "nt" else os.getpgid(proc.pid)
    # `run` is the primary enforcement for children without a native memory
    # knob. Enforce the persisted limit exactly; the default watchdog grace is
    # reserved for backstopping solvers that already self-enforce.
    guard = rss_watchdog(proc, limit_mb, label=label, grace_mb=0)
    timed_out = False
    received_signal = [None]
    previous_handlers = {}

    def terminate_on_parent_signal(signum, _frame):
        received_signal[0] = signum
        _terminate_process_group(proc, pgid)

    if threading.current_thread() is threading.main_thread():
        for signum in (signal.SIGINT, signal.SIGTERM):
            previous_handlers[signum] = signal.getsignal(signum)
            signal.signal(signum, terminate_on_parent_signal)
    try:
        try:
            returncode = proc.wait(timeout=timeout_s)
        except subprocess.TimeoutExpired:
            timed_out = True
            _terminate_process_group(proc, pgid)
            returncode = proc.wait()
    finally:
        # A wrapper can exit successfully while descendants remain in its
        # process group. Never disarm the watchdog while those descendants run.
        _terminate_process_group(proc, pgid)
        try:
            proc.wait(timeout=5)
        except (subprocess.TimeoutExpired, OSError):
            _terminate_process_group(proc, pgid)
            try:
                proc.wait(timeout=5)
            except (subprocess.TimeoutExpired, OSError):
                pass
        guard.stop()
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)
    if received_signal[0] is not None:
        return 128 + received_signal[0]
    if guard.breached:
        return WATCHDOG_BREACH_EXIT
    if timed_out:
        return WATCHDOG_TIMEOUT_EXIT
    if returncode < 0:
        return 128 + min(127, -returncode)
    return returncode


def warn_concurrent_build():
    """Refuse if a cargo/rustc build looks active — sweeps running concurrently
    with heavy LTO builds triggered the 2026-06-19 and 2026-07-11 watchdog
    panics."""
    n = count_active_rustc()
    if n >= 1:
        message = (
            f"[oom-guard] REFUSING: {n} build-driver/compiler process(es) are running — a cargo build "
            f"appears active. A sweep running concurrently with a build was the likely "
            f"cause of the 2026-06-19 and 2026-07-11 OOM/watchdog panics. Consider "
            f"waiting for the build to finish before sweeping."
        )
        print(message, file=sys.stderr, flush=True)
        raise RuntimeError(message)


def _cli(argv):
    """Resource-planning and native-harness watchdog CLI."""
    import argparse

    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("plan", help="print PLAN_JOBS/PLAN_MEMLIMIT_MB/"
                                    "PLAN_NBCORE/PLAN_HEADROOM_MB for eval")
    p.add_argument("--jobs", type=int, required=True)
    p.add_argument("--headroom-mb", type=int, default=None)
    p.add_argument("--mem-floor-mb", type=int, default=1024)
    p.add_argument("--label", default="shell")
    p.add_argument("--warn-concurrent-build", action="store_true")
    w = sub.add_parser(
        "watch",
        help="attach rss_watchdog to an existing process group",
    )
    w.add_argument("--pid", type=int, required=True)
    w.add_argument("--limit-mb", type=int, required=True)
    w.add_argument("--label", default="native-harness")
    w.add_argument("--poll-s", type=float, default=None)
    w.add_argument("--grace-mb", type=int, default=0)
    r = sub.add_parser(
        "run",
        help="run a command under rss_watchdog and an optional wall timeout",
    )
    r.add_argument("--limit-mb", type=int, required=True)
    r.add_argument("--timeout-s", type=float, default=None)
    r.add_argument("--label", default="shell-harness")
    r.add_argument("command", nargs=argparse.REMAINDER)
    args = ap.parse_args(argv)
    if args.cmd == "plan":
        if args.warn_concurrent_build:
            warn_concurrent_build()
        plan = plan_solver_resources(args.jobs, headroom_mb=args.headroom_mb,
                                     mem_floor_mb=args.mem_floor_mb, label=args.label)
        print(f"PLAN_JOBS={plan.jobs}")
        print(f"PLAN_MEMLIMIT_MB={plan.memlimit_mb}")
        print(f"PLAN_NBCORE={plan.nbcore}")
        print(f"PLAN_HEADROOM_MB={plan.headroom_mb}")
        return 0
    if args.cmd == "watch":
        if args.limit_mb <= 0:
            ap.error("watch requires --limit-mb > 0")
        breached = watch_existing_process(
            args.pid,
            args.limit_mb,
            label=args.label,
            poll_s=args.poll_s,
            grace_mb=args.grace_mb,
        )
        return WATCHDOG_BREACH_EXIT if breached else 0
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        ap.error("run requires a command after --")
    if args.limit_mb <= 0:
        ap.error("run requires --limit-mb > 0")
    return run_guarded(command, args.limit_mb, timeout_s=args.timeout_s,
                       label=args.label)


if __name__ == "__main__":
    sys.exit(_cli(sys.argv[1:]))
