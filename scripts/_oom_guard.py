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
limits: a large allocation can transiently overshoot the limit between polls,
and it bounds nothing if the harness itself dies. The next successful sample
does observe resident pages from a large mmap; treat the watchdog as a backstop,
not the primary bound.

Python harnesses call :func:`plan_solver_resources` once and retain its
process-scoped host lease for the full campaign. Native Rust harnesses keep a
``lease`` sidecar's stdin open while consuming ``plan`` output. The standalone
``plan`` CLI reports numeric admission only; a shell campaign must likewise
hold a ``lease`` sidecar until all planned children have exited. Production
leases use ``/tmp/ay-oom-guard-<uid>.lock`` regardless of ``TMPDIR`` so every
campaign for one host user contends on the same RAM-admission lock.
"""
import collections
import atexit
import dataclasses
import math
import os
import queue
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


ResourcePlan = collections.namedtuple(
    "ResourcePlan", ["jobs", "memlimit_mb", "nbcore", "headroom_mb"]
)

_ACTIVE_HARNESS_LEASE = None
_HOST_HARNESS_LEASE_DIR = "/tmp"


def _host_harness_lease_path():
    """Return the one production lease path for this host user.

    This must never consult TMPDIR: independently launched campaigns often
    inherit different temporary-directory settings, but still share the same
    physical RAM budget.
    """
    return os.path.join(
        _HOST_HARNESS_LEASE_DIR, f"ay-oom-guard-{os.getuid()}.lock"
    )


def _release_harness_lease():
    global _ACTIVE_HARNESS_LEASE
    if _ACTIVE_HARNESS_LEASE is not None:
        _ACTIVE_HARNESS_LEASE.close()
        _ACTIVE_HARNESS_LEASE = None


atexit.register(_release_harness_lease)


def acquire_harness_lease(label="harness", _lock_path=None):
    """Acquire one host-wide benchmark lease for this process.

    Per-child RSS caps do not protect against two independent harnesses each
    planning against the full host. Production planning therefore fails closed
    when another AY harness owns this exclusive lease. Explicit-RAM unit-policy
    calls skip the lease unless requested.
    """
    global _ACTIVE_HARNESS_LEASE
    if _ACTIVE_HARNESS_LEASE is not None:
        raise RuntimeError(
            "another independently planned benchmark campaign is already active "
            "in this process; reuse its plan explicitly instead of replanning "
            "against full host capacity"
        )
    if os.name == "nt":
        raise RuntimeError("aggregate harness coordination requires POSIX flock")
    import fcntl
    import stat
    if _lock_path is None:
        lock_path = _host_harness_lease_path()
    else:
        # Hidden dependency-injection seam for subprocess tests. Production
        # callers never override the stable host/user path above.
        lock_path = os.fspath(_lock_path)
        if not os.path.isabs(lock_path):
            raise ValueError("test harness lease path must be absolute")
    flags = os.O_RDWR | os.O_CREAT
    flags |= getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    fd = os.open(lock_path, flags, 0o600)
    try:
        metadata = os.fstat(fd)
        if (not stat.S_ISREG(metadata.st_mode) or metadata.st_uid != os.getuid()
                or metadata.st_nlink != 1):
            raise RuntimeError(
                f"unsafe aggregate lease file metadata: {lock_path}"
            )
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError(
                "another AY benchmark harness already owns the host resource lease"
            ) from error
        lease = os.fdopen(fd, "r+", encoding="utf-8")
        fd = -1
        lease.seek(0)
        lease.truncate()
        lease.write(f"pid={os.getpid()} label={label}\n")
        lease.flush()
        _ACTIVE_HARNESS_LEASE = lease
        return lease
    finally:
        if fd >= 0:
            os.close(fd)


def plan_solver_resources(jobs, ram_mb=None, cores=None, headroom_mb=None,
                          mem_floor_mb=1024, label="harness",
                          acquire_lease=None):
    """Plan (jobs, memlimit_mb_per_job, nbcore_per_job) for a parallel harness.

    Pure given explicit `ram_mb`/`cores` (injectable for tests); otherwise they
    are detected. Policy:
      * reserve `headroom_mb` (default: max(16 GiB, RAM/3)) for the OS,
        agents, and a possible concurrent cargo build;
      * split the remaining budget evenly across jobs as a per-child MEMLIMIT
        (MiB), never below `mem_floor_mb` — jobs are REDUCED rather than
        starving each child below the floor;
      * split physical cores evenly across the final jobs as NBCORE (min 1).

    Solver context: without MEMLIMIT each ay-pb child self-limits at phys/2,
    and the main `ay` binary at 85% of RAM — both sibling-blind, so N parallel
    children multiply them (the 2026-06-19 / 2026-07-11 panic arithmetic).

    Unknown or insufficient RAM fails closed; a zero-memory plan is never a
    valid execution envelope.
    """
    jobs = int(jobs)
    if jobs <= 0:
        raise ValueError("jobs must be positive")
    mem_floor_mb = int(mem_floor_mb)
    if mem_floor_mb <= 0:
        raise ValueError("mem_floor_mb must be positive")
    if headroom_mb is not None:
        headroom_mb = int(headroom_mb)
        if headroom_mb < 0:
            raise ValueError("headroom_mb must be non-negative")
    detected_ram = ram_mb is None
    if acquire_lease is None:
        acquire_lease = detected_ram
    cgroup = None
    if detected_ram:
        ram_mb = physical_ram_mb()
        cgroup = cgroup_memory_mb()
    if cores is None:
        cores = physical_core_count()
    cores = int(cores)
    if cores <= 0:
        raise ValueError("cores must be positive")
    ram_mb = int(ram_mb or 0)
    if ram_mb <= 0:
        message = "cannot determine an effective RAM ceiling; refusing an unenveloped plan"
        if detected_ram:
            raise RuntimeError(message)
        raise ValueError("ram_mb must be positive")
    if headroom_mb is None:
        if cgroup is not None and cgroup.limit_mb <= ram_mb:
            # Host-wide 16 GiB headroom is nonsensical inside a smaller
            # container. Reserve 10% (at least 1 GiB) inside the controller,
            # and separately account for its current usage below.
            headroom_mb = max(1024, ram_mb // 10)
        else:
            headroom_mb = max(16000, ram_mb // 3)
        # On small hosts, preserve one real child budget instead of recording
        # impossible headroom and fabricating the floor later.
        headroom_mb = min(headroom_mb, max(0, ram_mb - mem_floor_mb))
    budget = ram_mb - headroom_mb
    if cgroup is not None:
        cgroup_remaining = cgroup.limit_mb - cgroup.current_mb
        budget = min(budget, cgroup_remaining - headroom_mb)
    # A detected controller with less than one minimum child left must fail
    # closed. Native and shell harnesses reject this zero plan before spawning.
    if budget < mem_floor_mb:
        raise RuntimeError(
            f"only {max(0, budget)}MiB remains after effective memory limits and "
            f"headroom; need at least {mem_floor_mb}MiB for one child"
        )
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
    # Acquire only after every validation succeeds. A caller that handles a
    # failed planning attempt must not retain a host-wide lease accidentally.
    # The non-blocking flock still makes admission atomic before this plan is
    # returned to code that can spawn children.
    if acquire_lease:
        acquire_harness_lease(label)
    return ResourcePlan(jobs, memlimit_mb, nbcore, headroom_mb)


def _named_build_processes(proc_root="/proc", max_entries=1_000_000):
    """Return bounded ``(pid, comm)`` rows for supported Rust build tools."""
    wanted = {"cargo", "targo", "rustc", "compiler_consumer"}
    rows = []
    seen = 0
    try:
        entries = os.scandir(proc_root)
    except OSError as error:
        raise RuntimeError(f"cannot inspect build processes in {proc_root}: {error}")
    with entries:
        for entry in entries:
            seen += 1
            if seen > max_entries:
                raise RuntimeError(
                    f"process table exceeds fixed {max_entries}-entry inspection cap"
                )
            if not entry.name.isdigit():
                continue
            try:
                with open(os.path.join(proc_root, entry.name, "comm"), "rb") as fh:
                    raw_name = fh.read(129)
            except FileNotFoundError:
                continue
            except OSError as error:
                raise RuntimeError(
                    f"cannot inspect process {entry.name} name: {error}"
                )
            if len(raw_name) > 128:
                raise RuntimeError(f"process {entry.name} has an oversized name")
            name = raw_name.rstrip(b"\n").decode("utf-8", errors="replace")
            if name in wanted:
                rows.append((int(entry.name), name))
    return rows


def count_active_rustc(proc_root="/proc", ancestor_pids=None):
    """Number of live rustc/compiler_consumer or build-driving cargo/targo processes.

    Metadata, stopped processes, and other non-building driver commands are
    excluded. A cargo or targo process supervising this executable is an
    ancestor, not a concurrent build, and is excluded once its compiler
    children have finished.
    """
    processes = _named_build_processes(proc_root)
    inactive_states = {"Z", "T", "t", "X", "x"}
    count = sum(
        1 for pid, name in processes
        if name in ("rustc", "compiler_consumer")
        and _process_state(pid, proc_root=proc_root) not in inactive_states
    )
    build_commands = {
        "build", "check", "test", "run", "clippy", "rustc", "bench",
        "doc", "install", "fix",
    }
    ancestors = _ancestor_pids() if ancestor_pids is None else set(ancestor_pids)
    for pid, name in processes:
        if name not in ("cargo", "targo") or pid in ancestors:
            continue
        if _process_state(pid, proc_root=proc_root) in inactive_states:
            continue
        try:
            with open(os.path.join(proc_root, str(pid), "cmdline"), "rb") as fh:
                command = fh.read(64 * 1024 + 1)
            if len(command) > 64 * 1024:
                raise RuntimeError(
                    f"{name} process {pid} has an oversized command line"
                )
            command = command.replace(b"\0", b" ").decode(errors="replace")
        except FileNotFoundError:
            continue
        except OSError as error:
            raise RuntimeError(f"cannot inspect {name} process {pid}: {error}")
        tokens = command.split()
        if any(token in build_commands for token in tokens[1:]):
            count += 1
    return count


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


def _process_state(pid, proc_root="/proc"):
    """Return a Linux /proc process state, or None when unavailable."""
    try:
        with open(os.path.join(proc_root, str(int(pid)), "stat")) as fh:
            return fh.read().rsplit(")", 1)[1].split()[0]
    except (OSError, ValueError, IndexError):
        return None


_RSS_SNAPSHOT_LOCK = threading.Lock()
_RSS_SNAPSHOT_AT = 0.0
_RSS_SNAPSHOT = None
_RSS_SNAPSHOT_READY = False
_RSS_SNAPSHOT_TTL_S = 0.02
_RSS_SNAPSHOT_SCAN_COUNT = 0


def _linux_group_rss_snapshot():
    """One cached /proc walk shared by every concurrent watchdog thread."""
    global _RSS_SNAPSHOT_AT, _RSS_SNAPSHOT, _RSS_SNAPSHOT_READY
    global _RSS_SNAPSHOT_SCAN_COUNT
    with _RSS_SNAPSHOT_LOCK:
        # Compute freshness only after acquiring the lock. A thread may have
        # waited behind a slow scan; using its pre-lock timestamp would make
        # the snapshot appear expired immediately and serialize one full scan
        # per waiting watchdog under the exact memory pressure we guard.
        now = time.monotonic()
        if _RSS_SNAPSHOT_READY and now - _RSS_SNAPSHOT_AT < _RSS_SNAPSHOT_TTL_S:
            return _RSS_SNAPSHOT
        _RSS_SNAPSHOT_SCAN_COUNT += 1
        try:
            page_kb = os.sysconf("SC_PAGE_SIZE") // 1024
            totals = collections.defaultdict(int)
            process_seen = False
            for name in os.listdir("/proc"):
                if not name.isdigit():
                    continue
                try:
                    with open(f"/proc/{name}/stat") as fh:
                        stat_text = fh.read()
                    fields = stat_text.rsplit(")", 1)[1].split()
                    pgid = int(fields[2])
                    with open(f"/proc/{name}/statm") as fh:
                        resident_pages = int(fh.read().split()[1])
                    totals[pgid] += resident_pages * page_kb
                    process_seen = True
                except (FileNotFoundError, ProcessLookupError):
                    continue
                except (OSError, ValueError, IndexError):
                    _RSS_SNAPSHOT = None
                    _RSS_SNAPSHOT_AT = time.monotonic()
                    _RSS_SNAPSHOT_READY = True
                    return None
            if not process_seen:
                _RSS_SNAPSHOT = None
                _RSS_SNAPSHOT_AT = time.monotonic()
                _RSS_SNAPSHOT_READY = True
                return None
            _RSS_SNAPSHOT = {
                pgid: total_kb // 1024 for pgid, total_kb in totals.items()
            }
            _RSS_SNAPSHOT_AT = time.monotonic()
            _RSS_SNAPSHOT_READY = True
            return _RSS_SNAPSHOT
        except (OSError, ValueError):
            _RSS_SNAPSHOT = None
            _RSS_SNAPSHOT_AT = time.monotonic()
            _RSS_SNAPSHOT_READY = True
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
        snapshot = _linux_group_rss_snapshot()
        return None if snapshot is None else snapshot.get(int(pgid), 0)

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
    armed = False
    breached = False
    breach_time_ns = None
    identity_lost = False

    def stop(self):
        pass

    def wait_terminal(self, _timeout=None):
        return True

    def terminate_if_authenticated(self):
        return False


class _RssWatchdog:
    """Poll a child process group's RSS and SIGKILL it past `kill_mb`.

    See rss_watchdog() for the contract. Daemon thread; .stop() is idempotent.
    """

    def __init__(self, proc, pgid, kill_mb, poll_s, label, group_identity):
        self.armed = False
        self.breached = False
        self.breach_time_ns = None
        self._proc = proc
        self._pgid = pgid
        self._kill_mb = kill_mb
        self._poll_s = poll_s
        self._label = label
        self._group_identity = group_identity
        self._stop_evt = threading.Event()
        self._ready_evt = threading.Event()
        self._terminal_evt = threading.Event()
        self.identity_lost = False
        self._thread = threading.Thread(target=self._watch, daemon=True)
        self._thread.start()
        if not self._ready_evt.wait(timeout=10):
            self._stop_evt.set()
            self._thread.join(timeout=10)
            raise RuntimeError(f"{label}: RSS watchdog thread did not start")
        self.armed = True

    # Consecutive failed measurements before we assume the worst and kill. At
    # POLL_DEFAULT this is ~0.1s of blindness; the alternative (keep polling and
    # hope) is what disarmed the guard during the 07-11 swap storm.
    _MAX_UNKNOWN = 5

    def _same_group(self):
        """Authenticate the watched PGID before observing or signalling it."""
        return _group_identity_is_current(self._pgid, self._group_identity)

    def _retain_authenticated_group(self):
        if self._same_group():
            return True
        self.identity_lost = True
        return False

    def wait_terminal(self, timeout=None):
        """Wait until the monitor breaches, stops, or loses its identity."""
        return self._terminal_evt.wait(timeout)

    def terminate_if_authenticated(self):
        """Kill only while the originally captured group identity is current."""
        if not self._retain_authenticated_group():
            return False
        _terminate_process_group(self._proc, self._pgid)
        return True

    def _watch(self):
        self._ready_evt.set()
        unknown = 0
        try:
            while not self._stop_evt.wait(self._poll_s):
                if not self._retain_authenticated_group():
                    return
                rss = process_group_rss_mb(self._pgid)

                if rss is None:
                    if not self._retain_authenticated_group():
                        return
                    # FAIL CLOSED. Measurement failure is not evidence of safety — under
                    # memory pressure it is evidence of the opposite, since that is when
                    # the `ps` walk blocks.
                    unknown += 1
                    if unknown < self._MAX_UNKNOWN:
                        continue
                    if not self._retain_authenticated_group():
                        return
                    self.breach_time_ns = time.monotonic_ns()
                    self.breached = True
                    print(f"[oom-guard] {self._label}: cannot measure pgid {self._pgid} "
                          f"({unknown} consecutive failures) — SIGKILLing the process "
                          f"group rather than run it unmeasured (fail-closed).",
                          file=sys.stderr, flush=True)
                else:
                    unknown = 0
                    if rss <= self._kill_mb:
                        continue
                    if not self._retain_authenticated_group():
                        return
                    self.breach_time_ns = time.monotonic_ns()
                    self.breached = True
                    print(f"[oom-guard] {self._label}: child pgid {self._pgid} RSS "
                          f"{rss}MB breached the {self._kill_mb}MB backstop — "
                          f"SIGKILLing the process group (memout).",
                          file=sys.stderr, flush=True)

                self.terminate_if_authenticated()
                return
        finally:
            self._terminal_evt.set()

    def stop(self):
        self._stop_evt.set()
        if self._thread.is_alive():
            self._thread.join(timeout=10)
        if self._thread.is_alive():
            raise RuntimeError(
                f"{self._label}: RSS watchdog thread did not stop within 10 seconds"
            )


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

    Safe no-op (never breaches) only when limit_mb is 0/None. A positive
    envelope fails closed when POSIX process-group enforcement cannot arm or
    the child is already gone.
    """
    if limit_mb is None or limit_mb == 0:
        return _NoopWatchdog()
    if not math.isfinite(float(limit_mb)) or limit_mb <= 0:
        raise ValueError("RSS watchdog limit_mb must be finite and positive")
    if os.name == "nt" or not hasattr(os, "killpg"):
        raise RuntimeError(
            f"{label}: RSS watchdog requires POSIX process groups"
        )
    try:
        pgid = os.getpgid(proc.pid)
    except Exception as error:
        raise RuntimeError(
            f"{label}: cannot identify child process group; refusing an unarmed envelope"
        ) from error
    if int(pgid) != int(proc.pid):
        raise RuntimeError(
            f"{label}: child pid {proc.pid} is not its process-group leader "
            f"(pgid {pgid}); refusing to arm a watchdog that could target "
            "the harness group"
        )
    if grace_mb is None:
        grace_mb = max(256, limit_mb // 10)
    if not math.isfinite(float(grace_mb)) or grace_mb < 0:
        raise ValueError("RSS watchdog grace_mb must be finite and non-negative")
    if poll_s is None:
        poll_s = POLL_DEFAULT
    if not math.isfinite(float(poll_s)) or poll_s <= 0:
        raise ValueError("RSS watchdog poll_s must be finite and positive")
    group_identity = _group_watch_identity(pgid, proc.pid)
    if group_identity is None:
        raise RuntimeError(
            f"{label}: cannot authenticate process-group identity for pgid {pgid}"
        )
    return _RssWatchdog(
        proc, pgid, limit_mb + grace_mb, poll_s, label, group_identity
    )


def _process_group_exists(pgid):
    """Whether the exact process group still has at least one member."""
    try:
        os.killpg(int(pgid), 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        # The group exists even if a restricted platform denies inspection.
        return True


def _safe_getpgid(pid):
    try:
        return os.getpgid(int(pid))
    except (ProcessLookupError, PermissionError, OSError):
        return None


def _group_identity_is_current(pgid, group_identity):
    """Whether ``pgid`` still contains the exact member captured at arming."""
    if group_identity is None:
        return False
    pid, identity = group_identity
    return (
        _watch_process_identity(pid) == (pid, identity)
        and _safe_getpgid(pid) == int(pgid)
    )


def _terminate_process_group_if_authenticated(proc, pgid, group_identity):
    """Best-effort kill that refuses a vanished or recycled process group."""
    if not _group_identity_is_current(pgid, group_identity):
        return False
    _terminate_process_group(proc, pgid)
    return True


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
                           grace_mb=0, ready_file=None, ready_stdout=False,
                           return_details=False):
    """Watch an existing process group; return whether its RSS limit breached.

    This is the bridge used by Rust benchmark tooling.  It deliberately calls
    :func:`rss_watchdog` instead of maintaining a second implementation whose
    accounting, grace, or fail-closed behavior could drift.
    """
    if poll_s is not None and (not math.isfinite(float(poll_s)) or poll_s <= 0):
        raise ValueError("watch poll_s must be finite and positive")
    try:
        proc = _AttachedProcess(pid)
    except (AttributeError, OSError):
        # Absence is not evidence that the child respected the limit: it may
        # have allocated and exited before this sidecar attached. Fail closed.
        result = (True, time.monotonic_ns())
        return result if return_details else result[0]
    guard = rss_watchdog(proc, limit_mb, label=label, poll_s=poll_s,
                         grace_mb=grace_mb)
    interval = POLL_DEFAULT if poll_s is None else max(0.001, poll_s)
    completed_normally = False
    previous_handlers = {}

    def interrupt_watch(signum, _frame):
        raise RuntimeError(
            f"{label}: watchdog sidecar interrupted by signal {signum}"
        )

    if threading.current_thread() is threading.main_thread():
        for signum in (signal.SIGINT, signal.SIGTERM):
            previous_handlers[signum] = signal.getsignal(signum)
            signal.signal(signum, interrupt_watch)
    try:
        if not getattr(guard, "armed", False):
            print(f"[oom-guard] {label}: RSS watchdog did not arm; refusing "
                  "to signal readiness", file=sys.stderr, flush=True)
            return True
        if ready_file is not None:
            try:
                with open(ready_file, "w", encoding="utf-8") as ready:
                    ready.write("ready\n")
                    ready.flush()
            except OSError as error:
                print(f"[oom-guard] {label}: cannot signal armed watchdog: {error}",
                      file=sys.stderr, flush=True)
                return True
        if ready_stdout:
            # Rust's native harness consumes this fixed marker through the
            # sidecar's inherited stdout pipe. Unlike a shared pathname, that
            # channel cannot be forged by an unrelated filesystem writer.
            print("AY_OOM_WATCHDOG_READY_V1", flush=True)
        # The monitor owns the authenticated identity. Waiting on a raw PGID
        # here could follow a recycled group after the original target exits.
        while not guard.wait_terminal(interval):
            pass
        completed_normally = True
        result = (guard.breached, guard.breach_time_ns)
        return result if return_details else result[0]
    finally:
        # A sidecar that disappears while the target group is live must never
        # turn an enforced run into an orphaned, unbounded solver. SIGKILL
        # cannot execute Python cleanup, so Rust also owns the target PGID and
        # kills it before force-killing this sidecar during normal teardown.
        if not completed_normally:
            guard.terminate_if_authenticated()
        guard.stop()
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)


WATCH_SERVER_READY = b"AY_OOM_WATCHDOG_SERVER_READY_V1\n"
WATCH_SERVER_MAX_COMMAND_BYTES = 4096
WATCH_SERVER_HEARTBEAT_S = 0.1


def _watch_server_write(output, lock, line):
    """Write one bounded authenticated-by-pipe server protocol record."""
    payload = line.encode("ascii") + b"\n"
    if len(payload) > WATCH_SERVER_MAX_COMMAND_BYTES:
        raise RuntimeError("watchdog server response exceeds protocol limit")
    with lock:
        output.write(payload)
        output.flush()


def _watch_server_error_text(error):
    return str(error).encode("utf-8", errors="replace")[:512].hex()


def serve_watchdog_requests(input_stream, output_stream):
    """Multiplex campaign children through one RSS snapshot cache.

    Every WATCH request still arms :func:`rss_watchdog` independently, but all
    watchdog threads live in this interpreter and therefore share exactly one
    cached `/proc` walk per poll interval. EOF or a malformed command kills all
    still-registered process groups, preserving fail-closed sidecar semantics.
    """
    output_lock = threading.Lock()
    watches_lock = threading.Lock()
    workers_done = threading.Condition(watches_lock)
    watches = {}
    closing = threading.Event()
    active_workers = 0
    previous_handlers = {}
    received_signal = [None]

    def interrupt_server(signum, _frame):
        # Do not raise asynchronously here. In particular, SIGTERM can arrive
        # after READY is written while threading.Thread.start() is waiting for
        # its child bootstrap. Raising in that window can make start() report
        # failure even though the worker did start, and both paths then mutate
        # the worker count. Wake the main loop cooperatively instead.
        received_signal[0] = signum
        closing.set()

    if threading.current_thread() is threading.main_thread():
        for signum in (signal.SIGINT, signal.SIGTERM):
            previous_handlers[signum] = signal.getsignal(signum)
            signal.signal(signum, interrupt_server)

    output_stream.write(WATCH_SERVER_READY)
    output_stream.flush()

    def emit_heartbeats():
        # The Rust parent treats heartbeat loss as a campaign-wide enforcement
        # failure and kills every affected target group. This independent
        # thread keeps the liveness signal flowing while the main server thread
        # is intentionally blocked in readline waiting for another WATCH.
        while not closing.wait(WATCH_SERVER_HEARTBEAT_S):
            try:
                _watch_server_write(
                    output_stream,
                    output_lock,
                    f"HEARTBEAT {time.monotonic_ns()}",
                )
            except Exception:
                closing.set()
                return

    heartbeat_worker = threading.Thread(target=emit_heartbeats, daemon=True)
    heartbeat_worker.start()

    commands = queue.Queue()

    def read_commands():
        # A dedicated daemon reader lets the main thread react to signals and
        # heartbeat failures without relying on an exception to interrupt a
        # buffered stdin readline. The CLI process exits immediately after
        # server teardown, so a reader still blocked on an inherited pipe
        # cannot outlive any protected campaign.
        try:
            while not closing.is_set():
                command = input_stream.readline(WATCH_SERVER_MAX_COMMAND_BYTES + 1)
                commands.put(("command", command))
                if not command:
                    return
        except Exception as error:
            commands.put(("error", error))

    command_reader = threading.Thread(target=read_commands, daemon=True)
    command_reader.start()

    def complete_watch(watch_id, proc, guard, label):
        nonlocal active_workers
        try:
            # The guard's terminal event is tied to its captured process
            # identity. A raw `killpg(pgid, 0)` loop can silently follow a
            # recycled numeric PGID after the original group disappears.
            while not guard.wait_terminal(POLL_DEFAULT):
                if closing.is_set():
                    guard.terminate_if_authenticated()
                    break
            guard.stop()
            if closing.is_set():
                return
            if guard.breached:
                if guard.breach_time_ns is None:
                    raise RuntimeError("watchdog breach is missing its monotonic timestamp")
                _watch_server_write(
                    output_stream,
                    output_lock,
                    f"BREACH {watch_id} {guard.breach_time_ns}",
                )
            else:
                _watch_server_write(output_stream, output_lock, f"DONE {watch_id}")
        except Exception as error:
            guard.terminate_if_authenticated()
            if not closing.is_set():
                try:
                    _watch_server_write(
                        output_stream,
                        output_lock,
                        f"ERROR {watch_id} {_watch_server_error_text(error)}",
                    )
                except Exception:
                    closing.set()
        finally:
            try:
                guard.stop()
            except Exception:
                pass
            with workers_done:
                watches.pop(watch_id, None)
                active_workers -= 1
                workers_done.notify_all()

    failure = None
    try:
        while not closing.is_set():
            try:
                command_kind, command_payload = commands.get(
                    timeout=WATCH_SERVER_HEARTBEAT_S
                )
            except queue.Empty:
                continue
            if command_kind == "error":
                raise command_payload
            command = command_payload
            if not command:
                break
            if len(command) > WATCH_SERVER_MAX_COMMAND_BYTES or not command.endswith(b"\n"):
                raise RuntimeError("watchdog server command exceeds protocol limit")
            try:
                fields = command.decode("ascii").strip().split(" ")
                if len(fields) != 5 or fields[0] != "WATCH":
                    raise ValueError("invalid WATCH command")
                watch_id = int(fields[1])
                pid = int(fields[2])
                limit_mb = int(fields[3])
                label_bytes = bytes.fromhex(fields[4])
                label = label_bytes.decode("utf-8")
                if watch_id <= 0 or pid <= 0 or limit_mb <= 0:
                    raise ValueError("WATCH numeric fields must be positive")
                if len(label_bytes) > 512:
                    raise ValueError("WATCH label exceeds 512 bytes")
            except (UnicodeError, ValueError) as error:
                raise RuntimeError(f"malformed watchdog server command: {error}") from error
            with watches_lock:
                if watch_id in watches:
                    raise RuntimeError(f"duplicate watchdog id {watch_id}")
            proc = None
            cleanup_group_identity = None
            try:
                proc = _AttachedProcess(pid)
                cleanup_group_identity = _group_watch_identity(proc.pgid, proc.pid)
                guard = rss_watchdog(
                    proc,
                    limit_mb,
                    label=label,
                    poll_s=POLL_DEFAULT,
                    grace_mb=0,
                )
                if not getattr(guard, "armed", False):
                    raise RuntimeError("RSS watchdog did not arm")
            except Exception as error:
                try:
                    if proc is not None:
                        _terminate_process_group_if_authenticated(
                            proc,
                            getattr(proc, "pgid", pid),
                            cleanup_group_identity,
                        )
                finally:
                    _watch_server_write(
                        output_stream,
                        output_lock,
                        f"ERROR {watch_id} {_watch_server_error_text(error)}",
                    )
                continue
            with workers_done:
                watches[watch_id] = (proc, guard)
                active_workers += 1
            worker = threading.Thread(
                target=complete_watch,
                args=(watch_id, proc, guard, label),
                daemon=True,
            )
            try:
                # READY is emitted before the monitor can report a terminal
                # state. Rust keeps the target SIGSTOPped until this record.
                _watch_server_write(output_stream, output_lock, f"READY {watch_id}")
                worker.start()
            except Exception:
                with workers_done:
                    watches.pop(watch_id, None)
                    active_workers -= 1
                guard.terminate_if_authenticated()
                guard.stop()
                raise
    except Exception as error:
        failure = error
    finally:
        closing.set()
        heartbeat_worker.join(timeout=1)
        with watches_lock:
            active = list(watches.values())
        for _proc, guard in active:
            guard.terminate_if_authenticated()
        deadline = time.monotonic() + 10
        with workers_done:
            while active_workers and time.monotonic() < deadline:
                workers_done.wait(timeout=max(0.0, deadline - time.monotonic()))
            if active_workers:
                raise RuntimeError("watchdog server workers did not stop within 10 seconds")
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)
    if failure is None and received_signal[0] is not None:
        failure = RuntimeError(
            f"watchdog server interrupted by signal {received_signal[0]}"
        )
    if failure is not None:
        raise failure


def _terminate_process_group(proc, pgid):
    """Best-effort whole-tree termination after the group leader exits."""
    if os.name == "nt":
        subprocess.run(
            ["taskkill", "/F", "/T", "/PID", str(proc.pid)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=10,
        )
        return
    try:
        os.killpg(pgid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def _kill_reap_failed_spawn(proc, pgid, guard=None):
    """Fail-closed cleanup while the guarded group identity is still leased."""
    cleanup_error = None
    try:
        # The leader may already have been reaped by _wait_for_guard_stop, but
        # exec-stopped creates its PGID anchor before stopping. Always kill and
        # confirm the whole group instead of keying cleanup off returncode.
        _kill_and_reap_group(proc, pgid, "failed guarded spawn")
    except BaseException as error:
        cleanup_error = error
    try:
        if guard is not None:
            guard.stop()
    except BaseException as error:
        if cleanup_error is None:
            cleanup_error = error
        elif hasattr(cleanup_error, "add_note"):
            cleanup_error.add_note(f"watchdog cleanup also failed: {error}")
    if cleanup_error is not None:
        raise cleanup_error


def _guarded_command(command, fsize_bytes=None):
    wrapper = [
        sys.executable,
        os.path.abspath(__file__),
        "exec-stopped",
    ]
    if fsize_bytes is not None:
        if not isinstance(fsize_bytes, int) or fsize_bytes <= 0:
            raise ValueError("guarded file-size limit must be a positive integer")
        wrapper.extend(("--fsize-bytes", str(fsize_bytes)))
    wrapper.extend(("--", *command))
    return wrapper


def _process_identity(pid):
    """Stable process identity where /proc exposes a start-time token."""
    if os.path.exists("/proc/self/stat"):
        try:
            with open(f"/proc/{int(pid)}/stat") as fh:
                fields = fh.read().rsplit(")", 1)[1].split()
            return (int(pid), fields[19])  # field 22: process start time
        except (OSError, ValueError, IndexError):
            return None
    try:
        os.kill(int(pid), 0)
        return (int(pid), None)
    except (ProcessLookupError, PermissionError):
        return None


def _watch_process_identity(pid):
    """Stable identity used to prevent a delayed watcher hitting reused PIDs."""
    identity = _process_identity(pid)
    if identity is None or identity[1] is not None:
        return identity
    # Non-/proc POSIX fallback. lstart is kernel process creation time rather
    # than elapsed time, so it stays stable across the campaign.
    try:
        inspected = subprocess.run(
            ["ps", "-p", str(int(pid)), "-o", "lstart="],
            capture_output=True,
            text=True,
            timeout=5,
        )
    except (OSError, subprocess.TimeoutExpired, ValueError):
        return None
    started = inspected.stdout.strip()
    if inspected.returncode != 0 or not started:
        return None
    return (int(pid), started)


def _group_watch_identity(pgid, leader_pid):
    """Choose an authenticated group member, preferring exec-stopped's anchor."""
    members = []
    if os.path.exists("/proc/self/stat"):
        try:
            entries = os.scandir("/proc")
        except OSError:
            return None
        with entries:
            for entry in entries:
                if not entry.name.isdigit():
                    continue
                try:
                    with open(os.path.join(entry.path, "stat")) as fh:
                        fields = fh.read(4097)
                    if len(fields) > 4096:
                        return None
                    suffix = fields.rsplit(")", 1)[1].split()
                    pid = int(entry.name)
                    if int(suffix[2]) == int(pgid):  # field 5: process group
                        members.append(pid)
                except (OSError, ValueError, IndexError):
                    continue
    else:
        try:
            inspected = subprocess.run(
                ["ps", "-ax", "-o", "pid=,pgid="],
                capture_output=True,
                text=True,
                timeout=10,
            )
        except (OSError, subprocess.TimeoutExpired):
            return None
        if inspected.returncode != 0:
            return None
        for line in inspected.stdout.splitlines():
            pieces = line.split()
            if len(pieces) != 2:
                continue
            try:
                pid, candidate_pgid = (int(piece) for piece in pieces)
            except ValueError:
                continue
            if candidate_pgid == int(pgid):
                members.append(pid)
    members.sort(key=lambda pid: (pid == int(leader_pid), pid))
    for pid in members:
        identity = _watch_process_identity(pid)
        if identity is not None and _safe_getpgid(pid) == int(pgid):
            return identity
    return None


def _process_group_anchor(leader_pid, owner_pid, owner_identity, ready_fd):
    """Lease the original PGID until the parent has time to reap and clean it.

    A solver's group leader can exit before descendants. Once the leader is
    reaped, a later ``killpg(leader_pid)`` would otherwise have a theoretical
    PID/PGID-reuse race. This orphan anchor ignores graceful termination and
    retains the group identity until the parent's immediate SIGKILL cleanup.
    It self-expires if the harness dies before cleanup.
    """
    for signum in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(signum, signal.SIG_IGN)
    try:
        os.write(ready_fd, b"R")
    finally:
        os.close(ready_fd)
    try:
        max_fd = int(os.sysconf("SC_OPEN_MAX"))
    except (OSError, ValueError):
        max_fd = 1024
    os.closerange(0, max_fd)

    while True:
        if _process_identity(owner_pid) != owner_identity:
            # The harness disappeared (or its PID was recycled). Do not leave
            # an unowned solver tree running without its resource controller.
            try:
                os.killpg(os.getpgrp(), signal.SIGKILL)
            finally:
                os._exit(1)
        try:
            os.kill(leader_pid, 0)
        except ProcessLookupError:
            break
        except PermissionError:
            pass
        time.sleep(0.05)
    # Every guarded caller kills the group immediately after observing the
    # leader exit. Keep the identity leased across its bounded cleanup waits,
    # but do not leak forever if the harness itself crashed.
    deadline = time.monotonic() + 60
    while time.monotonic() < deadline:
        if _process_identity(owner_pid) != owner_identity:
            try:
                os.killpg(os.getpgrp(), signal.SIGKILL)
            finally:
                os._exit(1)
        time.sleep(0.05)
    os._exit(0)


def _spawn_process_group_anchor():
    """Create and confirm an identity anchor before the wrapper stops."""
    leader_pid = os.getpid()
    owner_pid = os.getppid()
    owner_identity = _process_identity(owner_pid)
    if owner_identity is None:
        raise RuntimeError("cannot authenticate guarded process owner")
    read_fd, write_fd = os.pipe()
    setup_pid = os.fork()
    if setup_pid == 0:
        os.close(read_fd)
        try:
            anchor_pid = os.fork()
        except OSError:
            try:
                os.write(write_fd, b"E")
            finally:
                os._exit(1)
        if anchor_pid == 0:
            _process_group_anchor(
                leader_pid, owner_pid, owner_identity, write_fd
            )
        os.close(write_fd)
        os._exit(0)

    os.close(write_fd)
    try:
        ready = os.read(read_fd, 1)
    finally:
        os.close(read_fd)
    _, setup_status = os.waitpid(setup_pid, 0)
    if ready != b"R" or not os.WIFEXITED(setup_status) or os.WEXITSTATUS(setup_status) != 0:
        raise RuntimeError("could not create guarded process-group identity anchor")


def _wait_for_guard_stop(proc, pgid, label):
    deadline = time.monotonic() + 10
    while True:
        try:
            waited_pid, status = os.waitpid(proc.pid, os.WUNTRACED | os.WNOHANG)
        except ChildProcessError as error:
            _terminate_process_group(proc, pgid)
            raise RuntimeError(
                f"{label}: guarded child vanished before watchdog attach"
            ) from error
        if waited_pid == 0:
            if time.monotonic() >= deadline:
                _terminate_process_group(proc, pgid)
                try:
                    proc.wait(timeout=5)
                except (subprocess.TimeoutExpired, OSError) as reap_error:
                    raise RuntimeError(
                        f"{label}: guarded child could not be reaped after "
                        "watchdog-attach timeout"
                    ) from reap_error
                raise RuntimeError(
                    f"{label}: guarded child did not stop for watchdog attach"
                )
            time.sleep(0.005)
            continue
        if os.WIFSTOPPED(status) and os.WSTOPSIG(status) == signal.SIGSTOP:
            return
        if os.WIFEXITED(status) or os.WIFSIGNALED(status):
            proc.returncode = os.waitstatus_to_exitcode(status)
        raise RuntimeError(f"{label}: guarded child exited before watchdog attach")


def guarded_popen(command, limit_mb, label="harness", grace_mb=0,
                  poll_s=None, non_reaping_watch=False, fsize_bytes=None,
                  **kwargs):
    """Spawn a child stopped until its process-group RSS watchdog is armed."""
    if not command:
        raise ValueError("guarded command must not be empty")
    if not limit_mb or limit_mb <= 0:
        raise ValueError("guarded command requires a positive memory limit")
    if os.name == "nt" or not hasattr(os, "killpg"):
        raise RuntimeError("exact guarded execution requires POSIX process groups")
    if "creationflags" in kwargs:
        raise ValueError("guarded_popen owns process-group creation")
    kwargs["start_new_session"] = True
    proc = subprocess.Popen(_guarded_command(command, fsize_bytes), **kwargs)
    # start_new_session makes the direct child the group leader, so this value
    # remains stable even after a very short-lived target exits.
    pgid = proc.pid
    try:
        if os.getpgid(proc.pid) != pgid:
            raise RuntimeError(f"{label}: guarded child is not its group leader")
        _wait_for_guard_stop(proc, pgid, label)
    except BaseException:
        _kill_reap_failed_spawn(proc, pgid)
        raise
    guard = None
    try:
        watched = _AttachedProcess(proc.pid) if non_reaping_watch else proc
        guard = rss_watchdog(
            watched, limit_mb, label=label, grace_mb=grace_mb, poll_s=poll_s
        )
        if not getattr(guard, "armed", False):
            raise RuntimeError(
                f"{label}: RSS watchdog did not arm; refusing to resume child"
            )
        os.killpg(pgid, signal.SIGCONT)
    except BaseException:
        # The wrapper is still stopped if arming or SIGCONT failed. Kill it
        # before reaping so neither the process nor its PGID can escape/recycle.
        _kill_reap_failed_spawn(proc, pgid, guard)
        raise
    return proc, guard


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
    if timeout_s is not None and (
            not math.isfinite(float(timeout_s)) or timeout_s <= 0):
        raise ValueError("guarded command timeout must be finite and positive")
    if os.name == "nt" or not hasattr(os, "killpg"):
        raise RuntimeError("exact guarded execution requires POSIX process groups")
    # `run` is the primary enforcement for children without a native memory
    # knob. Enforce the persisted limit exactly; the default watchdog grace is
    # reserved for backstopping solvers that already self-enforce.
    proc, guard = guarded_popen(command, limit_mb, label=label, grace_mb=0)
    pgid = proc.pid
    timed_out = False
    timeout_time_ns = None
    received_signal = [None, None]
    previous_handlers = {}
    returncode = None
    execution_error = None
    cleanup_error = None

    def terminate_on_parent_signal(signum, _frame):
        received_signal[0] = signum
        if received_signal[1] is None:
            received_signal[1] = time.monotonic_ns()
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
            timeout_time_ns = time.monotonic_ns()
            _terminate_process_group(proc, pgid)
        except BaseException as error:
            execution_error = error
    finally:
        # A wrapper can exit successfully while descendants remain in its
        # process group. Never disarm the watchdog while those descendants run.
        reaped = False
        try:
            try:
                _kill_and_reap_group(proc, pgid, label)
                reaped = True
                if returncode is None:
                    returncode = proc.returncode
            except BaseException as error:
                cleanup_error = error
            if reaped:
                try:
                    guard.stop()
                except BaseException as error:
                    if cleanup_error is None:
                        cleanup_error = error
                    elif hasattr(cleanup_error, "add_note"):
                        cleanup_error.add_note(
                            f"watchdog cleanup also failed: {error}"
                        )
        finally:
            for signum, handler in previous_handlers.items():
                signal.signal(signum, handler)
    if execution_error is not None:
        if cleanup_error is not None and hasattr(execution_error, "add_note"):
            execution_error.add_note(f"mandatory cleanup also failed: {cleanup_error}")
        raise execution_error
    if cleanup_error is not None:
        raise cleanup_error
    cause = _first_termination_cause(
        breach_time_ns=guard.breach_time_ns,
        timeout_time_ns=timeout_time_ns,
        cancel_time_ns=received_signal[1],
    )
    if cause == "memout":
        return WATCHDOG_BREACH_EXIT
    if cause == "timeout":
        return WATCHDOG_TIMEOUT_EXIT
    if cause == "cancel":
        return 128 + received_signal[0]
    if returncode < 0:
        return 128 + min(127, -returncode)
    return returncode


def _first_termination_cause(*, breach_time_ns=None, timeout_time_ns=None,
                             cancel_time_ns=None):
    """Return the earliest independently timestamped terminal trigger."""
    candidates = [
        (breach_time_ns, 0, "memout"),
        (timeout_time_ns, 1, "timeout"),
        (cancel_time_ns, 2, "cancel"),
    ]
    present = [candidate for candidate in candidates if candidate[0] is not None]
    return min(present)[2] if present else None


@dataclasses.dataclass(frozen=True)
class CapturedRun:
    """Bounded-process outcome returned by :func:`run_captured`."""

    stdout: str
    stderr: str
    returncode: int
    timed_out: bool
    memout: bool
    wall_sec: float
    stdout_truncated: bool
    stderr_truncated: bool
    cancelled: bool

    @property
    def output_truncated(self):
        """Whether any captured stream exceeded the fixed parent-RAM cap."""
        return self.stdout_truncated or self.stderr_truncated


CAPTURE_LIMIT_BYTES = 1024 * 1024
MAX_DECOMPRESSED_BYTES = 8 * 1024 * 1024 * 1024


def copy_stream_limited(source, destination, limit_bytes=MAX_DECOMPRESSED_BYTES):
    """Copy a decompression stream without allowing unbounded disk growth."""
    if not limit_bytes or limit_bytes <= 0:
        raise ValueError("copy limit must be positive")
    total = 0
    while True:
        chunk = source.read(min(1024 * 1024, limit_bytes - total + 1))
        if not chunk:
            return total
        total += len(chunk)
        if total > limit_bytes:
            raise ValueError(
                f"decompressed output exceeds fixed {limit_bytes}-byte limit"
            )
        destination.write(chunk)


def _bounded_pipe_drain(stream, result, failed_event):
    """Drain a child pipe completely while retaining at most 1 MiB."""
    kept = bytearray()
    truncated = False
    error = None
    try:
        while True:
            chunk = stream.read(8192)
            if not chunk:
                break
            remaining = CAPTURE_LIMIT_BYTES - len(kept)
            if remaining > 0:
                kept.extend(chunk[:remaining])
            if len(chunk) > remaining:
                truncated = True
    except BaseException as caught:
        error = caught
        failed_event.set()
    finally:
        try:
            stream.close()
        except BaseException as caught:
            if error is None:
                error = caught
                failed_event.set()
    result.append((bytes(kept), truncated, error))


def _kill_and_reap_group(proc, pgid, label):
    """SIGKILL a guarded group and confirm both leader and anchor are gone."""
    last_error = None
    for _attempt in range(2):
        _terminate_process_group(proc, pgid)
        try:
            proc.wait(timeout=5)
        except (subprocess.TimeoutExpired, OSError) as error:
            last_error = error
        deadline = time.monotonic() + 5
        while _process_group_exists(pgid) and time.monotonic() < deadline:
            _terminate_process_group(proc, pgid)
            time.sleep(0.01)
        if proc.returncode is not None and not _process_group_exists(pgid):
            return
    detail = f": {last_error}" if last_error is not None else ""
    raise RuntimeError(
        f"{label}: could not confirm guarded process-group reap{detail}"
    )


def run_captured(command, limit_mb, timeout_s, label="harness", env=None,
                 input_text=None, cancel_event=None, cwd=None):
    """Run and capture one child under the exact process-group RSS envelope.

    This is the shared sequential-harness path. It keeps the same process-tree
    timeout and zero-grace memory semantics as ``run_guarded`` while returning
    stdout/stderr for verdict parsing. Callers must persist the plan that
    supplied ``limit_mb`` alongside any timings or solved counts.
    """
    if not command:
        raise ValueError("captured command must not be empty")
    if not limit_mb or limit_mb <= 0:
        raise ValueError("captured command requires a positive memory limit")
    if timeout_s is None or not math.isfinite(timeout_s) or timeout_s <= 0:
        raise ValueError("captured command requires a finite positive timeout")
    if os.name == "nt" or not hasattr(os, "killpg"):
        raise RuntimeError(
            "exact captured-run RSS enforcement requires POSIX process groups"
        )

    started = time.monotonic()
    proc, guard = guarded_popen(
        command,
        limit_mb,
        label=label,
        grace_mb=0,
        stdin=subprocess.PIPE if input_text is not None else subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=env,
        cwd=cwd,
    )
    pgid = proc.pid
    timed_out = False
    timeout_time_ns = None
    cancelled = False
    cancel_time_ns = None
    received_signal = [None, None]
    previous_handlers = {}
    capture_failed = threading.Event()
    stdout_result = []
    stderr_result = []
    stdout_thread = threading.Thread(
        target=_bounded_pipe_drain,
        args=(proc.stdout, stdout_result, capture_failed),
        name=f"{label}-stdout",
        daemon=True,
    )
    stderr_thread = threading.Thread(
        target=_bounded_pipe_drain,
        args=(proc.stderr, stderr_result, capture_failed),
        name=f"{label}-stderr",
        daemon=True,
    )
    stdout_thread.start()
    stderr_thread.start()
    input_thread = None
    if input_text is not None:
        input_bytes = input_text.encode("utf-8")

        def write_input():
            try:
                proc.stdin.write(input_bytes)
            except (BrokenPipeError, OSError):
                pass
            finally:
                proc.stdin.close()

        input_thread = threading.Thread(
            target=write_input,
            name=f"{label}-stdin",
            daemon=True,
        )
        input_thread.start()
    execution_deadline = time.monotonic() + timeout_s

    def terminate_on_parent_signal(signum, _frame):
        nonlocal cancelled, cancel_time_ns
        received_signal[0] = signum
        if received_signal[1] is None:
            received_signal[1] = time.monotonic_ns()
        cancel_time_ns = received_signal[1]
        cancelled = True
        _terminate_process_group(proc, pgid)

    if threading.current_thread() is threading.main_thread():
        for signum in (signal.SIGINT, signal.SIGTERM):
            previous_handlers[signum] = signal.getsignal(signum)
            signal.signal(signum, terminate_on_parent_signal)
    try:
        while proc.poll() is None:
            if capture_failed.is_set():
                _terminate_process_group(proc, pgid)
                break
            if cancel_event is not None and cancel_event.is_set():
                cancelled = True
                cancel_time_ns = time.monotonic_ns()
                _terminate_process_group(proc, pgid)
                break
            if time.monotonic() >= execution_deadline:
                timed_out = True
                timeout_time_ns = time.monotonic_ns()
                _terminate_process_group(proc, pgid)
                break
            time.sleep(0.01)
    finally:
        reaped = False
        try:
            _kill_and_reap_group(proc, pgid, label)
            reaped = True
        finally:
            # If SIGKILL could not be confirmed, retain the watchdog thread as
            # the last live enforcement mechanism while the exception escapes.
            if reaped:
                guard.stop()
            for signum, handler in previous_handlers.items():
                signal.signal(signum, handler)

    for thread in (stdout_thread, stderr_thread, input_thread):
        if thread is not None:
            thread.join(timeout=5)
    if stdout_thread.is_alive() or stderr_thread.is_alive() or (
        input_thread is not None and input_thread.is_alive()
    ):
        raise RuntimeError("captured child pipes did not close after process-group reap")

    stdout_bytes, stdout_truncated, stdout_error = (
        stdout_result[0] if stdout_result else (b"", True, "capture produced no result")
    )
    stderr_bytes, stderr_truncated, stderr_error = (
        stderr_result[0] if stderr_result else (b"", True, "capture produced no result")
    )
    if stdout_error is not None or stderr_error is not None:
        raise RuntimeError(
            f"{label}: bounded pipe capture failed: "
            f"stdout={stdout_error!r}, stderr={stderr_error!r}"
        )

    returncode = proc.returncode if proc.returncode is not None else -1
    cause = _first_termination_cause(
        breach_time_ns=guard.breach_time_ns,
        timeout_time_ns=timeout_time_ns,
        cancel_time_ns=cancel_time_ns,
    )
    if cause == "cancel" and received_signal[0] is not None:
        returncode = 128 + received_signal[0]
    cancelled = cause == "cancel"

    return CapturedRun(
        stdout=stdout_bytes.decode("utf-8", errors="replace"),
        stderr=stderr_bytes.decode("utf-8", errors="replace"),
        returncode=returncode,
        timed_out=cause == "timeout",
        memout=cause == "memout",
        wall_sec=time.monotonic() - started,
        stdout_truncated=stdout_truncated,
        stderr_truncated=stderr_truncated,
        cancelled=cancelled,
    )


def warn_concurrent_build():
    """Refuse if a Cargo/Targo compiler build looks active — concurrent sweeps
    with heavy LTO builds triggered the 2026-06-19 and 2026-07-11 watchdog
    panics."""
    n = count_active_rustc()
    if n >= 1:
        message = (
            f"[oom-guard] REFUSING: {n} build-driver/compiler process(es) are running — a Cargo/Targo build "
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
    w.add_argument("--ready-file", default=None,
                   help="write 'ready' after the watchdog is armed")
    w.add_argument("--ready-stdout", action="store_true",
                   help=argparse.SUPPRESS)
    r = sub.add_parser(
        "run",
        help="run a command under rss_watchdog and an optional wall timeout",
    )
    r.add_argument("--limit-mb", type=int, required=True)
    r.add_argument("--timeout-s", type=float, default=None)
    r.add_argument("--label", default="shell-harness")
    r.add_argument("command", nargs=argparse.REMAINDER)
    x = sub.add_parser(
        "exec-stopped",
        help=argparse.SUPPRESS,
    )
    x.add_argument("--fsize-bytes", type=int, default=None,
                   help=argparse.SUPPRESS)
    x.add_argument("command", nargs=argparse.REMAINDER)
    lease = sub.add_parser("lease", help=argparse.SUPPRESS)
    lease.add_argument("--label", default="native-harness")
    lease.add_argument("--test-lock-path", default=None, help=argparse.SUPPRESS)
    sub.add_parser("watch-server", help=argparse.SUPPRESS)
    args = ap.parse_args(argv)
    if args.cmd == "plan":
        if args.jobs <= 0:
            ap.error("plan --jobs must be positive")
        if args.mem_floor_mb <= 0:
            ap.error("plan --mem-floor-mb must be positive")
        if args.headroom_mb is not None and args.headroom_mb < 0:
            ap.error("plan --headroom-mb must be non-negative")
        if args.warn_concurrent_build:
            warn_concurrent_build()
        plan = plan_solver_resources(args.jobs, headroom_mb=args.headroom_mb,
                                     mem_floor_mb=args.mem_floor_mb, label=args.label,
                                     acquire_lease=False)
        print(f"PLAN_JOBS={plan.jobs}")
        print(f"PLAN_MEMLIMIT_MB={plan.memlimit_mb}")
        print(f"PLAN_NBCORE={plan.nbcore}")
        print(f"PLAN_HEADROOM_MB={plan.headroom_mb}")
        return 0
    if args.cmd == "lease":
        acquire_harness_lease(args.label, _lock_path=args.test_lock_path)
        print("AY_OOM_HARNESS_LEASE_READY_V1", flush=True)
        # The Rust owner holds stdin open for the complete benchmark campaign.
        # EOF releases the process-scoped flock through normal interpreter exit.
        while sys.stdin.buffer.read(8192):
            pass
        return 0
    if args.cmd == "watch-server":
        serve_watchdog_requests(sys.stdin.buffer, sys.stdout.buffer)
        return 0
    if args.cmd == "watch":
        if args.limit_mb <= 0:
            ap.error("watch requires --limit-mb > 0")
        if args.poll_s is not None and (
                not math.isfinite(args.poll_s) or args.poll_s <= 0):
            ap.error("watch --poll-s must be finite and positive")
        if args.grace_mb < 0:
            ap.error("watch --grace-mb must be non-negative")
        breached, breach_time_ns = watch_existing_process(
            args.pid,
            args.limit_mb,
            label=args.label,
            poll_s=args.poll_s,
            grace_mb=args.grace_mb,
            ready_file=args.ready_file,
            ready_stdout=args.ready_stdout,
            return_details=True,
        )
        if args.ready_stdout and breached:
            if breach_time_ns is None:
                raise RuntimeError("watchdog breach is missing its monotonic timestamp")
            print(f"AY_OOM_WATCHDOG_BREACH_NS={breach_time_ns}", flush=True)
        return WATCHDOG_BREACH_EXIT if breached else 0
    if args.cmd == "exec-stopped":
        command = args.command[1:] if args.command[:1] == ["--"] else args.command
        if not command:
            ap.error("exec-stopped requires a command after --")
        if os.name == "nt" or not hasattr(os, "kill") or not hasattr(os, "fork"):
            ap.error("exec-stopped requires POSIX signals and fork")
        if args.fsize_bytes is not None:
            if args.fsize_bytes <= 0:
                ap.error("exec-stopped --fsize-bytes must be positive")
            try:
                import resource
                resource.setrlimit(
                    resource.RLIMIT_FSIZE,
                    (args.fsize_bytes, args.fsize_bytes),
                )
            except (ImportError, OSError, ValueError) as error:
                ap.error(f"cannot apply RLIMIT_FSIZE: {error}")
        # Confirm the PGID anchor first, then stop before exec. The target
        # executable still cannot allocate or exit in the attach window, and
        # even anchor-setup failure cannot leave an unleased post-reap PGID.
        _spawn_process_group_anchor()
        os.kill(os.getpid(), signal.SIGSTOP)
        os.execvpe(command[0], command, os.environ)
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        ap.error("run requires a command after --")
    if args.limit_mb <= 0:
        ap.error("run requires --limit-mb > 0")
    if args.timeout_s is not None and (
            not math.isfinite(args.timeout_s) or args.timeout_s <= 0):
        ap.error("run --timeout-s must be finite and positive")
    return run_guarded(command, args.limit_mb, timeout_s=args.timeout_s,
                       label=args.label)


if __name__ == "__main__":
    sys.exit(_cli(sys.argv[1:]))
