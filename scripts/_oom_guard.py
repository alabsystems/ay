# ay-script: oom-guard
"""OOM guard for the benchmark sweep harnesses and the differential gate.

Aggregate admission control for harness children: cap concurrency so N solver
processes cannot overcommit RAM, hand every child an explicit MEMLIMIT/NBCORE
budget, and admit a campaign only when the host can hold it. WARNING:
unbounded concurrent sweeps and builds have overcommitted RAM to the point of
hard OOM / kernel watchdog panics (2026-06-19 and 2026-07-11: sweeps beside
heavy LTO builds; 2026-07-30: nine solver children on a 24 GB host under plans
that each admitted two) — keep the budgets honest.

Pure stdlib, no third-party deps; automatic planning fails closed if RAM cannot
be detected.

Admission, by caller:
  * :func:`admit_campaign` (the differential gate) admits on MEASURED RAM
    headroom. It reads available memory and kernel memory pressure
    ``ADMISSION_SAMPLES`` times, ``ADMISSION_INTERVAL_S`` apart, and admits only
    if every reading was measurable, none was critical, and
        min(available) >= jobs * memlimit_mb + harness_mb + margin_mb
    where ``memlimit_mb`` is the per-child cap the harness actually ENFORCES
    (rss_watchdog's zero-grace kill threshold), ``harness_mb`` is the harness's
    measured peak RSS plus the bounded capture buffers its children can fill,
    and ``margin_mb = ceil(physical RAM / 8)`` is room for peers to GROW after
    the reading: 16 GiB on a 128 GiB host, 3 GiB on a 24 GiB one. The margin
    scales with the host and has no absolute floor: the old floor (16 GiB,
    sized for a shared 128 GiB host) was two thirds of a 24 GiB host's RAM and
    refused every run there at 10-15 GiB available with pressure normal
    (the development design notes DR-43). The planner sizes that cap into the measured
    room (``reserve_mb = margin + harness``), so on a busy host the per-child
    caps shrink instead of the run refusing; it refuses only when not even one
    ``mem_floor_mb`` child fits. During the campaign :class:`MemoryPressureWatch`
    polls pressure; at critical (or when pressure stops being measurable) it
    stops the campaign's children (SIGTERM, SIGKILL after
    ``PRESSURE_TERMINATE_GRACE_S``) and the gate reports COULD NOT RUN, never
    PASS or FAIL. Every sample, the envelope, the margin, the decision and the
    pressure trace go into the run's record.
  * :func:`warn_concurrent_build` (the sweep harnesses and ``plan
    --warn-concurrent-build``) still refuses while any Cargo/Targo build or
    compiler is running. Those harnesses run no pressure watch, and the watch is
    the condition under which the build veto may go: a harness drops the veto by
    adopting admit_campaign + MemoryPressureWatch, never by deleting the call.

Why the gate no longer vetoes on "any compiler running": on a shared 128 GiB
host a compiler is running somewhere nearly all the time, so the veto starved
every differential gate run for hours while tens of GiB sat free (measured
2026-10-02/03: the FP-sweep gate waited ~3 h, its review gate ~3 h, the QSAT
gate 2 h+ with zero admission windows). A compiler's memory is part of what
admission measures, its growth is what the margin is for, and a host that runs
short anyway is what the pressure watch catches. The incidents above are why
per-child MEMLIMIT/rss_watchdog enforcement, the host lease and the concurrency
cap all stay exactly as they were: the gate's caps are sized into the measured
room and enforced the same way.

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
campaign for one host user contends on the same RAM-admission lock. That lease
records its owner's pid; a lease whose recorded owner is DEAD is reclaimed and
logged (see :func:`acquire_harness_lease`), because a leaked lease refuses every
later run without protecting anything.
"""
import collections
import atexit
import dataclasses
import enum
import errno
import json
import math
import os
import queue
import re
import select
import signal
import subprocess
import sys
import threading
import time
import typing


# THE INTERPRETER FLOOR. This module is executed as a bare ``python3`` by
# ``ay-bisect`` (``Command::new("python3")`` in crates/ay-bisect/src/resource.rs,
# which also EMBEDS this file as the authoritative planner) and by the shell
# harnesses, so the oldest ``python3`` a supported host resolves to is the floor:
# a stock macOS ships /usr/bin/python3 as 3.9.x and installs nothing newer.
#
# It is therefore a hard constraint, not a preference: no syntax and no stdlib
# newer than 3.9 may be used here. In particular a PEP 604 ``X | None``
# annotation is a RUNTIME expression -- it parses on 3.9 and raises
# ``TypeError: unsupported operand type(s) for |`` when the class body executes,
# which is exactly how this floor was broken once (``CapturedRun.guard_evidence``).
# Spell optionals ``typing.Optional[X]``.
#
# Where this repo genuinely needs a newer interpreter it says so and PROBES for
# one instead of assuming ``python3`` (publish/transforms.sh,
# competition/pb/package.sh and scripts/ci/trust_verification_ratchet_gate.sh all
# need ``tomllib``, i.e. 3.11+). This module deliberately does not, because an
# admission planner that cannot start is an admission planner that is not
# enforcing anything.
#
# `ay-bisect`'s `embedded_planner_runs_on_the_declared_interpreter_floor` is the
# gate that keeps this true; it fails the build, it never skips.
MIN_PYTHON = (3, 9)
if sys.version_info < MIN_PYTHON:
    raise SystemExit(
        "_oom_guard.py requires Python >= {}.{}; this interpreter is {} at {}. "
        "Point PATH (or the harness) at a newer python3; this script is the "
        "authoritative admission planner and refuses to run degraded.".format(
            MIN_PYTHON[0],
            MIN_PYTHON[1],
            ".".join(str(n) for n in sys.version_info[:3]),
            sys.executable,
        )
    )


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


def host_available_ram_mb():
    """Currently reclaimable host memory in MiB, or 0 when it cannot be read.

    This is a LIVE reading, not a capacity, and it is the signal
    :func:`plan_solver_resources` was missing. That planner reserves
    ``headroom_mb`` out of TOTAL RAM, which describes an otherwise-idle host —
    precisely the assumption that fails when a second campaign, an agent, or an
    editor is already resident. Two passes that each plan that way commit twice
    the machine, which is how nine solver children were live on 2026-07-30 under
    plans that each admitted two.

    Returns 0 for "unknown", which leaves the static plan untouched. A counter we
    cannot read must not refuse every run on that platform — the static budget is
    still applied, so this can only ever make a plan smaller, never larger.
    Admission (:func:`admit_campaign`) reads :func:`host_available_ram_reading`
    instead, where unknown is ``None`` and refuses.
    """
    reading = host_available_ram_reading()
    return 0 if reading is None else reading


# Where the available-memory figure comes from, for the admission record.
AVAILABLE_RAM_SOURCE = (
    "vm_stat: Pages free + speculative + inactive + purgeable"
    if sys.platform == "darwin" else "/proc/meminfo MemAvailable"
)


def host_available_ram_reading():
    """Reclaimable host memory in MiB, or ``None`` when it cannot be measured.

    macOS: ``vm_stat``'s free + speculative + inactive + purgeable pages.
      * speculative IS counted: vm_stat prints ``Pages free`` as the kernel's
        ``free_count - speculative_count`` and ``speculative_count`` on its own
        row (system_cmds vm_stat.c), so speculative pages are free pages the
        kernel has merely read ahead into; adding them back is the kernel's own
        free count, not an optimistic extra.
      * inactive and purgeable are reclaimable without paging anything the
        owner is using. Purgeable pages also sit on the active/inactive queues,
        so the sum can overlap inactive by at most the purgeable count (hundreds
        of MiB where measured) — far inside the admission margin.
      * anonymous ``active`` pages are NOT reclaimable and are excluded on
        purpose; counting them would restore the very "host is empty"
        assumption this exists to remove. File-backed active pages are
        reclaimable but excluded too: conservative.
    Linux: ``MemAvailable`` from /proc/meminfo, the kernel's own estimate of
    memory available to a new workload without swapping.
    """
    if sys.platform == "darwin":
        try:
            out = subprocess.check_output(["vm_stat"], text=True,
                                          stderr=subprocess.DEVNULL, timeout=30)
        except Exception:
            return None
        page_size = 4096
        header = re.search(r"page size of (\d+) bytes", out)
        if header:
            page_size = int(header.group(1))
        pages = 0
        found = False
        for key in ("Pages free", "Pages inactive", "Pages speculative",
                    "Pages purgeable"):
            row = re.search(rf"^{key}:\s+(\d+)\.", out, re.MULTILINE)
            if row:
                pages += int(row.group(1))
                found = True
        return (pages * page_size) // (1024 * 1024) if found else None
    try:  # Linux
        with open("/proc/meminfo", "r", encoding="utf-8") as handle:
            for line in handle:
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) // 1024
    except Exception:
        return None
    return None


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


# One human-readable line, so `cat /tmp/ay-oom-guard-<uid>.lock` names the owner
# during an incident. `label` is free-form and therefore always last. Records
# written before the staleness check existed carry only `pid=` and `label=`;
# they still parse, with the extra fields defaulting to "unknown".
_LEASE_RECORD_MAX_BYTES = 4096
# How long a would-be reclaimer waits for the serializing reclaim lock before
# giving up and refusing. Reclaim work is a few syscalls, so this is only ever
# reached if a reclaimer itself wedged; refusing is the fail-closed answer.
_LEASE_RECLAIM_WAIT_S = 5.0


def _normalize_lease_token(token):
    """Whitespace-free, comparable form of a process start-time token."""
    if not token:
        return "-"
    return re.sub(r"\s+", "_", token.strip()) or "-"


def _harness_lease_record(pid, label):
    """Render the lease record written by the owner that holds the flock."""
    identity = _watch_process_identity(pid)
    start = _normalize_lease_token(identity[1] if identity else None)
    return f"pid={pid} acquired={int(time.time())} start={start} label={label}\n"


def _parse_harness_lease_record(text):
    """Parse a lease record, or ``None`` when it is absent or malformed.

    ``None`` means "owner unknown", and an unknown owner is NEVER grounds for
    reclaiming: a harness that has just O_CREATed the file and taken the flock
    but has not yet written its record is alive and holds the host.
    """
    line = text.split("\n", 1)[0].strip()
    if not line:
        return None
    tokens = line.split(" ")
    record = {}
    for index, token in enumerate(tokens):
        key, separator, value = token.partition("=")
        if not separator or not key:
            return None
        if key == "label":
            record["label"] = " ".join([value, *tokens[index + 1:]]).strip()
            break
        record[key] = value
    try:
        pid = int(record.get("pid", ""))
    except ValueError:
        return None
    if pid <= 0:
        return None
    record["pid"] = pid
    try:
        record["acquired"] = int(record.get("acquired", 0))
    except ValueError:
        record["acquired"] = 0
    record["start"] = record.get("start") or "-"
    record["label"] = record.get("label") or "?"
    return record


def _pid_is_alive(pid):
    """``kill -0`` semantics: False only when the PID provably does not exist."""
    try:
        os.kill(int(pid), 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        # The process exists; we merely may not signal it.
        return True
    except (OverflowError, ValueError, OSError):
        # Cannot tell. Fail closed — an unmeasurable owner counts as live.
        return True


def _harness_lease_owner_is_alive(record):
    """Whether the recorded lease owner is still the process that wrote it.

    `kill -0` is the primary test. The recorded start-time token is a strictly
    additional guard: without it, a dead owner whose PID has been recycled by an
    unrelated process would keep an abandoned lease "live" forever.

    Every uncertain answer resolves to "alive". Reclaiming a live campaign's
    lease is the one outcome this guard must never produce, and the cost of the
    opposite error is one extra refusal that the next attempt clears.
    """
    if record is None:
        return True
    if not _pid_is_alive(record["pid"]):
        return False
    recorded_start = record.get("start", "-")
    if recorded_start == "-":
        return True  # legacy record: PID liveness is all we have
    identity = _watch_process_identity(record["pid"])
    if identity is None:
        # `kill -0` just succeeded, so the PID exists; the start-time lookup
        # merely failed (or the owner exited in between). Either way this is a
        # measurement failure, not evidence of death.
        return True
    if identity[1] is None:
        return True  # platform exposes no start token; PID liveness only
    return _normalize_lease_token(identity[1]) == recorded_start


def _describe_lease_owner(record):
    """Owner description for the refusal / reclaim log lines."""
    if record is None:
        return "owner record unreadable"
    age = ""
    acquired = record.get("acquired", 0)
    if acquired:
        age = f" held={max(0, int(time.time()) - acquired)}s"
    return f"pid={record['pid']} label={record['label']}{age}"


def _resolve_harness_lease_path(lock_path):
    if lock_path is None:
        return _host_harness_lease_path()
    # Hidden dependency-injection seam for subprocess tests. Production
    # callers never override the stable host/user path above.
    resolved = os.fspath(lock_path)
    if not os.path.isabs(resolved):
        raise ValueError("test harness lease path must be absolute")
    return resolved


def _read_lease_record_text(fd):
    try:
        os.lseek(fd, 0, os.SEEK_SET)
        raw = os.read(fd, _LEASE_RECORD_MAX_BYTES)
    except OSError:
        return ""
    return raw.decode("utf-8", errors="replace")


def _reclaim_stale_harness_lease(lock_path, blocked_metadata, label):
    """Unlink a lease file whose recorded owner is gone. Returns True if it did.

    The kernel releases an flock when its holder dies, so a lease that is STILL
    held while its recorded owner is gone means an unrelated survivor inherited
    the descriptor (a forked, never-exec'd descendant, or an orphaned sidecar
    that outlived its harness). The campaign that planned against host RAM is
    over, so refusing forever protects nothing — it just wedges every later run
    (2026-08-24: a leaked lease naming a dead pid made every chc_baseline_compare
    run refuse before writing evidence, which read as a CHC regression). Only a
    stale-OWNER lease may be reclaimed; a live owner is still refused.

    Serialized through a sibling reclaim lock so two racing harnesses cannot
    both unlink and then each flock a different inode, which would admit two
    campaigns at once — precisely the overcommit this guard exists to prevent.
    """
    import fcntl
    import stat
    reclaim_path = f"{lock_path}.reclaim"
    flags = os.O_RDWR | os.O_CREAT
    flags |= getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    guard_fd = os.open(reclaim_path, flags, 0o600)
    try:
        guard_metadata = os.fstat(guard_fd)
        if (not stat.S_ISREG(guard_metadata.st_mode)
                or guard_metadata.st_uid != os.getuid()):
            raise RuntimeError(
                f"unsafe lease reclaim file metadata: {reclaim_path}"
            )
        deadline = time.monotonic() + _LEASE_RECLAIM_WAIT_S
        while True:
            try:
                fcntl.flock(guard_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                if time.monotonic() >= deadline:
                    return False
                time.sleep(0.05)
        # Re-verify everything under the reclaim lock: the file we are about to
        # unlink must still be the same inode we found blocked, still blocked,
        # and still owned by a process that is gone.
        try:
            check_fd = os.open(
                lock_path,
                os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
                | getattr(os, "O_NOFOLLOW", 0),
            )
        except FileNotFoundError:
            return False  # another harness already reclaimed it
        try:
            current = os.fstat(check_fd)
            if (current.st_dev, current.st_ino) != (
                    blocked_metadata.st_dev, blocked_metadata.st_ino):
                return False  # replaced already; contend for the new inode
            record = _parse_harness_lease_record(_read_lease_record_text(check_fd))
            if _harness_lease_owner_is_alive(record):
                return False
            try:
                fcntl.flock(check_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                pass
            else:
                # The kernel released it in the meantime: nothing is stale on
                # disk, and the ordinary contention path will now succeed.
                fcntl.flock(check_fd, fcntl.LOCK_UN)
                return False
            try:
                os.unlink(lock_path)
            except FileNotFoundError:
                return False  # raced with another reclaimer
        finally:
            os.close(check_fd)
    finally:
        os.close(guard_fd)
    # Never silently. A reclaim means an earlier campaign leaked its lease, and
    # the operator needs to see that in the same transcript as the run it let
    # through.
    print(
        f"[oom-guard] {label}: reclaimed the host resource lease {lock_path} — "
        f"its recorded owner ({_describe_lease_owner(record)}) is gone, so the "
        "surviving flock belongs to a leaked descriptor, not a live campaign.",
        file=sys.stderr, flush=True,
    )
    return True


def _open_harness_lease(lock_path, label, allow_reclaim):
    import fcntl
    import stat
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
            record = _parse_harness_lease_record(_read_lease_record_text(fd))
            if allow_reclaim and not _harness_lease_owner_is_alive(record):
                os.close(fd)
                fd = -1
                _reclaim_stale_harness_lease(lock_path, metadata, label)
                # Exactly one reclaim per acquisition: a second refusal is a
                # real live owner (or a racing reclaimer that won), never an
                # excuse to keep unlinking.
                return _open_harness_lease(lock_path, label, allow_reclaim=False)
            raise RuntimeError(
                "another AY benchmark harness already owns the host resource "
                f"lease ({_describe_lease_owner(record)})"
            ) from error
        lease = os.fdopen(fd, "r+", encoding="utf-8")
        fd = -1
        lease.seek(0)
        lease.truncate()
        lease.write(_harness_lease_record(os.getpid(), label))
        lease.flush()
        return lease
    finally:
        if fd >= 0:
            os.close(fd)


def acquire_harness_lease(label="harness", _lock_path=None):
    """Acquire one host-wide benchmark lease for this process.

    Per-child RSS caps do not protect against two independent harnesses each
    planning against the full host. Production planning therefore fails closed
    when another AY harness owns this exclusive lease. Explicit-RAM unit-policy
    calls skip the lease unless requested.

    A lease whose RECORDED OWNER is dead is reclaimed (and logged — never
    silently); a lease whose owner is alive is still refused. Age is recorded
    and reported but deliberately does NOT authorize expiry: legitimate races
    in this repo have run 20+ hours (chained division campaigns), so any age
    threshold short enough to clear a leak is short enough to evict a live
    campaign.
    Liveness of the owner is the only safe reclaim authority.
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
    lock_path = _resolve_harness_lease_path(_lock_path)
    lease = _open_harness_lease(lock_path, label, allow_reclaim=True)
    _ACTIVE_HARNESS_LEASE = lease
    return lease


def plan_solver_resources(jobs, ram_mb=None, cores=None, headroom_mb=None,
                          mem_floor_mb=1024, label="harness",
                          acquire_lease=None, available_mb=None,
                          reserve_mb=None):
    """Plan (jobs, memlimit_mb_per_job, nbcore_per_job) for a parallel harness.

    Pure given explicit `ram_mb`/`cores`/`available_mb` (injectable for tests);
    otherwise they are detected. Policy:
      * reserve `headroom_mb` (default: max(16 GiB, RAM/3)) for the OS,
        agents, and a possible concurrent cargo build;
      * clamp to memory that is actually free RIGHT NOW (`available_mb`), so a
        plan can never hand out capacity another tenant already holds, keeping
        `reserve_mb` of that free pool unallocated (default: one
        `mem_floor_mb`; :func:`admit_campaign` passes its peer-growth margin
        plus the harness itself, so the caps it enforces fit the room it
        measured);
      * split the remaining budget evenly across jobs as a per-child MEMLIMIT
        (MiB), never below `mem_floor_mb` — jobs are REDUCED rather than
        starving each child below the floor;
      * split physical cores evenly across the final jobs as NBCORE (min 1).

    Solver context: without MEMLIMIT each ay-pb child self-limits at phys/2,
    and the main `ay` binary at 85% of RAM — both sibling-blind, so N parallel
    children multiply them (the 2026-06-19 / 2026-07-11 panic arithmetic).

    The live clamp is what makes the plan composable. `ram_mb - headroom_mb`
    describes an idle host, so two campaigns planning independently each commit
    the whole machine; on 2026-07-30 that put nine solver children on a 24 GB
    host under plans that each admitted two, and the userspace watchdog panicked
    it. The exclusive lease below cannot close that on its own — it dies with the
    process that holds it, so a chain that plans once per phase leaves a gap
    between phases, and children wedged in the VM outlive the harness that
    planned them. Measuring what is free sees both.

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
    reserve_mb = mem_floor_mb if reserve_mb is None else int(reserve_mb)
    if reserve_mb < 0:
        raise ValueError("reserve_mb must be non-negative")
    detected_ram = ram_mb is None
    if acquire_lease is None:
        acquire_lease = detected_ram
    cgroup = None
    if detected_ram:
        ram_mb = physical_ram_mb()
        cgroup = cgroup_memory_mb()
        if available_mb is None:
            available_mb = host_available_ram_mb()
    if available_mb is not None:
        available_mb = int(available_mb)
        if available_mb < 0:
            raise ValueError("available_mb must be non-negative")
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
    # Memory another tenant already holds is not ours to hand out. Keep
    # `reserve_mb` of the free pool unallocated (by default one child's worth)
    # so the trimmed plan still leaves the machine room to breathe rather than
    # filling it exactly.
    if available_mb:
        live_budget = available_mb - reserve_mb
        if live_budget < budget:
            print(
                f"[oom-guard] {label}: {available_mb}MB free now, not the "
                f"{ram_mb}MB an idle host would offer; keeping {reserve_mb}MB "
                f"of it unallocated, trimming budget "
                f"{budget}MB -> {max(0, live_budget)}MB.",
                file=sys.stderr, flush=True,
            )
            budget = live_budget
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
    if not os.path.isdir(proc_root):
        # No procfs (macOS): fall back to `ps` for the same bounded pid/comm
        # rows. Failure here must not abort the caller's resource planning —
        # an empty row set means "no concurrent build detected", the safe
        # default for a warn-only check.
        import subprocess
        try:
            out = subprocess.run(
                ["ps", "-axo", "pid=,comm="],
                capture_output=True,
                text=True,
                timeout=10,
                check=True,
            ).stdout
        except Exception:
            return rows
        for line in out.splitlines()[:max_entries]:
            parts = line.split(None, 1)
            if len(parts) != 2:
                continue
            pid_s, comm = parts
            base = os.path.basename(comm.strip())
            if pid_s.isdigit() and base in wanted:
                rows.append((int(pid_s), base))
        return rows
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
            except OSError as error:
                # A listed process may exit before open OR while comm is read.
                # Only disappearance is benign; unreadable live entries fail.
                if error.errno in (errno.ENOENT, errno.ESRCH):
                    continue
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

    Hosts without a procfs (macOS) use an equivalent bounded ``ps`` scan so
    the concurrent-build refusal keeps protecting sweeps on every supported
    platform instead of crashing.
    """
    if proc_root == "/proc" and not os.path.isdir(proc_root):
        return _count_active_rustc_ps(ancestor_pids)
    processes = _named_build_processes(proc_root)
    inactive_states = {"Z", "T", "t", "X", "x"}
    count = sum(
        1 for pid, name in processes
        if name in ("rustc", "compiler_consumer")
        and _process_state(pid, proc_root=proc_root) not in inactive_states
    )
    build_commands = {
        "build", "check", "test", "run", "clippy", "tippy", "rustc", "bench",
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
        except OSError as error:
            # The driver can disappear between the name scan and this read.
            if error.errno in (errno.ENOENT, errno.ESRCH):
                continue
            raise RuntimeError(f"cannot inspect {name} process {pid}: {error}")
        tokens = command.split()
        if any(token in build_commands for token in tokens[1:]):
            count += 1
    return count


def _count_active_rustc_ps(ancestor_pids=None):
    """`count_active_rustc` for procfs-less hosts (macOS) via bounded ``ps``.

    Same contract: count live rustc/compiler_consumer compilers plus non-ancestor
    cargo/targo drivers running a build-like subcommand. Any inspection
    failure raises so callers keep their fail-closed refusal behavior.
    """
    wanted = {"cargo", "targo", "rustc", "compiler_consumer"}
    try:
        listing = subprocess.run(
            ["ps", "-axo", "pid=,state=,comm="],
            capture_output=True,
            timeout=30,
            check=True,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise RuntimeError(f"cannot inspect build processes via ps: {error}")
    lines = listing.stdout.decode("utf-8", errors="replace").splitlines()
    if len(lines) > 1_000_000:
        raise RuntimeError("process table exceeds fixed 1000000-entry inspection cap")
    inactive_states = {"Z", "T", "t", "X", "x"}
    rows = []
    for line in lines:
        parts = line.split(None, 2)
        if len(parts) != 3 or not parts[0].isdigit():
            continue
        pid, state, command_name = int(parts[0]), parts[1][:1], parts[2].strip()
        name = os.path.basename(command_name)
        if name in wanted and state not in inactive_states:
            rows.append((pid, name))
    count = sum(1 for _, name in rows if name in ("rustc", "compiler_consumer"))
    build_commands = {
        "build", "check", "test", "run", "clippy", "tippy", "rustc", "bench",
        "doc", "install", "fix",
    }
    ancestors = _ancestor_pids_ps() if ancestor_pids is None else set(ancestor_pids)
    for pid, name in rows:
        if name not in ("cargo", "targo") or pid in ancestors:
            continue
        try:
            detail = subprocess.run(
                ["ps", "-o", "command=", "-p", str(pid)],
                capture_output=True,
                timeout=30,
            )
        except (OSError, subprocess.SubprocessError) as error:
            raise RuntimeError(f"cannot inspect {name} process {pid}: {error}")
        if detail.returncode != 0:
            continue  # exited between the scan and the detail lookup
        command = detail.stdout.decode("utf-8", errors="replace")
        if len(command) > 64 * 1024:
            raise RuntimeError(f"{name} process {pid} has an oversized command line")
        tokens = command.split()
        if any(token in build_commands for token in tokens[1:]):
            count += 1
    return count


def _ancestor_pids_ps(pid=None):
    """Ancestor PID set via ``ps`` for procfs-less hosts (macOS)."""
    current = os.getpid() if pid is None else int(pid)
    ancestors = set()
    visited = set()
    while current > 1 and current not in visited:
        visited.add(current)
        try:
            detail = subprocess.run(
                ["ps", "-o", "ppid=", "-p", str(current)],
                capture_output=True,
                timeout=30,
            )
            parent = int(detail.stdout.decode("utf-8", errors="replace").strip())
        except (OSError, subprocess.SubprocessError, ValueError):
            break
        if parent <= 0 or parent == current:
            break
        ancestors.add(parent)
        current = parent
    return ancestors


def _ancestor_pids(pid=None):
    """Ancestor PID set, used to ignore the supervising cargo command."""
    if not os.path.isdir("/proc"):
        return _ancestor_pids_ps(pid)
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

    def terminate_gracefully_if_authenticated(self):
        return False


class _WatchPhase(enum.Enum):
    ACTIVE = "active"
    QUIESCING = "quiescing"
    QUIESCED = "quiesced"
    KILL_SENT = "kill-sent"
    GROUP_GONE = "group-gone"
    REAPED = "reaped"
    LOST = "identity-lost"
    ERROR = "monitor-error"


class GuardEnforcementError(RuntimeError):
    """The monitored lifecycle cannot justify an enforced command outcome."""


class _RssWatchdog:
    """Poll a child process group's RSS and SIGKILL it past `kill_mb`.

    See rss_watchdog() for the contract. Daemon thread; .stop() is idempotent.
    """

    def __init__(self, proc, pgid, kill_mb, poll_s, label, group_identity):
        self.armed = False
        self.breached = False
        self.breach_time_ns = None
        # Peak RSS the sampler actually observed, in MB (None if never sampled).
        #
        # Without this, NO banked run is auditable for envelope compliance. That
        # is not hypothetical: the SQ QF_Datatypes win of 2026-08-01 recorded
        # memlimit_mb 6954 and a SIGKILL watchdog, yet one of its solved
        # instances needs 9,477 MB — verified 2026-08-17 with /usr/bin/time -l.
        # Nothing in the banked rows could have revealed that, because peak RSS
        # was sampled and then thrown away. The sampler is already walking the
        # process group every poll; keeping the maximum is free.
        self.peak_rss_mb = None
        self._proc = proc
        self._pgid = pgid
        self._kill_mb = kill_mb
        self._poll_s = poll_s
        self._label = label
        self._group_identity = group_identity
        self._stop_evt = threading.Event()
        self._ready_evt = threading.Event()
        self._terminal_evt = threading.Event()
        self._lifecycle_lock = threading.RLock()
        self._phase = _WatchPhase.ACTIVE
        self._events = []
        self._worker_error = None
        self._kill_sent = False
        self._frozen_members = None
        self._owned_proc = None
        self.identity_lost = False
        self.identity_lost_time_ns = None
        self._thread = threading.Thread(target=self._watch, daemon=True)
        self._thread.start()
        if not self._ready_evt.wait(timeout=10):
            self._stop_evt.set()
            self._thread.join(timeout=10)
            raise RuntimeError(f"{label}: RSS watchdog thread did not start")
        self.armed = True
        with self._lifecycle_lock:
            self._event_locked("armed", identity=self._group_identity)

    # Consecutive failed measurements before we assume the worst and kill. At
    # POLL_DEFAULT this is ~0.1s of blindness; the alternative (keep polling and
    # hope) is what disarmed the guard during the 07-11 swap storm.
    _MAX_UNKNOWN = 5

    def _same_group(self):
        """Authenticate the watched PGID before observing or signalling it."""
        return _group_identity_is_current(self._pgid, self._group_identity)

    def _event_locked(self, kind, **details):
        self._events.append({"kind": kind, "time_ns": time.monotonic_ns(), **details})

    def evidence(self):
        """Snapshot state protected by the same lock as sampling and shutdown."""
        with self._lifecycle_lock:
            return {"phase": self._phase.value, "group_identity": self._group_identity,
                    "identity_lost": self.identity_lost,
                    "identity_lost_time_ns": self.identity_lost_time_ns,
                    "peak_rss_mib": self.peak_rss_mb, "kill_threshold_mib": self._kill_mb,
                    "poll_seconds": self._poll_s, "breached": self.breached,
                    "breach_time_ns": self.breach_time_ns,
                    "worker_error": self._worker_error,
                    "events": [dict(event) for event in self._events]}

    def _retain_authenticated_group(self):
        # Call only under _lifecycle_lock. Never turn an earlier loss into success.
        if self.identity_lost:
            return False
        if self._same_group():
            return True
        # A genuinely absent WHOLE group has no remaining member to monitor.
        # A failed identity lookup while a group exists/inspection is uncertain
        # is different: it must not be reported as completion.
        if not _process_group_exists(self._pgid):
            self._phase = _WatchPhase.GROUP_GONE
            self._event_locked("whole-group-absent")
            return False
        if _group_has_exited(self._pgid):
            self._phase = _WatchPhase.GROUP_GONE
            self._event_locked("whole-group-exited")
            return False
        # The last zombie's parent can reap it between the probe above and
        # that member listing, which then finds no member at all
        # (`_group_has_ended`). Probe again before calling the identity lost.
        if not _process_group_exists(self._pgid):
            self._phase = _WatchPhase.GROUP_GONE
            self._event_locked("whole-group-reaped")
            return False
        self.identity_lost = True
        self.identity_lost_time_ns = time.monotonic_ns()
        self._phase = _WatchPhase.LOST
        self._event_locked("identity-lost", identity=self._group_identity)
        print(f"[oom-guard] {self._label}: lost authenticated group identity "
              f"for pgid {self._pgid}; refusing an enforced result.",
              file=sys.stderr, flush=True)
        return False

    def check_enforcement(self):
        with self._lifecycle_lock:
            stopped_early = (self._terminal_evt.is_set()
                             and self._phase in (_WatchPhase.ACTIVE, _WatchPhase.QUIESCING))
            if self.identity_lost or self._worker_error is not None or stopped_early:
                raise GuardEnforcementError(
                    f"{self._label}: enforcement lost: {self.evidence()}"
                )

    def wait_terminal(self, timeout=None):
        """Wait until the monitor breaches, stops, or loses its identity."""
        return self._terminal_evt.wait(timeout)

    def terminate_if_authenticated(self):
        """Kill only while the originally captured group identity is current."""
        with self._lifecycle_lock:
            return self._kill_authenticated_locked("abort")

    def terminate_gracefully_if_authenticated(self):
        """SIGTERM the group, only while its captured identity is current.

        The polite first half of a campaign stop (see
        :class:`MemoryPressureWatch`): the solver may exit on its own. It does
        not end the lifecycle: the owner still calls :meth:`finish`, which
        SIGKILLs whatever remains (exec-stopped's anchor ignores SIGTERM by
        design) and reaps. Never SIGABRT: that writes crash reports.
        """
        with self._lifecycle_lock:
            if self._kill_sent or self._phase is not _WatchPhase.ACTIVE:
                return False
            if not self._same_group():
                self._retain_authenticated_group()
                return False
            try:
                os.killpg(self._pgid, signal.SIGTERM)
            except ProcessLookupError:
                return False
            self._event_locked("authenticated-terminate", signal="SIGTERM")
            return True

    def _kill_authenticated_locked(self, cause):
        if self._kill_sent or self._phase in (_WatchPhase.GROUP_GONE, _WatchPhase.REAPED):
            return False
        # Cleanup may re-authenticate the SAME identity after a transient lookup
        # failure, but identity_lost stays true and still refuses the result.
        if not self._same_group():
            self._retain_authenticated_group()
            return False
        os.killpg(self._pgid, signal.SIGKILL)
        self._kill_sent = True
        self._phase = _WatchPhase.KILL_SENT
        self._event_locked("authenticated-kill", cause=cause)
        self._stop_evt.set()
        return True

    def _watch(self):
        self._ready_evt.set()
        unknown = 0
        try:
            while not self._stop_evt.wait(self._poll_s):
                with self._lifecycle_lock:
                    if self._phase not in (_WatchPhase.ACTIVE, _WatchPhase.QUIESCING):
                        return
                    if not self._retain_authenticated_group():
                        return
                    rss = process_group_rss_mb(self._pgid)
                    if rss is None:
                        if not self._retain_authenticated_group():
                            return
                        unknown += 1
                        if unknown < self._MAX_UNKNOWN:
                            continue
                        reason = f"cannot measure RSS ({unknown} consecutive failures; fail-closed)"
                    else:
                        unknown = 0
                        if self.peak_rss_mb is None or rss > self.peak_rss_mb:
                            self.peak_rss_mb = rss
                        if rss <= self._kill_mb:
                            continue
                        reason = f"RSS {rss}MB breached {self._kill_mb}MB"
                    if not self._retain_authenticated_group():
                        return
                    self.breach_time_ns = time.monotonic_ns()
                    self.breached = True
                    self._event_locked("memory-breach", reason=reason)
                    print(f"[oom-guard] {self._label}: {reason}; killing the "
                          f"authenticated process group {self._pgid} (memout).",
                          file=sys.stderr, flush=True)
                    # This is a distinct, authenticated terminal transition.
                    # The sampler never reclassifies its own kill as identity loss.
                    self._kill_authenticated_locked("memout")
                    return
        except BaseException as error:
            with self._lifecycle_lock:
                self._worker_error = repr(error)
                self._phase = _WatchPhase.ERROR
                self._event_locked("monitor-error", error=repr(error))
        finally:
            self._terminal_evt.set()

    def finish(self, proc, label=None):
        """Quiesce while monitored, join the monitor, then kill/reap exactly once.

        An earlier identity/monitor error is sticky even if authenticated cleanup
        subsequently succeeds. No raw numeric PGID is signalled after its captured
        identity disappears. This API does not resume a stopped group.
        """
        label = self._label if label is None else label
        if proc is not self._owned_proc:
            raise GuardEnforcementError(f"{label}: completion supplied a different process owner")
        cleanup_error = None
        try:
            deadline = time.monotonic() + _GROUP_SETTLE_S
            previous = None
            while True:
                with self._lifecycle_lock:
                    if self.identity_lost or self._worker_error is not None:
                        self._kill_authenticated_locked("enforcement-error-cleanup")
                        break
                    if self._phase in (_WatchPhase.KILL_SENT, _WatchPhase.GROUP_GONE,
                                       _WatchPhase.REAPED):
                        break
                    if self._phase == _WatchPhase.QUIESCED:
                        break
                    if not self._retain_authenticated_group():
                        continue
                    self._phase = _WatchPhase.QUIESCING
                    # Keep the sampler armed during SIGSTOP and quiescence checks.
                    os.killpg(self._pgid, signal.SIGSTOP)
                    self._event_locked("authenticated-stop")
                members = _stopped_group_snapshot(self._pgid, self._group_identity)
                with self._lifecycle_lock:
                    if self._phase != _WatchPhase.QUIESCING:
                        continue
                    if not self._retain_authenticated_group():
                        continue
                    if members is not None and members == previous:
                        self._frozen_members = members
                        self._phase = _WatchPhase.QUIESCED
                        self._event_locked("group-quiesced", members=members)
                        self._stop_evt.set()
                        break
                    previous = members
                if time.monotonic() >= deadline:
                    raise GuardEnforcementError(f"{label}: cannot confirm whole-group quiescence")
                time.sleep(0.01)

            self.stop()
            with self._lifecycle_lock:
                self._event_locked("monitor-joined")
                if self._phase == _WatchPhase.QUIESCED:
                    if _stopped_group_snapshot(self._pgid, self._group_identity) != self._frozen_members:
                        raise GuardEnforcementError(f"{label}: stopped group changed before final kill")
                    if not self._kill_authenticated_locked("completed-quiescence"):
                        raise GuardEnforcementError(f"{label}: final group identity unavailable")
            # Never repeat killpg after identity/PGID lease destruction.
            _reap_group_without_signalling(proc, self._pgid, label)
            with self._lifecycle_lock:
                self._phase = _WatchPhase.REAPED
                self._event_locked("group-reaped")
        except BaseException as error:
            cleanup_error = error
            # Best effort while the exact original identity remains available.
            # Failure stays failure, including a stopped but unkillable group.
            try:
                self.terminate_if_authenticated()
                if self._kill_sent or not _process_group_exists(self._pgid):
                    _reap_group_without_signalling(proc, self._pgid, label)
                    self.stop()
            except BaseException as secondary:
                if hasattr(error, "add_note"):
                    error.add_note(f"authenticated cleanup also failed: {secondary}")
        self.check_enforcement()
        if cleanup_error is not None:
            raise cleanup_error
        return self.evidence()

    def stop(self):
        with self._lifecycle_lock:
            if self._phase in (_WatchPhase.ACTIVE, _WatchPhase.QUIESCING):
                if (not self.identity_lost and self._worker_error is None
                        and _group_has_ended(self._pgid)):
                    self._phase = _WatchPhase.GROUP_GONE
                    self._event_locked("whole-group-absent-at-stop")
                else:
                    self._worker_error = self._worker_error or "monitor stopped before authenticated completion"
                    self._phase = _WatchPhase.ERROR
                    self._event_locked("monitor-stopped-early")
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


# How long the guard waits for the kernel to show a process group's state: a hang
# detector, not a latency budget. It bounds each `ps` listing that authenticates or
# observes a member (the listing that picks a new group's identity included), the wait
# for a new guarded child to stop itself for attach, the wait for a stopped group to
# show quiescent, and the reap after the final kill. On this repository's shared hosts
# that can take well over 5 s: in a differential gate run at load 145, solver runs that
# finish in about 2 s took 20-23 s of wall time, and the next completion could not show
# a quiesced group within the 5 s these waits used to be (`cannot confirm whole-group
# quiescence`); at load 183 the listing itself outran 5 s (`cannot inspect stopped
# group ...: timed out after 5 seconds`). Each cancelled the whole campaign. A longer
# wait proves nothing more or less: the same listing must still show the same stopped
# members twice, a completing group stays stopped with its RSS monitor armed while it
# waits, and a group that never settles still fails, after this long. In the monitor, a
# member's identity listing that timed out read as a lost identity, which ends
# enforcement of that group for good; waiting for the listing keeps it. At spawn
# nothing runs unwatched while the guard waits: the child is the exec-stopped wrapper,
# which execs the command only after the monitor is armed and the group resumed, and
# the child's own budget starts at that resume (run_captured). Those two spawn waits
# had 10 s, and at load 120 a generator the gate had already stopped and identified
# once failed its second identity listing (`differential-generator: cannot
# authenticate process-group identity`); during a host stall a test run saw `guarded
# child did not stop for attach`. The same identity listing writes the host lease's
# owner record and checks a recorded owner's start time, where every doubt already
# reads as "alive": there a slow `ps` costs latency, never a reclaimed lease.
_GROUP_SETTLE_S = 60.0


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


def _group_has_exited(pgid):
    """Whether every remaining member of ``pgid`` is a zombie awaiting its reap.

    An exited child that its parent has not yet reaped still holds its process
    group (``killpg(pgid, 0)`` succeeds) while ``getpgid`` on it fails with
    ESRCH (macOS), so the authenticated-identity check reads the child's
    ordinary exit as a lost identity. An all-zombie group runs nothing and
    holds no memory, and its PGID cannot be reused while any member remains,
    so it has exited. Any doubt (a failed listing, a live member) is False.
    """
    try:
        listing = subprocess.run(
            ["ps", "-axo", "pid=,pgid=,stat="], capture_output=True, text=True,
            timeout=_GROUP_SETTLE_S, check=True,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    members = [
        fields for fields in (line.split() for line in listing.stdout.splitlines())
        if len(fields) == 3 and fields[1] == str(int(pgid))
    ]
    return bool(members) and all(fields[2][:1] in ("Z", "X", "x") for fields in members)


def _group_has_ended(pgid):
    """Whether ``pgid`` has ended: no member left, or only zombies awaiting reap.

    Three observations, in this order: the group exists; its members are all
    zombies (``_group_has_exited``); the group exists still. The parent reaps
    the last zombie when it chooses, which is often between the first probe
    and the member listing: the probe finds the group (on macOS ``killpg``
    answers EPERM for a zombie-only group), and the ``ps`` listing then finds
    no member at all, which by itself is not an exit (measured 2026-09-29 on
    macOS: 274 of 300 children their parent reaped at once went that way).
    A group the last probe no longer finds has ended, as the first probe would
    have said a moment later. Anything else, including a listing that cannot
    be read or a member that is not a zombie, has not ended.
    """
    return (not _process_group_exists(pgid)
            or _group_has_exited(pgid)
            or not _process_group_exists(pgid))


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


def _stopped_group_snapshot(pgid, group_identity):
    """Return exact stopped/zombie member identities, including the armed member.

    Failure or an observed runnable member does not prove quiescence. Two equal
    snapshots are required by finish, while repeated group SIGSTOP and the RSS
    monitor remain active. A stopped member cannot itself spawn a missed child;
    the next complete inventory observes children created during stop delivery.
    """
    try:
        listing = subprocess.run(
            ["ps", "-axo", "pid=,pgid=,stat="], capture_output=True, text=True,
            timeout=_GROUP_SETTLE_S, check=True,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise GuardEnforcementError(f"cannot inspect stopped group {pgid}: {error}") from error
    lines = listing.stdout.splitlines()
    if len(lines) > 1_000_000:
        raise GuardEnforcementError("stopped-group snapshot exceeds process-table cap")
    members = []
    seen_pids = set()
    for line in lines:
        fields = line.split()
        if len(fields) != 3 or not fields[0].isdigit() or not fields[1].isdigit():
            raise GuardEnforcementError("malformed stopped-group process row")
        pid, candidate_pgid = int(fields[0]), int(fields[1])
        if pid in seen_pids:
            raise GuardEnforcementError("duplicate PID in stopped-group snapshot")
        seen_pids.add(pid)
        if candidate_pgid != int(pgid):
            continue
        if fields[2][:1] not in ("T", "t", "Z", "X", "x"):
            return None
        identity = _watch_process_identity(pid)
        if identity is None or _safe_getpgid(pid) != int(pgid):
            return None
        members.append(identity)
    frozen = tuple(sorted(members))
    return frozen if group_identity in frozen else None


def _reap_group_without_signalling(proc, pgid, label):
    """Confirm exit after a single authenticated signal; never signal a new PGID."""
    try:
        proc.wait(timeout=_GROUP_SETTLE_S)
    except (subprocess.TimeoutExpired, OSError) as error:
        raise GuardEnforcementError(f"{label}: could not reap guarded leader") from error
    deadline = time.monotonic() + _GROUP_SETTLE_S
    while _process_group_exists(pgid) and time.monotonic() < deadline:
        time.sleep(0.01)
    if _process_group_exists(pgid):
        raise GuardEnforcementError(f"{label}: could not confirm whole-group disappearance")


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
        guard.check_enforcement()
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
# How long the command reader may sit in one poll before it re-checks
# `closing`. It bounds teardown, not latency: a readable pipe wakes the
# poll immediately, so this only decides how long a QUIET reader takes to
# notice the server is shutting down.
WATCH_SERVER_READ_POLL_S = 0.1


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


def _watch_server_command_lines(input_stream, closing):
    """Read bounded protocol lines while allowing an idle pipe to stop."""
    try:
        fd = input_stream.fileno() if os.name != "nt" else None
    except (AttributeError, OSError, ValueError):
        fd = None
    if fd is None:
        # In-memory test streams and the existing Windows stream path.
        while not closing.is_set():
            command = input_stream.readline(WATCH_SERVER_MAX_COMMAND_BYTES + 1)
            yield command
            if not command:
                return
        return

    # The server owns an unread protocol pipe. Read its descriptor directly:
    # BufferedReader.readline can hide later complete commands from select,
    # or hold stdin's buffered lock forever while awaiting a partial line.
    pending = bytearray()
    while not closing.is_set():
        ready, _, _ = select.select([fd], [], [], WATCH_SERVER_READ_POLL_S)
        if not ready:
            continue
        chunk = os.read(fd, WATCH_SERVER_MAX_COMMAND_BYTES + 1 - len(pending))
        if not chunk:
            if pending:
                yield bytes(pending)
            yield b""
            return
        pending.extend(chunk)
        while not closing.is_set():
            end = pending.find(b"\n")
            if end < 0:
                break
            yield bytes(pending[:end + 1])
            del pending[:end + 1]
        if len(pending) > WATCH_SERVER_MAX_COMMAND_BYTES:
            # Preserve the main loop's refusal of overlong commands even if
            # the sender leaves its pipe open without sending a newline.
            yield bytes(pending)
            return


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
        # waits for another WATCH or arms a child monitor.
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
        try:
            for command in _watch_server_command_lines(input_stream, closing):
                commands.put(("command", command))
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
            guard.check_enforcement()
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
        # See read_commands: a reader still inside `readline` at interpreter
        # shutdown turns a clean run into SIGABRT.
        command_reader.join(timeout=WATCH_SERVER_READ_POLL_S * 4)
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
    """Cleanup with the launch-captured identity, never a newly observed PGID."""
    if (guard is not None and getattr(guard, "armed", False)
            and callable(getattr(guard, "finish", None))):
        guard.finish(proc, "failed guarded spawn")
    else:
        # A rejected no-op/unarmed monitor cannot issue a completion result.
        # The still-stopped wrapper has the independent launch-captured identity.
        _kill_and_reap_group(proc, pgid, "failed guarded spawn")
        if guard is not None:
            guard.stop()


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
            timeout=_GROUP_SETTLE_S,
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
                timeout=_GROUP_SETTLE_S,
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
    deadline = time.monotonic() + _GROUP_SETTLE_S
    while True:
        try:
            waited_pid, status = os.waitpid(proc.pid, os.WUNTRACED | os.WNOHANG)
        except ChildProcessError as error:
            raise GuardEnforcementError(f"{label}: guarded child vanished before attach") from error
        if waited_pid == 0:
            if time.monotonic() >= deadline:
                raise GuardEnforcementError(f"{label}: guarded child did not stop for attach")
            time.sleep(0.005)
            continue
        if os.WIFSTOPPED(status) and os.WSTOPSIG(status) == signal.SIGSTOP:
            return
        if os.WIFEXITED(status) or os.WIFSIGNALED(status):
            proc.returncode = os.waitstatus_to_exitcode(status)
        raise GuardEnforcementError(f"{label}: guarded child exited before attach")


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
    proc._guard_group_identity = _watch_process_identity(proc.pid)
    proc._guard_kill_sent = False
    try:
        if os.getpgid(proc.pid) != pgid:
            raise RuntimeError(f"{label}: guarded child is not its group leader")
        _wait_for_guard_stop(proc, pgid, label)
        # The stopped, unreaped leader pins this original group while its
        # persistent anchor identity is selected. Never learn identity at cleanup.
        proc._guard_group_identity = _group_watch_identity(pgid, proc.pid)
        if proc._guard_group_identity is None:
            raise GuardEnforcementError(f"{label}: stopped group identity unavailable")
    except BaseException:
        _kill_reap_failed_spawn(proc, pgid)
        raise
    guard = None
    try:
        watched = _AttachedProcess(proc.pid) if non_reaping_watch else proc
        guard = rss_watchdog(
            watched, limit_mb, label=label, grace_mb=grace_mb, poll_s=poll_s
        )
        guard._owned_proc = proc
        if not getattr(guard, "armed", False):
            raise RuntimeError(
                f"{label}: RSS watchdog did not arm; refusing to resume child"
            )
        with guard._lifecycle_lock:
            guard.check_enforcement()
            if guard._phase == _WatchPhase.KILL_SENT and guard.breached and guard._kill_sent:
                # The stopped wrapper itself can breach a tiny budget. Return
                # the genuine memout for owner cleanup without ever resuming it.
                return proc, guard
            if guard._phase != _WatchPhase.ACTIVE:
                raise GuardEnforcementError(f"{label}: monitor is not active before resume")
            if not guard._retain_authenticated_group():
                raise GuardEnforcementError(f"{label}: lost stopped group before resume")
            os.killpg(pgid, signal.SIGCONT)
            guard._event_locked("authenticated-resume")
    except BaseException:
        # The wrapper is still stopped if arming or SIGCONT failed. Kill it
        # before reaping so neither the process nor its PGID can escape/recycle.
        _kill_reap_failed_spawn(proc, pgid, guard)
        raise
    return proc, guard


def wait_guarded_exit(proc, guard, timeout_s=None, cancel_event=None):
    """Observe a child exit while promptly refusing a failed monitor."""
    if proc is not guard._owned_proc:
        raise GuardEnforcementError("wait supplied a different guarded process owner")
    deadline = None if timeout_s is None else time.monotonic() + timeout_s
    while True:
        guard.check_enforcement()
        returncode = proc.poll()
        if returncode is not None:
            guard.check_enforcement()
            return returncode
        if cancel_event is not None and cancel_event.is_set():
            return None
        if deadline is not None and time.monotonic() >= deadline:
            raise subprocess.TimeoutExpired(proc.args, timeout_s)
        time.sleep(0.01)


def run_guarded(command, limit_mb, timeout_s=None, label="harness"):
    """Run one command with authenticated monitored completion and tree timeout."""
    if not command:
        raise ValueError("guarded command must not be empty")
    if not limit_mb or limit_mb <= 0:
        raise ValueError("guarded command requires a positive memory limit")
    if timeout_s is not None and (
            not math.isfinite(float(timeout_s)) or timeout_s <= 0):
        raise ValueError("guarded command timeout must be finite and positive")
    if os.name == "nt" or not hasattr(os, "killpg"):
        raise RuntimeError("exact guarded execution requires POSIX process groups")
    proc, guard = guarded_popen(command, limit_mb, label=label, grace_mb=0)
    started = time.monotonic()  # the authenticated resume; see run_captured
    timeout_time_ns = None
    received_signal = [None, None]
    cancelled = threading.Event()
    previous_handlers = {}
    returncode = None
    execution_error = cleanup_error = None

    def terminate_on_parent_signal(signum, _frame):
        received_signal[0] = signum
        if received_signal[1] is None:
            received_signal[1] = time.monotonic_ns()
        cancelled.set()  # finish owns authenticated signalling, outside the handler.

    if threading.current_thread() is threading.main_thread():
        for signum in (signal.SIGINT, signal.SIGTERM):
            previous_handlers[signum] = signal.getsignal(signum)
            signal.signal(signum, terminate_on_parent_signal)
    try:
        try:
            remaining = None if timeout_s is None else max(0.0, timeout_s - (time.monotonic() - started))
            returncode = wait_guarded_exit(proc, guard, remaining, cancelled)
        except subprocess.TimeoutExpired:
            timeout_time_ns = time.monotonic_ns()
        except BaseException as error:
            execution_error = error
    finally:
        try:
            guard.finish(proc, label)
            if returncode is None:
                returncode = proc.returncode
        except BaseException as error:
            cleanup_error = error
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
    guard_evidence: typing.Optional[dict] = None

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
    """Failed-launch cleanup using only launch-captured identity; signal once."""
    identity = getattr(proc, "_guard_group_identity", None)
    if not getattr(proc, "_guard_kill_sent", False):
        if _group_identity_is_current(pgid, identity):
            os.killpg(pgid, signal.SIGKILL)
            proc._guard_kill_sent = True
        elif not _group_has_ended(pgid):
            raise GuardEnforcementError(f"{label}: original launch identity unavailable")
    _reap_group_without_signalling(proc, pgid, label)


def _terminate_then_wait(proc, guard, grace_s):
    """SIGTERM the authenticated group, then give its leader ``grace_s`` to exit.

    The caller's ``guard.finish`` then SIGKILLs and reaps whatever remains, so
    a child that ignores SIGTERM is still stopped: SIGTERM, then SIGKILL after
    the grace. Never SIGABRT.
    """
    if not guard.terminate_gracefully_if_authenticated():
        return
    deadline = time.monotonic() + grace_s
    while proc.poll() is None and time.monotonic() < deadline:
        time.sleep(0.01)


def run_captured(command, limit_mb, timeout_s, label="harness", env=None,
                 input_text=None, cancel_event=None, cwd=None,
                 terminate_grace_s=None):
    """Run and capture one child under the exact process-group RSS envelope.

    This is the shared sequential-harness path. It keeps the same process-tree
    timeout and zero-grace memory semantics as ``run_guarded`` while returning
    stdout/stderr for verdict parsing. Callers must persist the plan that
    supplied ``limit_mb`` alongside any timings or solved counts.

    With ``terminate_grace_s``, a ``cancel_event`` stop first SIGTERMs the
    authenticated group and allows it that long to exit before the usual
    authenticated SIGKILL-and-reap; without it a cancel goes straight to the
    SIGKILL, as before.
    """
    if not command:
        raise ValueError("captured command must not be empty")
    if not limit_mb or limit_mb <= 0:
        raise ValueError("captured command requires a positive memory limit")
    if timeout_s is None or not math.isfinite(timeout_s) or timeout_s <= 0:
        raise ValueError("captured command requires a finite positive timeout")
    if terminate_grace_s is not None and (
            not math.isfinite(terminate_grace_s) or terminate_grace_s < 0):
        raise ValueError("captured command terminate grace must be finite and non-negative")
    if os.name == "nt" or not hasattr(os, "killpg"):
        raise RuntimeError(
            "exact captured-run RSS enforcement requires POSIX process groups"
        )

    # Reject invalid input before creating a child that would need cleanup.
    input_bytes = input_text.encode("utf-8") if input_text is not None else None
    timeout_time_ns = None
    cancel_time_ns = None
    received_signal = [None, None]
    previous_handlers = {}
    capture_failed = threading.Event()
    stdout_result = []
    stderr_result = []
    stdout_thread = stderr_thread = input_thread = None
    execution_error = None
    cleanup_errors = []

    def terminate_on_parent_signal(signum, _frame):
        nonlocal cancel_time_ns
        received_signal[0] = signum
        if received_signal[1] is None:
            received_signal[1] = time.monotonic_ns()
        cancel_time_ns = received_signal[1]

    proc, guard = guarded_popen(
        command,
        limit_mb,
        label=label,
        grace_mb=0,
        stdin=subprocess.PIPE if input_bytes is not None else subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=env,
        cwd=cwd,
    )
    # The child's budget and its wall time start at the authenticated resume, which
    # guarded_popen has just sent: until then the command has not run. The spawn's
    # own waits are hang detectors (_GROUP_SETTLE_S), so on a stalled host the spawn
    # alone can outlast a solver's whole budget; started before it, the deadline
    # killed the solver as it resumed and its answer was recorded as a time-out.
    started = time.monotonic()
    execution_deadline = started + timeout_s
    try:
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
        if input_bytes is not None:
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

        if threading.current_thread() is threading.main_thread():
            for signum in (signal.SIGINT, signal.SIGTERM):
                previous_handlers[signum] = signal.getsignal(signum)
                signal.signal(signum, terminate_on_parent_signal)
        while True:
            guard.check_enforcement()
            if proc.poll() is not None:
                guard.check_enforcement()
                break
            if received_signal[0] is not None:
                break
            if capture_failed.is_set():
                break
            if cancel_event is not None and cancel_event.is_set():
                cancel_time_ns = time.monotonic_ns()
                if terminate_grace_s is not None:
                    _terminate_then_wait(proc, guard, terminate_grace_s)
                break
            if time.monotonic() >= execution_deadline:
                timeout_time_ns = time.monotonic_ns()
                break
            time.sleep(0.01)
    except BaseException as error:
        execution_error = error
    finally:
        try:
            completion = guard.finish(proc, label)
        except BaseException as error:
            cleanup_errors.append(error)
        for signum, handler in previous_handlers.items():
            try:
                signal.signal(signum, handler)
            except BaseException as error:
                cleanup_errors.append(error)

        for thread, stream in (
            (stdout_thread, proc.stdout),
            (stderr_thread, proc.stderr),
            (input_thread, proc.stdin if input_bytes is not None else None),
        ):
            try:
                # ident remains set after completion, and also catches a start
                # that raised after actually starting the thread.
                if thread is not None and thread.ident is not None:
                    thread.join(timeout=5)
                if thread is not None and thread.is_alive():
                    raise RuntimeError(
                        "captured child pipes did not close after process-group reap"
                    )
                # An active drainer/writer can hold the buffered stream lock.
                # Close here only when no live thread owns that stream.
                if stream is not None:
                    stream.close()
            except BaseException as error:
                cleanup_errors.append(error)

    if execution_error is not None:
        if hasattr(execution_error, "add_note"):
            for error in cleanup_errors:
                execution_error.add_note(f"mandatory cleanup also failed: {error}")
        raise execution_error
    if cleanup_errors:
        error = cleanup_errors[0]
        if hasattr(error, "add_note"):
            for secondary in cleanup_errors[1:]:
                error.add_note(f"mandatory cleanup also failed: {secondary}")
        raise error

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
        guard_evidence=completion,
    )


# ------------------------------------------------------------ measured admission
#
# The policy is in the module docstring. Every probe below is injectable, so the
# admission and the pressure watch are tested with fakes and no real pressure.

# margin_mb = ceil(RAM / ADMISSION_MARGIN_DIVISOR): room for peers (a build, an
# agent, another tenant) to GROW after the reading. A share of the host, never an
# absolute amount: an absolute floor is sized for one host. 1/8 keeps the 16 GiB
# the policy was measured with on a 128 GiB host (DR-12) and gives a 24 GiB host
# 3 GiB; critical pressure during the run is the backstop on every host (DR-43).
ADMISSION_MARGIN_DIVISOR = 8
# The window: this many readings, this far apart (~30 s), and the MINIMUM counts.
ADMISSION_SAMPLES = 3
ADMISSION_INTERVAL_S = 15.0
# During a campaign: one pressure poll per second; this many consecutive
# unmeasurable polls stop the campaign (fail closed); and a stopped child gets
# this long between SIGTERM and SIGKILL.
PRESSURE_POLL_S = 1.0
PRESSURE_MAX_UNKNOWN = 3
PRESSURE_TERMINATE_GRACE_S = 2.0

# macOS: sysctl kern.memorystatus_vm_pressure_level. XNU's handler
# (bsd/kern/kern_memorystatus_notify.c, sysctl_memorystatus_vm_pressure_level)
# returns convert_internal_pressure_level_to_dispatch_level(...): Normal ->
# NOTE_MEMORYSTATUS_PRESSURE_NORMAL (0x1), Warning and Urgent ->
# NOTE_MEMORYSTATUS_PRESSURE_WARN (0x2), Critical ->
# NOTE_MEMORYSTATUS_PRESSURE_CRITICAL (0x4) (bsd/sys/event_private.h), the same
# values the public SDK names DISPATCH_MEMORYPRESSURE_NORMAL/WARN/CRITICAL in
# <dispatch/source.h>. Any other value is not a reading.
DARWIN_PRESSURE_SYSCTL = "kern.memorystatus_vm_pressure_level"
DARWIN_PRESSURE_STATES = {1: "normal", 2: "warn", 4: "critical"}
# Linux has no kernel "critical" level. The PSI memory `full avg10` share (the
# percentage of the last 10 s in which every non-idle task was stalled on
# memory; Documentation/accounting/psi.rst) counts as critical at
# systemd-oomd's default memory-pressure limit, 60% (oomd.conf(5),
# DefaultMemoryPressureLimit=). UNTESTED: chosen by analogy, never run on a
# Linux host; a Linux campaign must measure it before it is trusted
# (the development design notes DR-12).
LINUX_PSI_MEMORY = "/proc/pressure/memory"
LINUX_PSI_FULL_CRITICAL_PCT = 60.0

_DARWIN_SYSCTLBYNAME = []


def _darwin_pressure_raw():
    """The raw kern.memorystatus_vm_pressure_level value, or ``None``.

    ctypes sysctlbyname first: one syscall, no fork, which matters when the
    host is short of memory. ``sysctl -n`` is the fallback.
    """
    try:
        import ctypes
        import ctypes.util
        if not _DARWIN_SYSCTLBYNAME:
            libc = ctypes.CDLL(ctypes.util.find_library("c") or "libc.dylib",
                               use_errno=True)
            call = libc.sysctlbyname
            call.argtypes = [ctypes.c_char_p, ctypes.POINTER(ctypes.c_uint32),
                             ctypes.POINTER(ctypes.c_size_t), ctypes.c_void_p,
                             ctypes.c_size_t]
            call.restype = ctypes.c_int
            _DARWIN_SYSCTLBYNAME.append(call)
        value = ctypes.c_uint32(0)
        size = ctypes.c_size_t(ctypes.sizeof(value))
        if (_DARWIN_SYSCTLBYNAME[0](DARWIN_PRESSURE_SYSCTL.encode(), ctypes.byref(value),
                                    ctypes.byref(size), None, 0) == 0
                and size.value == ctypes.sizeof(value)):
            return int(value.value)
    except Exception:
        pass
    try:
        out = subprocess.run(["sysctl", "-n", DARWIN_PRESSURE_SYSCTL],
                             capture_output=True, text=True, timeout=5,
                             check=True).stdout
        return int(out.strip())
    except Exception:
        return None


def memory_pressure_reading():
    """One reading of the kernel's memory-pressure state, or ``None``.

    Returns ``{"source", "raw", "state"}`` with ``state`` one of ``normal``,
    ``warn`` (macOS only) or ``critical``. ``None`` means unmeasurable, and
    every caller treats that as a refusal, never as normal.
    """
    if sys.platform == "darwin":
        raw = _darwin_pressure_raw()
        state = DARWIN_PRESSURE_STATES.get(raw)
        if state is None:
            return None
        return {"source": "sysctl " + DARWIN_PRESSURE_SYSCTL, "raw": raw,
                "state": state}
    try:
        with open(LINUX_PSI_MEMORY, "r", encoding="utf-8") as handle:
            text = handle.read(4096)
        share = re.search(r"^full avg10=([0-9]+(?:\.[0-9]+)?)\b", text, re.MULTILINE)
        if share is None:
            return None
        pct = float(share.group(1))
    except (OSError, ValueError):
        return None
    return {"source": LINUX_PSI_MEMORY + " full avg10", "raw": pct,
            "state": "critical" if pct >= LINUX_PSI_FULL_CRITICAL_PCT else "normal"}


def harness_peak_rss_mb():
    """This process's peak resident set in MiB (rounded up), or ``None``.

    getrusage(2)'s ``ru_maxrss`` is bytes on macOS and KiB on Linux.
    """
    try:
        import resource
        peak = int(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    except Exception:
        return None
    if peak <= 0:
        return None
    unit = 1024 * 1024 if sys.platform == "darwin" else 1024
    return -(-peak // unit)


def admission_margin_mb(physical_mb):
    """Peer-growth margin: ceil(physical RAM / ADMISSION_MARGIN_DIVISOR), in MiB."""
    physical_mb = int(physical_mb)
    if physical_mb <= 0:
        raise ValueError("physical RAM must be positive")
    return -(-physical_mb // ADMISSION_MARGIN_DIVISOR)


def _probe_value(probe):
    try:
        return probe()
    except Exception:
        return None


def sample_admission_window(samples=ADMISSION_SAMPLES, interval_s=ADMISSION_INTERVAL_S,
                            available_probe=None, pressure_probe=None,
                            sleep=time.sleep, clock=time.monotonic, wall=time.time):
    """``samples`` readings of available memory and pressure, ``interval_s`` apart.

    Never raises for a failed probe: an unmeasurable reading is recorded as
    ``None``, and :func:`ram_admission_decision` refuses it.
    """
    samples = int(samples)
    if samples <= 0:
        raise ValueError("admission needs at least one sample")
    available_probe = available_probe or host_available_ram_reading
    pressure_probe = pressure_probe or memory_pressure_reading
    rows = []
    started = clock()
    for index in range(samples):
        if index:
            sleep(interval_s)
        available = _probe_value(available_probe)
        if isinstance(available, bool) or not isinstance(available, int) or available < 0:
            available = None
        pressure = _probe_value(pressure_probe)
        if not isinstance(pressure, dict) or pressure.get("state") not in (
                "normal", "warn", "critical"):
            pressure = None
        rows.append({"index": index, "t_unix": round(wall(), 3),
                     "t_offset_s": round(clock() - started, 3),
                     "available_mb": available, "pressure": pressure})
    return rows


def _window_refusal(samples, physical_mb, harness_mb):
    """Why these readings cannot admit anything, or ``None``. Fail closed."""
    if not samples:
        return "no admission readings"
    unread = [row["index"] for row in samples if row.get("available_mb") is None]
    if unread:
        return f"cannot measure available memory (samples {unread}); refusing fail-closed"
    unread = [row["index"] for row in samples if row.get("pressure") is None]
    if unread:
        return f"cannot measure memory pressure (samples {unread}); refusing fail-closed"
    if not physical_mb or physical_mb <= 0:
        return "cannot measure physical RAM; refusing fail-closed"
    if harness_mb is None:
        return "cannot measure the harness's own resident memory; refusing fail-closed"
    critical = [row["index"] for row in samples if row["pressure"]["state"] == "critical"]
    if critical:
        return f"memory pressure is critical at admission (samples {critical})"
    return None


def ram_admission_decision(samples, jobs, memlimit_mb, harness_mb, physical_mb,
                           plan_error=None):
    """The admission record for one window and one enforced envelope. Pure.

    Admits iff every reading was measurable and none critical, and
        min(available) >= jobs * memlimit_mb + harness_mb + margin_mb.
    """
    measured = [row["available_mb"] for row in samples
                if isinstance(row.get("available_mb"), int)]
    record = {
        "samples": [dict(row) for row in samples],
        "min_available_mb": min(measured) if measured else None,
        "physical_mb": physical_mb or None,
        "margin_mb": (admission_margin_mb(physical_mb)
                      if physical_mb and physical_mb > 0 else None),
        "margin_rule": f"ceil(physical_mb / {ADMISSION_MARGIN_DIVISOR})",
        "jobs": jobs,
        "memlimit_mb": memlimit_mb,
        "harness_mb": harness_mb,
        "children_mb": None,
        "envelope_mb": None,
        "required_mb": None,
    }
    if jobs is not None and memlimit_mb is not None and harness_mb is not None:
        record["children_mb"] = jobs * memlimit_mb
        record["envelope_mb"] = record["children_mb"] + harness_mb
        if record["margin_mb"] is not None:
            record["required_mb"] = record["envelope_mb"] + record["margin_mb"]
    reason = _window_refusal(samples, physical_mb, harness_mb) or plan_error
    if reason is None and record["required_mb"] is None:
        reason = "no enforced envelope to admit"
    if reason is None and record["min_available_mb"] < record["required_mb"]:
        reason = (f"tight host: min available {record['min_available_mb']} MiB < envelope "
                  f"{record['envelope_mb']} MiB + margin {record['margin_mb']} MiB")
    record["decision"] = "refuse" if reason else "admit"
    record["reason"] = reason or (
        f"min available {record['min_available_mb']} MiB >= envelope "
        f"{record['envelope_mb']} MiB + margin {record['margin_mb']} MiB")
    return record


class AdmissionRefused(RuntimeError):
    """The campaign was not admitted; ``record`` says why, with every reading."""

    def __init__(self, message, record):
        super().__init__(message)
        self.record = record


def admit_campaign(jobs, label="harness", mem_floor_mb=1024, ram_mb=None, cores=None,
                   samples=ADMISSION_SAMPLES, interval_s=ADMISSION_INTERVAL_S,
                   available_probe=None, pressure_probe=None, rss_probe=None,
                   build_probe=None, capture_streams=2, sleep=time.sleep,
                   acquire_lease=True, _lock_path=None):
    """Admit a campaign on measured RAM headroom; return ``(plan, record)``.

    Takes the host lease first (another AY campaign is refused as before), so
    no other campaign starts children while the window is read, then reads the
    window, sizes the plan's per-child caps into the measured room and admits
    by :func:`ram_admission_decision`. On refusal the lease is released and
    :class:`AdmissionRefused` carries the record. On admission the caller
    holds the lease (release with ``_release_harness_lease``) and should run a
    :class:`MemoryPressureWatch` for as long as its children can run.

    A running compiler is not a veto: ``build_probe`` (default
    :func:`count_active_rustc`) is recorded for the audit and decides nothing.
    """
    jobs = int(jobs)
    if jobs <= 0:
        raise ValueError("jobs must be positive")
    rss_probe = rss_probe or harness_peak_rss_mb
    build_probe = build_probe or count_active_rustc
    record = {"policy": "measured-ram-headroom", "label": label, "requested_jobs": jobs,
              "window": {"samples": int(samples), "interval_s": interval_s},
              "available_source": AVAILABLE_RAM_SOURCE}
    if acquire_lease:
        try:
            acquire_harness_lease(label, _lock_path=_lock_path)
        except RuntimeError as error:
            record.update(decision="refuse", reason=f"host resource lease: {error}")
            raise AdmissionRefused(record["reason"], record) from error
    try:
        window = sample_admission_window(samples, interval_s, available_probe,
                                         pressure_probe, sleep=sleep)
        physical = int(ram_mb) if ram_mb is not None else physical_ram_mb()
        rss = _probe_value(rss_probe)
        rss = rss if isinstance(rss, int) and not isinstance(rss, bool) and rss > 0 else None
        # run_captured retains at most CAPTURE_LIMIT_BYTES per stream per child.
        capture_mb = -(-jobs * capture_streams * CAPTURE_LIMIT_BYTES // (1024 * 1024))
        harness_mb = None if rss is None else rss + capture_mb
        try:
            builds = build_probe()
        except Exception as error:
            builds = f"unmeasured ({type(error).__name__}: {error})"
        plan = plan_error = None
        if _window_refusal(window, physical, harness_mb) is None:
            room = min(row["available_mb"] for row in window)
            try:
                plan = plan_solver_resources(
                    jobs, ram_mb=ram_mb, cores=cores, mem_floor_mb=mem_floor_mb,
                    label=label, acquire_lease=False, available_mb=room,
                    reserve_mb=admission_margin_mb(physical) + harness_mb)
            except (RuntimeError, ValueError) as error:
                plan_error = f"tight host: no {mem_floor_mb} MiB child fits the measured room: {error}"
        record.update(ram_admission_decision(
            window, plan.jobs if plan else None, plan.memlimit_mb if plan else None,
            harness_mb, physical, plan_error))
        record.update(harness_rss_mb=rss, harness_capture_mb=capture_mb,
                      nbcore=plan.nbcore if plan else None,
                      headroom_mb=plan.headroom_mb if plan else None,
                      active_build_processes=builds,
                      build_processes_role="recorded, not a veto")
        if record["decision"] != "admit":
            raise AdmissionRefused(record["reason"], record)
        return plan, record
    except BaseException:
        if acquire_lease:
            _release_harness_lease()
        raise


def format_admission(record):
    """Human-readable lines for an admission record (every sample included)."""
    decision = str(record.get("decision", "refuse")).upper()
    lines = [f"admission: {decision} ({record.get('reason')})"]
    for row in record.get("samples", []):
        pressure = row.get("pressure")
        shown = (f"{pressure['state']} ({pressure['source']}={pressure['raw']})"
                 if pressure else "UNMEASURED")
        available = row.get("available_mb")
        lines.append(f"  sample {row['index']} t+{row['t_offset_s']}s available "
                     f"{'UNMEASURED' if available is None else str(available) + ' MiB'} "
                     f"pressure {shown}")
    if record.get("envelope_mb") is not None:
        lines.append(
            f"  envelope {record['envelope_mb']} MiB = {record['jobs']} jobs x "
            f"{record['memlimit_mb']} MiB enforced per-child cap + harness "
            f"{record['harness_mb']} MiB (peak RSS {record.get('harness_rss_mb')} + "
            f"capture buffers {record.get('harness_capture_mb')})")
    if record.get("margin_mb") is not None:
        lines.append(f"  margin {record['margin_mb']} MiB = {record.get('margin_rule')} "
                     f"with physical_mb={record.get('physical_mb')}; required "
                     f"{record.get('required_mb')} MiB vs min available "
                     f"{record.get('min_available_mb')} MiB")
    if "active_build_processes" in record:
        lines.append(f"  active build processes: {record['active_build_processes']} "
                     f"({record.get('build_processes_role')})")
    return lines


# ------------------------------------------------------------ landing builds
#
# A landing's cargo builds and test builds take their job count from the room
# measured when the round starts, not from the core count alone. The anchor is
# a measurement of ay's own build, not of a host: on 2026-10-14 a landing whose
# legs built the workspace and ay's CLI cold at cargo's default 14 jobs peaked
# at 9164 MiB over its whole process tree, sampled every 2 s
# (the development design notes); BUILD_PEAK_MB is that, rounded up, and
# BUILD_PEAK_JOBS the job count it was measured at. A job's share is
# BUILD_PEAK_MB / BUILD_PEAK_JOBS. (The largest single compiler, ay-dpll at
# 6464 MiB, is not the unit: it sits on the dependency chain, and a job is a
# jobserver token its codegen threads share, so a smaller job count also
# shrinks it. Sizing every job as that compiler planned one job at 9.5 GiB
# available, a single-threaded build where 14 jobs had just run without
# memory pressure.)
BUILD_PEAK_MB = 9216
BUILD_PEAK_JOBS = 14


def landing_build_plan(available_mb=None, physical_mb=None, cores=None,
                       peak_mb=BUILD_PEAK_MB, peak_jobs=BUILD_PEAK_JOBS, cap=None):
    """The cargo job count for a landing's builds, and what it was sized from. Pure.

    jobs = clamp(floor(room / (peak_mb / peak_jobs)), 1, cores), with room the
    memory available less DR-43's peer-growth margin: the measured build's
    share per job fits the room, and never more jobs than cores. One job when
    the room or the RAM cannot be measured, or holds less than one share: a
    landing never refuses to build, it builds slower. `cap`, the job count
    the caller set (CARGO_BUILD_JOBS: a machine-wide gate's share, such as
    build-slot's, or the lander's own), bounds it from above.
    """
    record = {"cores": cores, "physical_mb": physical_mb, "available_mb": available_mb,
              "peak_mb": peak_mb, "peak_jobs": peak_jobs, "margin_mb": None, "room_mb": None,
              "jobs": 1, "why": None, "cap": cap}
    record = _landing_build_fit(record)
    if cap is not None and cap >= 1 and record["jobs"] > cap:
        record["jobs"] = int(cap)
        record["why"] += f" -> at most the caller's {int(cap)} (CARGO_BUILD_JOBS)"
    return record


def _landing_build_fit(record):
    cores, physical_mb, available_mb = record["cores"], record["physical_mb"], record["available_mb"]
    peak_mb, peak_jobs = record["peak_mb"], record["peak_jobs"]
    if not cores or cores <= 0:
        record["why"] = "core count unmeasured: one job"
        return record
    if available_mb is None or not physical_mb or physical_mb <= 0:
        record["why"] = "available memory or RAM unmeasured: one job"
        return record
    record["margin_mb"] = admission_margin_mb(physical_mb)
    room = record["room_mb"] = available_mb - record["margin_mb"]
    fit = (room * peak_jobs) // peak_mb if room > 0 else 0
    record["jobs"] = max(1, min(int(cores), int(fit)))
    record["why"] = (f"min({cores} cores, floor(({available_mb} available - {record['margin_mb']} margin)"
                     f" / ({peak_mb} measured build peak / {peak_jobs} jobs)))"
                     + (" -> at least one" if fit < 1 else ""))
    return record


class MemoryPressureWatch:
    """Poll kernel memory pressure for a campaign; at critical, stop its children.

    ``on_critical`` is called once, from the watch thread, when pressure reads
    critical or has been unmeasurable for ``max_unknown`` consecutive polls
    (fail closed). The campaign wires it to the cancel event its
    ``run_captured`` children observe, with ``terminate_grace_s``, so every live
    child gets SIGTERM, then SIGKILL after the grace, and no new child starts.
    A tripped campaign is COULD NOT RUN: its results are neither a pass nor a
    failure. Every poll is appended to ``trace_path`` (JSON lines); memory
    keeps only counts and state transitions.
    """

    MAX_TRANSITIONS = 256

    def __init__(self, label="harness", probe=None, poll_s=PRESSURE_POLL_S,
                 on_critical=None, trace_path=None, max_unknown=PRESSURE_MAX_UNKNOWN,
                 clock=time.monotonic, wall=time.time):
        if not math.isfinite(float(poll_s)) or poll_s <= 0:
            raise ValueError("pressure poll interval must be finite and positive")
        if int(max_unknown) <= 0:
            raise ValueError("max_unknown must be positive")
        self._label = label
        self._probe = probe or memory_pressure_reading
        self._poll_s = poll_s
        self._on_critical = on_critical
        self._trace_path = trace_path
        self._max_unknown = int(max_unknown)
        self._clock = clock
        self._wall = wall
        self._lock = threading.Lock()
        self._stop_evt = threading.Event()
        self._tripped = threading.Event()
        self._thread = None
        self._trace = None
        self._started = None
        self._unknown = 0
        self._polls = 0
        self._counts = collections.Counter()
        self._transitions = []
        self._last_state = None
        self._last = None
        self._worst = None
        self._summary = None
        self.trip_reason = None
        self.trip_time_unix = None

    @property
    def tripped(self):
        return self._tripped.is_set()

    def start(self):
        if self._thread is not None:
            raise RuntimeError("pressure watch already started")
        if self._trace_path is not None:
            self._trace = open(self._trace_path, "x", encoding="utf-8")
        self._started = self._clock()
        self._poll()
        self._thread = threading.Thread(target=self._run, name=f"{self._label}-pressure",
                                        daemon=True)
        self._thread.start()
        return self

    def __enter__(self):
        return self.start()

    def __exit__(self, *_exc):
        self.stop()
        return False

    def _poll(self):
        reading = _probe_value(self._probe)
        if not isinstance(reading, dict) or reading.get("state") not in (
                "normal", "warn", "critical"):
            reading = None
        state = reading["state"] if reading else "unmeasured"
        row = {"t_unix": round(self._wall(), 3),
               "t_offset_s": round(self._clock() - self._started, 3),
               "pressure": reading}
        if self._trace is not None:
            self._trace.write(json.dumps(row, sort_keys=True) + "\n")
            self._trace.flush()
        rank = {"normal": 0, "warn": 1, "unmeasured": 2, "critical": 3}
        with self._lock:
            self._polls += 1
            self._counts[state] += 1
            self._last = row
            if self._worst is None or rank[state] > rank[self._worst["state"]]:
                self._worst = dict(row, state=state)
            if state != self._last_state:
                if len(self._transitions) < self.MAX_TRANSITIONS:
                    self._transitions.append(dict(row, state=state))
                self._last_state = state
            if reading is None:
                self._unknown += 1
                unknown = self._unknown
            else:
                self._unknown = 0
                unknown = 0
        if reading is None and unknown >= self._max_unknown:
            self._trip(f"memory pressure unmeasurable for {unknown} consecutive polls")
        elif reading is not None and reading["state"] == "critical":
            self._trip(f"memory pressure critical ({reading['source']}={reading['raw']})")

    def _trip(self, reason):
        with self._lock:
            if self._tripped.is_set():
                return
            self.trip_reason = reason
            self.trip_time_unix = round(self._wall(), 3)
            self._tripped.set()
        print(f"[oom-guard] {self._label}: {reason}; stopping the campaign's children "
              "(SIGTERM, then SIGKILL after the grace): COULD NOT RUN.",
              file=sys.stderr, flush=True)
        if self._on_critical is not None:
            self._on_critical()

    def _run(self):
        try:
            while not self._stop_evt.wait(self._poll_s):
                self._poll()
        except BaseException as error:
            self._trip(f"memory pressure watch failed: {error!r}")

    def stop(self):
        """Stop polling (idempotent) and return :meth:`summary`."""
        self._stop_evt.set()
        thread = self._thread
        if thread is not None and thread is not threading.current_thread():
            thread.join(timeout=10)
            if thread.is_alive():
                raise RuntimeError(f"{self._label}: pressure watch did not stop within 10 seconds")
        if self._trace is not None:
            self._trace.close()
            self._trace = None
        return self.summary()

    def summary(self):
        with self._lock:
            return {"probe_poll_s": self._poll_s, "polls": self._polls,
                    "counts": dict(self._counts), "worst": self._worst,
                    "last": self._last, "transitions": list(self._transitions),
                    "tripped": self._tripped.is_set(), "trip_reason": self.trip_reason,
                    "trip_time_unix": self.trip_time_unix, "trace_path": self._trace_path}


def format_pressure(summary):
    """One line for a pressure-watch summary."""
    worst = summary.get("worst") or {}
    return (f"memory pressure: {summary.get('polls')} polls every "
            f"{summary.get('probe_poll_s')}s, counts {summary.get('counts')}, worst "
            f"{worst.get('state')} at t+{worst.get('t_offset_s')}s, "
            f"{'TRIPPED: ' + str(summary.get('trip_reason')) if summary.get('tripped') else 'never critical'}"
            f" (trace {summary.get('trace_path')})")


def warn_concurrent_build():
    """Refuse if a Cargo/Targo compiler build looks active — concurrent sweeps
    with heavy LTO builds triggered the 2026-06-19 and 2026-07-11 watchdog
    panics.

    The legacy admission for the sweep harnesses and ``plan
    --warn-concurrent-build``. A harness that admits through
    :func:`admit_campaign` and runs a :class:`MemoryPressureWatch` (the
    differential gate) must not call it: there a compiler is measured, not
    vetoed. See the module docstring."""
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
    landing = sub.add_parser("landing-plan", help="print what this host has now and the build job count "
                                                  "a landing sizes into it (shell assignments)")
    landing.add_argument("--cap", type=int, default=None,
                         help="the job count the landing's caller set (CARGO_BUILD_JOBS): an upper bound")
    args = ap.parse_args(argv)
    if args.cmd == "landing-plan":
        cores = os.cpu_count()
        record = landing_build_plan(host_available_ram_reading(), physical_ram_mb(), cores, cap=args.cap)
        try:
            load = "%.1f" % os.getloadavg()[0]
        except OSError:
            load = "unmeasured"
        pressure = memory_pressure_reading()
        print(f"LAND_BUILD_JOBS={record['jobs']}")
        print("LAND_HOST_PLAN='cores {cores} ram {ram} MiB available {avail} MiB ({src}) load {load} "
              "pressure {pressure}; build jobs {jobs} = {why}'".format(
                  cores=cores, ram=record["physical_mb"], avail=record["available_mb"],
                  src=AVAILABLE_RAM_SOURCE, load=load,
                  pressure=pressure["state"] if pressure else "unmeasured",
                  jobs=record["jobs"], why=record["why"]).replace("\n", " "))
        return 0
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
