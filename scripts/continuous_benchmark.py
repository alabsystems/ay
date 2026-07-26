#!/usr/bin/env python3
# ay-script: continuous-benchmark
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Safe continuous integration and competition-benchmark campaign driver.

The driver is intentionally orchestration only: scoring and solver resource
enforcement remain in the native `ay bench` runner.  A cycle:

1. snapshots all remote branch heads;
2. classifies topics by ancestry and patch equivalence;
3. merges unique topics in a disposable worktree;
4. builds and runs correctness gates;
5. runs every canary plus one resumable rolling benchmark lane;
6. optionally asks Codex for one repair attempt, then repeats every gate;
7. pushes only an ordinary fast-forward from the exact tested base; and
8. atomically publishes a local JSON/Markdown progress packet.

Raw benchmark evidence stays outside Git.  The process-wide `_oom_guard.py`
lease used by `ay bench` prevents overlapping solver campaigns and persists
the enforced child envelope in each native results packet.
"""

from __future__ import annotations

import argparse
import contextlib
import dataclasses
import datetime as dt
import fnmatch
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import shlex
import shutil
import signal
import stat
import subprocess
import sys
import time
import tomllib
from typing import Any, Iterable

try:
    from scripts import _oom_guard
except ImportError:
    import _oom_guard  # type: ignore[no-redef]


SCHEMA_VERSION = 1
ISSUE_TITLE = "Continuous 2025–2026 competition benchmark scoreboard"
# Compact remote progress lives outside refs/heads so operational state never
# masquerades as an integration candidate or requires a permanent topic branch.
STATUS_REF = "refs/notes/continuous/status"
MAX_JSON_BYTES = 64 * 1024 * 1024
MAX_MANIFEST_TEXT_BYTES = 8 * 1024 * 1024
MAX_TASK_DEFINITION_BYTES = 64 * 1024 * 1024
MAX_YAML_PATH_SCALAR_BYTES = 16 * 1024
MAX_SOLVER_BYTES = 1024 * 1024 * 1024
MAX_CHILD_FILE_BYTES = 10 * 1024 * 1024 * 1024
DEFAULT_CYCLE_TIMEOUT_SEC = 3 * 60 * 60 + 30 * 60
_ACTIVE_CHILD_PROCESS_GROUP: int | None = None
BUILD_SANDBOX_MARKER = "AY_CONTINUOUS_BUILD_SANDBOX"
BENCH_CORPUS_ROOT_ENV = "AY_BENCH_CORPUS_ROOT"
CARGO_BUILD_JOBS_ENV = "CARGO_BUILD_JOBS"
PARENT_LEASE_ENV = "AY_OOM_GUARD_PARENT_LEASE"
CONTINUOUS_JOBS_ENV = "AY_CONTINUOUS_JOBS"
CONTINUOUS_HEADROOM_ENV = "AY_CONTINUOUS_HEADROOM_MB"
BUILD_DRIVER_NAMES = frozenset({"cargo", "targo"})
BUILD_DRIVER_SUBCOMMANDS = frozenset(
    {
        "bench",
        "build",
        "check",
        "clippy",
        "doc",
        "fix",
        "install",
        "run",
        "rustc",
        "test",
    }
)
BUILD_DRIVER_JOB_OPTIONS = frozenset({"-j", "--jobs"})
BUILD_DRIVER_GLOBAL_OPTIONS_WITH_VALUE = frozenset(
    {
        "--color",
        "--config",
        "--manifest-path",
        "-C",
        "-Z",
    }
) | BUILD_DRIVER_JOB_OPTIONS
REPAIR_PROTECTED_PREFIXES = (
    ".cargo/",
    ".github/",
    "benchmarks/",
    "crates/ay-bench/",
    "crates/ay-drat-check/",
    "crates/ay-lrat-check/",
    "crates/ay-proof/",
    "crates/ay-proof-common/",
    "crates/ay-test-support/",
    "deploy/",
    "evals/",
    "reference/",
    "scripts/",
)
INTEGRATION_POLICY_PREFIXES = (
    ".cargo/",
    ".github/",
    "benchmarks/",
    "crates/ay-bench/",
    "crates/ay-drat-check/",
    "crates/ay-lrat-check/",
    "crates/ay-proof/",
    "crates/ay-proof-common/",
    "crates/ay-test-support/",
    "deploy/",
    "evals/",
    "reference/",
    "scripts/",
)
CAMPAIGN_CHECK_COMMAND = ["{ay}", "bench", "compare", "campaign-check"]
OFFICIAL_FIELD_PACKET = "continuous-official-field-2025-2026.json"
AY_SCOREBOARD_PACKET = "continuous-ay-scoreboard.json"
CANDIDATE_EXACT_CPU_TIME_SOURCE = "sandbox-posix-time-user+sys-v1"
REFERENCE_EXACT_CPU_TIME_SOURCE = "posix-time-user+sys"
CHC_COMPETITION_TIMEOUT_SEC = 1800.0
CHC_COMPETITION_TIMEOUT_MS = str(int(CHC_COMPETITION_TIMEOUT_SEC * 1000))
FIXED_OFFICIAL_CHC_LANE_ID = (
    "chccomp-2025-lia-nonlin-arrays-official-shard-0"
)
FIXED_OFFICIAL_CHC_EVAL_ID = "chccomp-2025-lia-nonlin-arrays"
FIXED_OFFICIAL_CHC_SHARD_SIZE = 64
FIXED_OFFICIAL_CHC_SHARD_INDEX = 0
FIXED_OFFICIAL_CHC_COMMAND_TIMEOUT_SEC = 12_000
FIXED_OFFICIAL_CHC_MIN_BENCHMARKS = 1738
FIXED_OFFICIAL_CHC_SET_PATH = (
    "benchmarks/chc/chc-comp25-benchmarks/LIA-Arrays.set"
)
EXACT_CPU_TIME_SOURCES = frozenset(
    {
        CANDIDATE_EXACT_CPU_TIME_SOURCE,
        REFERENCE_EXACT_CPU_TIME_SOURCE,
    }
)
DEFINITIVE_RESULTS = frozenset(
    {
        "sat",
        "unsat",
        "safe",
        "unsafe",
        "satisfiable",
        "unsatisfiable",
        "optimal",
    }
)


class CampaignError(RuntimeError):
    """A fail-closed campaign error."""


class CycleInterrupted(BaseException):
    """Non-operational control flow for SIGALRM/SIGTERM cleanup."""


def solver_mode_control_or_delimiter(argument: str) -> bool:
    attached_short = argument.removeprefix("-t")
    attached_digits = attached_short.removeprefix("+")
    return (
        argument == "--"
        or argument == "--competition"
        or argument == "--timeout"
        or argument.startswith("--competition=")
        or argument.startswith("--timeout=")
        or argument == "-t"
        or argument == "-T"
        or argument.startswith("-t:")
        or argument.startswith("-T:")
        or argument.startswith("-t=")
        or argument.startswith("timeout=")
        or (
            attached_short != argument
            and bool(attached_digits)
            and attached_digits.isascii()
            and attached_digits.isdigit()
        )
    )


def cycle_interrupt_handler(signum: int, _frame: Any) -> None:
    """Turn service termination/deadline signals into orderly cycle failures."""

    global _ACTIVE_CHILD_PROCESS_GROUP
    child_group = _ACTIVE_CHILD_PROCESS_GROUP
    _ACTIVE_CHILD_PROCESS_GROUP = None
    if child_group is not None:
        with contextlib.suppress(ProcessLookupError):
            os.killpg(child_group, signal.SIGTERM)
    name = signal.Signals(signum).name
    raise CycleInterrupted(f"cycle interrupted by {name}; cleanup requested")


def arm_cycle_deadline(timeout_sec: int) -> tuple[Any, Any]:
    if timeout_sec < 60:
        raise CampaignError("cycle timeout must be at least 60 seconds")
    previous_alarm = signal.getsignal(signal.SIGALRM)
    previous_term = signal.getsignal(signal.SIGTERM)
    signal.signal(signal.SIGALRM, cycle_interrupt_handler)
    signal.signal(signal.SIGTERM, cycle_interrupt_handler)
    signal.setitimer(signal.ITIMER_REAL, float(timeout_sec))
    return previous_alarm, previous_term


def disarm_cycle_deadline(previous: tuple[Any, Any]) -> None:
    signal.setitimer(signal.ITIMER_REAL, 0.0)
    signal.signal(signal.SIGALRM, previous[0])
    signal.signal(signal.SIGTERM, previous[1])


@dataclasses.dataclass
class CommandRecord:
    argv: list[str]
    cwd: str
    exit_code: int
    elapsed_sec: float
    log: str

    def as_json(self) -> dict[str, Any]:
        return dataclasses.asdict(self)


@dataclasses.dataclass
class BranchRecord:
    name: str
    sha: str
    classification: str
    detail: str = ""

    def as_json(self) -> dict[str, str]:
        return dataclasses.asdict(self)


@dataclasses.dataclass
class LaneOutcome:
    lane_id: str
    eval_id: str
    status: str
    detail: str
    command: CommandRecord | None = None
    scorecard_path: str | None = None
    scorecard: dict[str, Any] | None = None
    evidence_path: str | None = None
    evidence: dict[str, Any] | None = None
    shard: dict[str, Any] | None = None
    correctness_alarm: bool = False

    def as_json(self) -> dict[str, Any]:
        value = dataclasses.asdict(self)
        if self.command is not None:
            value["command"] = self.command.as_json()
        return value


def utc_now() -> dt.datetime:
    return dt.datetime.now(dt.UTC)


def run_id(now: dt.datetime | None = None) -> str:
    return (now or utc_now()).strftime("%Y%m%dT%H%M%SZ")


def atomic_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}")
    with temporary.open("w", encoding="utf-8") as handle:
        json.dump(value, handle, indent=2, sort_keys=True)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def atomic_text(path: Path, value: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}")
    with temporary.open("w", encoding="utf-8") as handle:
        handle.write(value)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def read_json(
    path: Path,
    default: Any,
    *,
    max_bytes: int = MAX_JSON_BYTES,
) -> Any:
    """Read a bounded regular JSON file without following its final symlink."""

    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    descriptor = -1
    try:
        descriptor = os.open(path, flags)
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode) or metadata.st_size > max_bytes:
            return default
        with os.fdopen(descriptor, "rb") as handle:
            descriptor = -1
            content = handle.read(max_bytes + 1)
        if len(content) > max_bytes:
            return default
        return json.loads(content)
    except (
        FileNotFoundError,
        json.JSONDecodeError,
        OSError,
        TypeError,
        UnicodeDecodeError,
    ):
        return default
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def read_bounded_regular_text(
    path: Path,
    *,
    max_bytes: int = MAX_MANIFEST_TEXT_BYTES,
) -> str:
    """Read a bounded regular UTF-8 file without following its final symlink."""

    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise CampaignError(f"cannot open manifest input {path}: {error}") from error
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            raise CampaignError(f"manifest input is not a regular file: {path}")
        if metadata.st_size > max_bytes:
            raise CampaignError(
                f"manifest input exceeds the {max_bytes}-byte cap: {path}"
            )
        with os.fdopen(descriptor, "rb") as handle:
            descriptor = -1
            content = handle.read(max_bytes + 1)
        if len(content) > max_bytes:
            raise CampaignError(
                f"manifest input exceeds the {max_bytes}-byte cap: {path}"
            )
        return content.decode("utf-8")
    except UnicodeDecodeError as error:
        raise CampaignError(f"manifest input is not UTF-8: {path}") from error
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def prepare_state_root(path: Path) -> None:
    """Create the host-local evidence root without group/world write access."""

    path.mkdir(mode=0o700, parents=True, exist_ok=True)
    if os.name == "posix":
        path.chmod(0o700)


def load_toml(path: Path) -> dict[str, Any]:
    try:
        with path.open("rb") as handle:
            value = tomllib.load(handle)
    except (OSError, tomllib.TOMLDecodeError) as error:
        raise CampaignError(f"cannot load {path}: {error}") from error
    if value.get("schema_version") != SCHEMA_VERSION:
        raise CampaignError(
            f"{path}: unsupported schema_version "
            f"{value.get('schema_version')!r}; expected {SCHEMA_VERSION}"
        )
    return value


def command_text(argv: Iterable[str]) -> str:
    return " ".join(shlex.quote(part) for part in argv)


def run_command(
    argv: list[str],
    cwd: Path,
    log_path: Path,
    *,
    env: dict[str, str] | None = None,
    timeout: float | None = None,
    abort_on_concurrent_build: bool = False,
    inherit_env: bool = True,
) -> CommandRecord:
    """Run one command with unbounded output streamed to an evidence log."""

    global _ACTIVE_CHILD_PROCESS_GROUP
    log_path.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    merged_env = os.environ.copy() if inherit_env else {}
    if env:
        merged_env.update(env)
    with log_path.open("w", encoding="utf-8") as log:
        log.write(f"$ {command_text(argv)}\n")
        log.flush()
        if abort_on_concurrent_build:
            try:
                active_builds = _oom_guard.count_active_rustc()
            except Exception as error:
                log.write(
                    "continuous-benchmark: cannot inspect host build processes; "
                    f"refusing sweep: {error}\n"
                )
                return CommandRecord(
                    argv=argv,
                    cwd=str(cwd),
                    exit_code=125,
                    elapsed_sec=round(time.monotonic() - started, 3),
                    log=str(log_path),
                )
            if active_builds:
                log.write(
                    "continuous-benchmark: refusing sweep because "
                    f"{active_builds} host Cargo/rustc process(es) are active\n"
                )
                return CommandRecord(
                    argv=argv,
                    cwd=str(cwd),
                    exit_code=125,
                    elapsed_sec=round(time.monotonic() - started, 3),
                    log=str(log_path),
                )
        process = subprocess.Popen(
            argv,
            cwd=cwd,
            env=merged_env,
            stdin=subprocess.DEVNULL,
            stdout=log,
            stderr=subprocess.STDOUT,
            text=True,
            start_new_session=True,
        )
        _ACTIVE_CHILD_PROCESS_GROUP = process.pid
        deadline = started + timeout if timeout is not None else None

        def terminate_group() -> None:
            with contextlib.suppress(ProcessLookupError):
                os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                with contextlib.suppress(ProcessLookupError):
                    os.killpg(process.pid, signal.SIGKILL)
                process.wait()

        def wait_for_completion() -> int:
            if not abort_on_concurrent_build:
                try:
                    return process.wait(timeout=timeout)
                except subprocess.TimeoutExpired:
                    log.write(
                        f"\ncontinuous-benchmark: command timed out after {timeout}s\n"
                    )
                    log.flush()
                    terminate_group()
                    return 124

            while True:
                remaining = (
                    None
                    if deadline is None
                    else max(0.0, deadline - time.monotonic())
                )
                if remaining == 0.0:
                    log.write(
                        f"\ncontinuous-benchmark: command timed out after {timeout}s\n"
                    )
                    log.flush()
                    terminate_group()
                    return 124
                wait_slice = 5.0 if remaining is None else min(5.0, remaining)
                try:
                    return process.wait(timeout=wait_slice)
                except subprocess.TimeoutExpired:
                    try:
                        active_builds = _oom_guard.count_active_rustc()
                    except Exception as error:
                        log.write(
                            "\ncontinuous-benchmark: cannot inspect host build "
                            f"processes; aborting sweep: {error}\n"
                        )
                        active_builds = 1
                    if active_builds:
                        log.write(
                            "\ncontinuous-benchmark: aborting sweep because "
                            f"{active_builds} host Cargo/rustc process(es) started\n"
                        )
                        log.flush()
                        terminate_group()
                        return 125

        try:
            code = wait_for_completion()
        finally:
            if process.poll() is None:
                terminate_group()
            _ACTIVE_CHILD_PROCESS_GROUP = None
    return CommandRecord(
        argv=argv,
        cwd=str(cwd),
        exit_code=code,
        elapsed_sec=round(time.monotonic() - started, 3),
        log=str(log_path),
    )


def capture(argv: list[str], cwd: Path, *, check: bool = True) -> str:
    completed = subprocess.run(
        argv,
        cwd=cwd,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if check and completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise CampaignError(
            f"{command_text(argv)} failed with {completed.returncode}: {detail}"
        )
    return completed.stdout.strip()


def git(repo: Path, *args: str, check: bool = True) -> str:
    return capture(["git", *args], repo, check=check)


def git_code(repo: Path, *args: str) -> int:
    return subprocess.run(
        ["git", *args],
        cwd=repo,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    ).returncode


def git_nul_paths(repo: Path, *args: str) -> list[str]:
    """Return raw Git path records without C-quoting unusual filenames."""

    completed = subprocess.run(
        ["git", *args],
        cwd=repo,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        detail = os.fsdecode(completed.stderr).strip()
        raise CampaignError(
            f"{command_text(['git', *args])} failed with "
            f"{completed.returncode}: {detail}"
        )
    if completed.stdout and not completed.stdout.endswith(b"\0"):
        raise CampaignError("Git returned a malformed NUL-delimited path list")
    return [
        os.fsdecode(path)
        for path in completed.stdout.split(b"\0")
        if path
    ]


def ensure_repo(repo: Path) -> None:
    if not (repo / ".git").exists():
        raise CampaignError(f"{repo} is not a standalone Git checkout")
    dirty = git(repo, "status", "--porcelain", "--untracked-files=normal")
    if dirty:
        raise CampaignError(
            "automation checkout has edits or untracked files; refusing to mix "
            "them into a cycle"
        )


def bootstrap_checkout(repo: Path, remote: str, base_branch: str) -> str | None:
    """Fast-forward the controller checkout before trusting repo policy files.

    The remote and branch are command-line bootstrap roots, not values loaded
    from the possibly stale lane manifest.  A changed checkout must be
    re-executed by the caller so the fetched controller code parses and admits
    the fetched manifests and branches.
    """

    ensure_repo(repo)
    if (
        not remote
        or remote.startswith("-")
        or any(character.isspace() for character in remote)
    ):
        raise CampaignError(f"unsafe bootstrap remote name {remote!r}")
    if (
        not base_branch
        or base_branch.startswith("-")
        or git_code(repo, "check-ref-format", f"refs/heads/{base_branch}") != 0
    ):
        raise CampaignError(f"unsafe bootstrap branch name {base_branch!r}")
    current_branch = git(repo, "branch", "--show-current")
    if current_branch != base_branch:
        raise CampaignError(
            f"automation checkout is on {current_branch!r}, expected "
            f"bootstrap branch {base_branch!r}"
        )
    fetch = subprocess.run(
        ["git", "fetch", "--prune", "--", remote],
        cwd=repo,
        text=True,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if fetch.returncode != 0:
        raise CampaignError(
            "bootstrap git fetch failed: "
            + (fetch.stderr.strip() or fetch.stdout.strip())
        )
    remote_ref = f"refs/remotes/{remote}/{base_branch}"
    remote_sha = git(repo, "rev-parse", "--verify", remote_ref)
    local_sha = git(repo, "rev-parse", "HEAD")
    if local_sha == remote_sha:
        return None
    if git_code(repo, "merge-base", "--is-ancestor", local_sha, remote_sha) != 0:
        raise CampaignError(
            f"automation checkout {local_sha} diverged from {remote_ref} "
            f"{remote_sha}; refusing a non-fast-forward bootstrap"
        )
    update = subprocess.run(
        ["git", "merge", "--ff-only", remote_sha],
        cwd=repo,
        text=True,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if update.returncode != 0:
        raise CampaignError(
            "bootstrap fast-forward failed: "
            + (update.stderr.strip() or update.stdout.strip())
        )
    if git(repo, "rev-parse", "HEAD") != remote_sha:
        raise CampaignError("bootstrap fast-forward did not reach the fetched base")
    return remote_sha


def reexec_updated_controller(repo: Path, updated_sha: str) -> None:
    script = (repo / "scripts" / "continuous_benchmark.py").resolve()
    if not script.is_file() or script.is_symlink():
        raise CampaignError(f"updated controller is not a regular file: {script}")
    attempts_raw = os.environ.get("AY_CONTINUOUS_BOOTSTRAP_ATTEMPTS", "0")
    try:
        attempts = int(attempts_raw)
    except ValueError as error:
        raise CampaignError("invalid bootstrap attempt counter") from error
    if attempts >= 3:
        raise CampaignError(
            "remote base changed during three controller bootstrap attempts"
        )
    env = os.environ.copy()
    env["AY_CONTINUOUS_BOOTSTRAP_ATTEMPTS"] = str(attempts + 1)
    env["AY_CONTINUOUS_BOOTSTRAPPED_SHA"] = updated_sha
    print(
        f"continuous-benchmark: controller fast-forwarded to {updated_sha}; "
        "re-executing fetched policy",
        file=sys.stderr,
        flush=True,
    )
    os.execve(sys.executable, [sys.executable, str(script), *sys.argv[1:]], env)


def ensure_git_identity(repo: Path) -> dict[str, str]:
    name = git(repo, "config", "--get", "user.name", check=False)
    email = git(repo, "config", "--get", "user.email", check=False)
    if not name:
        name = "AY Continuous Benchmark"
        git(repo, "config", "user.name", name)
    if not email:
        email = "continuous-benchmark@localhost"
        git(repo, "config", "user.email", email)
    return {"name": name, "email": email}


def excluded_branch(name: str, patterns: list[str]) -> bool:
    return any(fnmatch.fnmatchcase(name, pattern) for pattern in patterns)


def normalized_repo_path(path: str) -> str | None:
    normalized = path.replace("\\", "/")
    while normalized.startswith("./"):
        normalized = normalized[2:]
    if normalized.startswith("/") or ".." in normalized.split("/"):
        return None
    return normalized


def integration_path_is_protected(path: str) -> bool:
    """Return whether a topic changes the campaign's trusted control plane."""

    normalized = normalized_repo_path(path)
    if normalized is None:
        return True
    name = normalized.rsplit("/", 1)[-1]
    return (
        normalized
        in {
            "Cargo.lock",
            "rust-toolchain",
            "rust-toolchain.toml",
        }
        or name in {"AGENTS.md", "Cargo.toml", "build.rs"}
        or normalized.startswith(INTEGRATION_POLICY_PREFIXES)
    )


def integration_policy_changes(
    repo: Path,
    base_sha: str,
    branch_sha: str,
    *,
    merge_tree: str | None = None,
) -> list[str]:
    if merge_tree is None:
        diff_args = [f"{base_sha}...{branch_sha}"]
    else:
        diff_args = [base_sha, merge_tree]
    paths = git_nul_paths(
        repo,
        "diff",
        "-z",
        "--name-only",
        "--diff-filter=ACDMRTUXB",
        *diff_args,
        "--",
    )
    return sorted(path for path in paths if integration_path_is_protected(path))


def prospective_merge_tree(repo: Path, base_sha: str, branch_sha: str) -> str | None:
    """Return the exact recursive merge tree, or None when the merge conflicts."""

    completed = subprocess.run(
        [
            "git",
            "merge-tree",
            "--write-tree",
            "--no-messages",
            base_sha,
            branch_sha,
        ],
        cwd=repo,
        text=True,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        return None
    first_line = completed.stdout.splitlines()[0] if completed.stdout else ""
    if (
        len(first_line) not in {40, 64}
        or any(character not in "0123456789abcdef" for character in first_line)
    ):
        raise CampaignError(
            f"git merge-tree returned an invalid tree id for {branch_sha}"
        )
    return first_line


def remote_heads(repo: Path, remote: str) -> dict[str, str]:
    output = git(
        repo,
        "for-each-ref",
        "--format=%(refname:strip=3)%09%(objectname)",
        f"refs/remotes/{remote}/",
    )
    heads: dict[str, str] = {}
    for line in output.splitlines():
        name, separator, sha = line.partition("\t")
        if not separator or name == "HEAD":
            continue
        heads[name] = sha
    return heads


def classify_branches(
    repo: Path,
    remote: str,
    base_branch: str,
    heads: dict[str, str],
    exclude: list[str],
) -> list[BranchRecord]:
    base_sha = heads[base_branch]
    records: list[BranchRecord] = []
    for name, sha in sorted(heads.items()):
        if name == base_branch:
            records.append(BranchRecord(name, sha, "base"))
            continue
        if excluded_branch(name, exclude):
            records.append(BranchRecord(name, sha, "excluded"))
            continue
        if git_code(repo, "merge-base", "--is-ancestor", sha, base_sha) == 0:
            records.append(BranchRecord(name, sha, "ancestor"))
            continue
        merge_tree = prospective_merge_tree(repo, base_sha, sha)
        base_tree = git(repo, "rev-parse", f"{base_sha}^{{tree}}")
        if merge_tree == base_tree:
            records.append(
                BranchRecord(
                    name,
                    sha,
                    "patch-equivalent",
                    "merging the snapshotted topic produces the exact base tree",
                )
            )
            continue
        policy_changes = integration_policy_changes(
            repo,
            base_sha,
            sha,
            merge_tree=merge_tree,
        )
        if policy_changes:
            examples = ", ".join(policy_changes[:5])
            if len(policy_changes) > 5:
                examples += f", … (+{len(policy_changes) - 5})"
            records.append(
                BranchRecord(
                    name,
                    sha,
                    "policy-review",
                    "manual admission required for trusted campaign changes: "
                    + examples,
                )
            )
            continue
        cherry = git(repo, "cherry", base_sha, sha)
        unique = [line for line in cherry.splitlines() if line.startswith("+ ")]
        detail = (
            f"{len(unique)} unique patch(es)"
            if unique
            else "prospective merge changes the base tree via merge/resolution state"
        )
        records.append(
            BranchRecord(
                name,
                sha,
                "unique",
                detail,
            )
        )
    return records


def sort_unique_branches(
    repo: Path,
    base_sha: str,
    records: list[BranchRecord],
) -> list[BranchRecord]:
    def key(record: BranchRecord) -> tuple[int, str]:
        count = git(repo, "rev-list", "--count", f"{base_sha}..{record.sha}")
        return (int(count), record.name)

    return sorted(
        (record for record in records if record.classification == "unique"),
        key=key,
    )


def expand_command(
    row: list[str],
    *,
    cargo: str,
    target: Path,
    ay: Path,
) -> list[str]:
    substitutions = {
        "{cargo}": cargo,
        "{target}": str(target),
        "{ay}": str(ay),
    }
    expanded: list[str] = []
    for part in row:
        for token, value in substitutions.items():
            part = part.replace(token, value)
        expanded.append(part)
    return expanded


def _sandbox_parent_directories(paths: Iterable[Path]) -> list[Path]:
    parents: set[Path] = set()
    for path in paths:
        for parent in path.parents:
            if parent == Path("/"):
                break
            if parent == Path("/dev"):
                break
            if parent in {Path("/usr"), Path("/bin"), Path("/lib"), Path("/lib64"), Path("/etc"), Path("/sys")}:
                break
            if parent == Path("/tmp"):
                break
            parents.add(parent)
    return sorted(parents, key=lambda path: (len(path.parts), str(path)))


def sandbox_command(
    argv: list[str],
    *,
    repo: Path,
    worktree: Path,
    writable_paths: list[Path],
    read_only_paths: list[Path] | None = None,
    env: dict[str, str],
) -> list[str]:
    """Wrap candidate execution in a no-network, credential-free filesystem."""

    bwrap = shutil.which("bwrap")
    if bwrap is None:
        raise CampaignError("bubblewrap is required for untrusted candidate execution")

    task_home = Path.home()
    cargo_home = task_home / ".cargo"
    rustup_home = task_home / ".rustup"
    local_bin = task_home / ".local" / "bin"
    local_opt = task_home / ".local" / "opt"
    target = Path(env["CARGO_TARGET_DIR"])
    zig_caches = [target / ".zig-global", target / ".zig-local"]
    for path in [*writable_paths, *zig_caches]:
        path.mkdir(mode=0o700, parents=True, exist_ok=True)

    lock_path = Path(_oom_guard._host_harness_lease_path())
    if not lock_path.is_file():
        raise CampaignError(f"host resource lease is not initialized: {lock_path}")

    read_only = [
        path
        for path in [
            Path("/usr"),
            Path("/bin"),
            Path("/lib"),
            Path("/lib64"),
            Path("/etc"),
            Path("/sys"),
            cargo_home / "bin",
            cargo_home / "registry",
            cargo_home / "git",
            rustup_home,
            local_bin,
            local_opt,
            repo / ".git",
            worktree / ".git",
            *(read_only_paths or []),
        ]
        if path.exists()
    ]
    destinations = [worktree, lock_path, *read_only, *writable_paths]
    command = [
        bwrap,
        "--die-with-parent",
        "--unshare-net",
        "--unshare-pid",
        "--clearenv",
        "--ro-bind",
        "/usr",
        "/usr",
    ]
    for path in [Path("/bin"), Path("/lib"), Path("/lib64"), Path("/etc"), Path("/sys")]:
        if path.exists():
            command.extend(["--ro-bind", str(path), str(path)])
    command.extend(
        [
            "--proc",
            "/proc",
            "--dev",
            "/dev",
            "--tmpfs",
            "/tmp",
            "--size",
            str(64 * 1024 * 1024),
            "--tmpfs",
            "/run",
        ]
    )
    for parent in _sandbox_parent_directories(destinations):
        command.extend(["--dir", str(parent)])
    command.extend(["--ro-bind", str(worktree), str(worktree)])
    for path in read_only:
        if path == worktree:
            continue
        command.extend(["--ro-bind", str(path), str(path)])
    for path in writable_paths:
        command.extend(["--bind", str(path), str(path)])
    # Candidate code only needs to observe that the controller owns this
    # host-wide coordination inode. Never let an integrated topic mutate
    # persistent host state outside its bounded target directory.
    command.extend(["--ro-bind", str(lock_path), str(lock_path)])
    command.extend(["--dir", "/tmp/home", "--chdir", str(worktree), "--clearenv"])

    sandbox_env = {
        "HOME": "/tmp/home",
        "USER": os.environ.get("USER", "ay-continuous"),
        "LOGNAME": os.environ.get("LOGNAME", "ay-continuous"),
        # Authenticate the build-only resource environment for nested tooling.
        # This marker never grants a capability by itself; the outer controller
        # still owns the host lease and supplies the bounded plan below.
        BUILD_SANDBOX_MARKER: "1",
        "PATH": f"{cargo_home}/bin:{local_bin}:/usr/local/bin:/usr/bin:/bin",
        "CARGO_HOME": str(cargo_home),
        "RUSTUP_HOME": str(rustup_home),
        "CARGO_NET_OFFLINE": "true",
        "CARGO_INCREMENTAL": "0",
        "ZIG_GLOBAL_CACHE_DIR": str(zig_caches[0]),
        "ZIG_LOCAL_CACHE_DIR": str(zig_caches[1]),
        "TMPDIR": "/tmp",
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
    }
    for key in (
        "CARGO_TARGET_DIR",
        "AY_BENCH_RESULTS_ROOT",
        "AY_BENCH_STORE_PATH",
        CONTINUOUS_HEADROOM_ENV,
        CONTINUOUS_JOBS_ENV,
        "AY_CONTINUOUS_MEMLIMIT_MB",
        CARGO_BUILD_JOBS_ENV,
        "MEMLIMIT",
        "NBCORE",
        PARENT_LEASE_ENV,
        "CC",
        "CXX",
        "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER",
        "Z3_BIN",
        "Z3_LIB",
    ):
        if key in env:
            sandbox_env[key] = env[key]
    for key, value in sandbox_env.items():
        command.extend(["--setenv", key, value])
    command.extend(["--", *argv])
    return file_size_limited_command(command)


@contextlib.contextmanager
def planned_build_resources(label: str) -> Iterable[Any]:
    """Hold the host benchmark lease while build/test processes are active."""

    try:
        plan = _oom_guard.plan_solver_resources(
            1,
            label=label,
            acquire_lease=True,
        )
    except (RuntimeError, ValueError, OSError) as error:
        raise CampaignError(f"cannot admit {label}: {error}") from error
    try:
        yield plan
    finally:
        _oom_guard._release_harness_lease()


def resource_plan_json(plan: Any) -> dict[str, int]:
    cargo_jobs = planned_build_jobs(plan)
    return {
        "jobs": int(plan.jobs),
        "memlimit_mb": int(plan.memlimit_mb),
        "nbcore": int(plan.nbcore),
        "cargo_jobs": cargo_jobs,
        "headroom_mb": int(plan.headroom_mb),
    }


def planned_build_jobs(plan: Any) -> int:
    """Return the exact Cargo/Targo worker cap for a one-group build plan."""

    outer_jobs = getattr(plan, "jobs", None)
    nbcore = getattr(plan, "nbcore", None)
    if (
        not isinstance(outer_jobs, int)
        or isinstance(outer_jobs, bool)
        or outer_jobs != 1
    ):
        raise CampaignError(
            "build resource plan must admit exactly one process group"
        )
    if not isinstance(nbcore, int) or isinstance(nbcore, bool) or nbcore < 1:
        raise CampaignError("build resource plan requires a positive NBCORE")
    return nbcore


def parent_lease_build_environment(
    env: dict[str, str],
    plan: Any,
) -> dict[str, str]:
    """Return a build-only environment authenticated by the held parent lease."""

    cargo_jobs = planned_build_jobs(plan)
    memory_limit_mb = getattr(plan, "memlimit_mb", None)
    headroom_mb = getattr(plan, "headroom_mb", None)
    if (
        not isinstance(memory_limit_mb, int)
        or isinstance(memory_limit_mb, bool)
        or memory_limit_mb < 1
    ):
        raise CampaignError("build resource plan requires a positive memory limit")
    if (
        not isinstance(headroom_mb, int)
        or isinstance(headroom_mb, bool)
        or headroom_mb < 0
    ):
        raise CampaignError(
            "build resource plan requires non-negative headroom"
        )
    build_env = dict(env)
    build_env.update(
        {
            CONTINUOUS_HEADROOM_ENV: str(headroom_mb),
            CONTINUOUS_JOBS_ENV: str(plan.jobs),
            "AY_CONTINUOUS_MEMLIMIT_MB": str(memory_limit_mb),
            CARGO_BUILD_JOBS_ENV: str(cargo_jobs),
            "MEMLIMIT": str(memory_limit_mb),
            "NBCORE": str(cargo_jobs),
            PARENT_LEASE_ENV: "1",
        }
    )
    return build_env


def build_jobs_from_environment(env: dict[str, str], label: str) -> int:
    """Authenticate the build-driver cap before constructing a child."""

    raw_jobs = env.get(CARGO_BUILD_JOBS_ENV)
    raw_nbcore = env.get("NBCORE")
    raw_memlimit = env.get("MEMLIMIT")
    raw_continuous_memlimit = env.get("AY_CONTINUOUS_MEMLIMIT_MB")
    raw_outer_jobs = env.get(CONTINUOUS_JOBS_ENV)
    raw_headroom = env.get(CONTINUOUS_HEADROOM_ENV)
    try:
        cargo_jobs = int(raw_jobs) if raw_jobs is not None else 0
        nbcore = int(raw_nbcore) if raw_nbcore is not None else 0
        memlimit = int(raw_memlimit) if raw_memlimit is not None else 0
        continuous_memlimit = (
            int(raw_continuous_memlimit)
            if raw_continuous_memlimit is not None
            else 0
        )
        outer_jobs = int(raw_outer_jobs) if raw_outer_jobs is not None else 0
        headroom = int(raw_headroom) if raw_headroom is not None else -1
    except (TypeError, ValueError) as error:
        raise CampaignError(f"{label} parent build plan is malformed") from error
    if env.get(PARENT_LEASE_ENV) != "1":
        raise CampaignError(f"{label} parent resource lease marker is missing")
    if outer_jobs != 1:
        raise CampaignError(f"{label} parent build job count must be one")
    if headroom < 0:
        raise CampaignError(f"{label} parent build headroom is missing")
    if memlimit < 1 or continuous_memlimit < 1:
        raise CampaignError(f"{label} build memory plan is missing")
    if memlimit != continuous_memlimit:
        raise CampaignError(
            f"{label} MEMLIMIT={memlimit} does not match "
            f"AY_CONTINUOUS_MEMLIMIT_MB={continuous_memlimit}"
        )
    if cargo_jobs < 1 or nbcore < 1:
        raise CampaignError(f"{label} build core plan is missing")
    if cargo_jobs != nbcore:
        raise CampaignError(
            f"{label} CARGO_BUILD_JOBS={cargo_jobs} does not match NBCORE={nbcore}"
        )
    return cargo_jobs


def _build_driver_subcommand(argv: list[str]) -> str | None:
    if not argv or Path(argv[0]).name not in BUILD_DRIVER_NAMES:
        return None
    index = 1
    while index < len(argv):
        token = argv[index]
        if token == "--":
            return None
        if token.startswith("+"):
            index += 1
            continue
        if token in BUILD_DRIVER_GLOBAL_OPTIONS_WITH_VALUE:
            if index + 1 >= len(argv):
                raise CampaignError(
                    f"build command has a missing {token} value"
                )
            if token in BUILD_DRIVER_JOB_OPTIONS:
                value = argv[index + 1]
                try:
                    int(value)
                except ValueError as error:
                    raise CampaignError(
                        f"build command has a malformed job count {value!r}"
                    ) from error
            index += 2
            continue
        if any(
            token.startswith(f"{option}=")
            for option in BUILD_DRIVER_GLOBAL_OPTIONS_WITH_VALUE
            if option.startswith("--")
        ):
            index += 1
            continue
        if token.startswith("-"):
            index += 1
            continue
        return token
    return None


def enforce_direct_build_jobs(argv: list[str], cargo_jobs: int) -> list[str]:
    """Pin direct Cargo/Targo build-like commands to the admitted core count."""

    if cargo_jobs < 1:
        raise CampaignError("direct build command requires positive cargo jobs")
    if _build_driver_subcommand(argv) not in BUILD_DRIVER_SUBCOMMANDS:
        return list(argv)

    delimiter = argv.index("--") if "--" in argv else len(argv)
    configured: list[int] = []
    index = 1
    while index < delimiter:
        token = argv[index]
        value: str | None = None
        if token in {"-j", "--jobs"}:
            if index + 1 >= delimiter:
                raise CampaignError(f"build command has a missing {token} value")
            value = argv[index + 1]
            index += 2
        elif token.startswith("--jobs="):
            value = token.partition("=")[2]
            index += 1
        elif token.startswith("-j") and token != "-j":
            value = token[2:].removeprefix("=")
            index += 1
        else:
            index += 1
        if value is None:
            continue
        try:
            configured.append(int(value))
        except ValueError as error:
            raise CampaignError(
                f"build command has a malformed job count {value!r}"
            ) from error

    if len(configured) > 1:
        raise CampaignError("build command has multiple job-count overrides")
    if configured and configured[0] != cargo_jobs:
        raise CampaignError(
            f"build command jobs={configured[0]} conflicts with admitted "
            f"CARGO_BUILD_JOBS={cargo_jobs}"
        )
    if configured:
        return list(argv)
    return [*argv[:delimiter], "-j", str(cargo_jobs), *argv[delimiter:]]


def watchdog_command(
    argv: list[str],
    *,
    memory_limit_mb: int,
    timeout_sec: float,
    label: str,
) -> list[str]:
    """Wrap a no-native-knob child in the repository RSS watchdog."""

    if memory_limit_mb < 1:
        raise CampaignError("RSS watchdog requires a positive memory limit")
    guard = Path(__file__).resolve().with_name("_oom_guard.py")
    if not guard.is_file():
        raise CampaignError(f"OOM watchdog script is missing: {guard}")
    return [
        sys.executable,
        str(guard),
        "run",
        "--limit-mb",
        str(memory_limit_mb),
        "--timeout-s",
        str(timeout_sec),
        "--label",
        label,
        "--",
        *argv,
    ]


def file_size_limited_command(argv: list[str]) -> list[str]:
    prlimit = shutil.which("prlimit")
    if prlimit is None:
        raise CampaignError("prlimit is required for child file-size enforcement")
    return [
        prlimit,
        f"--fsize={MAX_CHILD_FILE_BYTES}",
        "--",
        *argv,
    ]


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return f"sha256:{digest.hexdigest()}"


def freeze_candidate_solver(
    source: Path,
    run_dir: Path,
    *,
    tested_sha: str,
    label: str,
) -> dict[str, Any]:
    """Copy the tested solver into immutable per-run evidence."""

    if (
        not source.is_file()
        or source.is_symlink()
        or not os.access(source, os.X_OK)
    ):
        raise CampaignError(f"candidate solver is not a regular executable: {source}")
    source_metadata = source.stat()
    if source_metadata.st_size < 1 or source_metadata.st_size > MAX_SOLVER_BYTES:
        raise CampaignError(
            f"candidate solver size {source_metadata.st_size} is outside the "
            f"1..{MAX_SOLVER_BYTES} byte envelope"
        )
    destination = run_dir / "candidates" / label / "ay"
    destination.parent.mkdir(mode=0o700, parents=True, exist_ok=False)
    with source.open("rb") as reader, destination.open("xb") as writer:
        shutil.copyfileobj(reader, writer, length=1024 * 1024)
        writer.flush()
        os.fsync(writer.fileno())
    destination.chmod(0o500)
    digest = file_sha256(destination)
    if digest != file_sha256(source):
        raise CampaignError("candidate solver changed while it was being frozen")
    copied_metadata = destination.stat()
    if copied_metadata.st_size != source_metadata.st_size:
        raise CampaignError("candidate solver copy size mismatch")
    return {
        "source_sha": tested_sha,
        "source_path": str(source),
        "path": str(destination),
        "sha256": digest,
        "size_bytes": copied_metadata.st_size,
    }


def solver_launcher_source(
    candidate: Path,
    candidate_sha256: str,
    results_root: Path,
    bwrap: Path,
    runtime_read_only: list[Path],
) -> str:
    """Return a self-contained launcher that survives ay-bench pinning."""

    header = (
        "#!/usr/bin/python3\n"
        f"CANDIDATE = {str(candidate)!r}\n"
        f"CANDIDATE_SHA256 = {candidate_sha256!r}\n"
        f"RESULTS_ROOT = {str(results_root)!r}\n"
        f"BWRAP = {str(bwrap)!r}\n"
        f"RUNTIME_READ_ONLY = {[str(path) for path in runtime_read_only]!r}\n"
    )
    body = r'''
import hashlib
import os
from pathlib import Path
import stat
import sys

FORWARDED_ENV = (
    "MEMLIMIT",
    "NBCORE",
    "AY_SAT_TRACK",
    "AY_SAT_AI_CLASS",
    "AY_SAT_PROFILE_ID",
    "AY_SAT_COMPETITION_PROFILE",
)
CPU_TIMING_NONCE_ENV = "AY_BENCH_CPU_TIMING_NONCE"
CPU_TIMING_PREFIX = "AY_BENCH_CPU_TIME_V1"


def fail(message):
    print(f"continuous solver sandbox: {message}", file=sys.stderr)
    raise SystemExit(125)


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return "sha256:" + digest.hexdigest()


def require_under_results(path, *, regular):
    root = Path(RESULTS_ROOT)
    if not path.is_absolute():
        fail(f"path is not absolute: {path}")
    try:
        resolved = path.resolve(strict=regular)
    except OSError as error:
        fail(f"cannot resolve private path {path}: {error}")
    if resolved != path:
        fail(f"private path is not canonical: {path}")
    candidate = path if regular else path.parent
    try:
        candidate.relative_to(root)
    except ValueError:
        fail(f"private path escapes results root: {path}")
    current = candidate
    while current != root:
        try:
            metadata = current.lstat()
        except OSError as error:
            fail(f"cannot inspect private path {current}: {error}")
        if stat.S_ISLNK(metadata.st_mode):
            fail(f"private path contains a symlink: {current}")
        current = current.parent
    try:
        root_metadata = root.lstat()
    except OSError as error:
        fail(f"cannot inspect results root: {error}")
    if not stat.S_ISDIR(root_metadata.st_mode):
        fail("results root is not a directory")
    if regular:
        metadata = path.lstat()
        if not stat.S_ISREG(metadata.st_mode):
            fail(f"solver input is not a regular file: {path}")
    else:
        if path.exists() or path.is_symlink():
            fail(f"proof output must be absent before solver execution: {path}")
        parent_metadata = path.parent.lstat()
        if not stat.S_ISDIR(parent_metadata.st_mode):
            fail(f"proof staging parent is not a directory: {path.parent}")


def parent_directories(paths):
    parents = set()
    for path in paths:
        for parent in Path(path).parents:
            if parent == Path("/"):
                break
            parents.add(parent)
    return sorted(parents, key=lambda value: (len(value.parts), str(value)))


candidate = Path(CANDIDATE)
if (
    not candidate.is_file()
    or candidate.is_symlink()
    or sha256(candidate) != CANDIDATE_SHA256
):
    fail("frozen candidate identity check failed")

arguments = sys.argv[1:]
version_only = arguments == ["--version"]
cpu_timing_nonce = os.environ.get(CPU_TIMING_NONCE_ENV)
if cpu_timing_nonce is not None and (
    version_only
    or not 1 <= len(cpu_timing_nonce) <= 128
    or any(
        not (character.isascii() and (character.isalnum() or character in "._-"))
        for character in cpu_timing_nonce
    )
):
    fail("invalid CPU timing nonce")
proof_path = None
proof_directory_fd = None
input_path = None
rewritten = list(arguments)
if not version_only:
    if arguments.count("--") != 1:
        fail("expected exactly one solver input delimiter")
    delimiter = arguments.index("--")
    if delimiter != len(arguments) - 2:
        fail("expected exactly one final solver input after `--`")
    input_path = Path(arguments[-1])
    require_under_results(input_path, regular=True)
    proof_positions = [
        index
        for index, value in enumerate(arguments[:delimiter])
        if value == "--proof"
    ]
    if len(proof_positions) > 1:
        fail("multiple proof outputs are not allowed")
    if proof_positions:
        proof_index = proof_positions[0]
        if proof_index + 1 >= delimiter:
            fail("missing proof output argument")
        proof_path = Path(arguments[proof_index + 1])
        require_under_results(proof_path, regular=False)
        proof_directory = proof_path.parent
        proof_directory_metadata = proof_directory.lstat()
        if proof_directory_metadata.st_uid != os.getuid():
            fail(f"proof staging directory is not owned by this user: {proof_directory}")
        if stat.S_IMODE(proof_directory_metadata.st_mode) != 0o700:
            fail(f"proof staging directory is not private: {proof_directory}")
        directory_flags = os.O_RDONLY
        directory_flags |= getattr(os, "O_DIRECTORY", 0)
        directory_flags |= getattr(os, "O_CLOEXEC", 0)
        directory_flags |= getattr(os, "O_NOFOLLOW", 0)
        proof_directory_fd = os.open(proof_directory, directory_flags)
        opened_metadata = os.fstat(proof_directory_fd)
        if (
            not stat.S_ISDIR(opened_metadata.st_mode)
            or (opened_metadata.st_dev, opened_metadata.st_ino)
            != (proof_directory_metadata.st_dev, proof_directory_metadata.st_ino)
        ):
            fail(f"proof staging directory changed while opening: {proof_directory}")
        if os.listdir(proof_directory_fd):
            fail(f"proof staging directory is not empty: {proof_directory}")
        os.set_inheritable(proof_directory_fd, True)
        rewritten[proof_index + 1] = f"/run/ay-proof/{proof_path.name}"
    rewritten[-1] = "/run/ay-input/instance"

runtime_paths = [Path(value) for value in RUNTIME_READ_ONLY]
command = [
    BWRAP,
    "--die-with-parent",
    "--unshare-all",
    "--unshare-user",
    "--disable-userns",
    "--cap-drop",
    "ALL",
    "--clearenv",
    "--ro-bind",
    "/usr",
    "/usr",
]
for system_path in ("/bin", "/lib", "/lib64", "/etc"):
    if Path(system_path).exists():
        command.extend(["--ro-bind", system_path, system_path])
for parent in parent_directories(runtime_paths):
    command.extend(["--dir", str(parent)])
for runtime_path in runtime_paths:
    if runtime_path.exists():
        command.extend(["--ro-bind", str(runtime_path), str(runtime_path)])
command.extend(
    [
        "--proc",
        "/proc",
        "--dev",
        "/dev",
        "--size",
        str(64 * 1024 * 1024),
        "--tmpfs",
        "/tmp",
        "--dir",
        "/solver",
        "--ro-bind",
        str(candidate),
        "/solver/ay",
    ]
)
if not version_only:
    command.extend(
        [
            "--dir",
            "/run",
            "--dir",
            "/run/ay-input",
            "--ro-bind",
            str(input_path),
            "/run/ay-input/instance",
        ]
    )
    if proof_path is not None:
        command.extend(
            [
                "--dir",
                "/run/ay-proof",
                "--bind-fd",
                str(proof_directory_fd),
                "/run/ay-proof",
            ]
        )
command.extend(
    [
        "--chdir",
        "/tmp",
        "--setenv",
        "HOME",
        "/tmp",
        "--setenv",
        "PATH",
        "/usr/bin:/bin",
        "--setenv",
        "LC_ALL",
        "C",
        "--setenv",
        "TZ",
        "UTC",
    ]
)
if runtime_paths:
    command.extend(
        [
            "--setenv",
            "LD_LIBRARY_PATH",
            ":".join(str(path) for path in runtime_paths),
        ]
    )
for key in FORWARDED_ENV:
    value = os.environ.get(key)
    if value is not None:
        if len(value) > 256:
            fail(f"environment value is too long: {key}")
        command.extend(["--setenv", key, value])
solver_command = ["/solver/ay", *rewritten]
if cpu_timing_nonce is not None:
    # This timer must be inside bubblewrap and immediately around the solver.
    # Timing the outer bwrap supervisor omits CPU consumed by the sandboxed
    # child on Linux. The nonce-bound footer gives the trusted Rust harness an
    # unambiguous record while remaining separate from solver verdict parsing.
    solver_command = [
        "/usr/bin/time",
        "-f",
        f"{CPU_TIMING_PREFIX} {cpu_timing_nonce} %U %S",
        *solver_command,
    ]
command.extend(["--", *solver_command])
os.execv(BWRAP, command)
'''
    return header + body


def create_solver_launcher(
    run_dir: Path,
    candidate: dict[str, Any],
    results_root: Path,
    *,
    label: str,
) -> dict[str, Any]:
    """Create the trusted candidate-only bubblewrap boundary."""

    bwrap_value = shutil.which("bwrap")
    if bwrap_value is None:
        raise CampaignError("bubblewrap is required for solver containment")
    bwrap = Path(bwrap_value).resolve()
    time_binary = Path("/usr/bin/time")
    try:
        time_metadata = time_binary.lstat()
    except OSError as error:
        raise CampaignError(
            "GNU /usr/bin/time is required for exact sandbox CPU timing"
        ) from error
    if (
        not stat.S_ISREG(time_metadata.st_mode)
        or time_binary.is_symlink()
        or not os.access(time_binary, os.X_OK)
    ):
        raise CampaignError(
            "GNU /usr/bin/time must be an executable non-symlink regular file"
        )
    try:
        time_version = subprocess.run(
            [str(time_binary), "--version"],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=5,
            check=False,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise CampaignError("cannot probe GNU /usr/bin/time") from error
    if time_version.returncode != 0 or "GNU Time" not in time_version.stdout:
        raise CampaignError(
            "GNU /usr/bin/time is required for nonce-bound sandbox CPU timing"
        )
    runtime_read_only: list[Path] = []
    z3_library = Path.home() / ".local" / "bin" / "libz3.so"
    if z3_library.is_file():
        runtime_read_only.append(z3_library.resolve().parent)
    launcher = run_dir / "trusted-launchers" / label / "ay-sandbox"
    launcher.parent.mkdir(mode=0o700, parents=True, exist_ok=False)
    source = solver_launcher_source(
        Path(candidate["path"]),
        str(candidate["sha256"]),
        results_root.resolve(),
        bwrap,
        runtime_read_only,
    )
    with launcher.open("x", encoding="utf-8") as handle:
        handle.write(source)
        handle.flush()
        os.fsync(handle.fileno())
    launcher.chmod(0o500)
    return {
        **candidate,
        "launcher_path": str(launcher),
        "launcher_sha256": file_sha256(launcher),
        "sandbox": "candidate-only-bubblewrap-v1",
        "results_root": str(results_root.resolve()),
        "runtime_read_only": [str(path) for path in runtime_read_only],
    }


def prepare_candidate_solver(
    source: Path,
    run_dir: Path,
    results_root: Path,
    *,
    tested_sha: str,
    label: str,
) -> dict[str, Any]:
    candidate = freeze_candidate_solver(
        source,
        run_dir,
        tested_sha=tested_sha,
        label=label,
    )
    return create_solver_launcher(
        run_dir,
        candidate,
        results_root,
        label=label,
    )


def trusted_lane_environment(env: dict[str, str], run_dir: Path) -> dict[str, str]:
    """Return the exact non-credential environment for the trusted supervisor."""

    trusted_home = run_dir / "trusted-home"
    trusted_home.mkdir(mode=0o700, parents=True, exist_ok=True)
    results_root = Path(env["AY_BENCH_RESULTS_ROOT"])
    native_tmp = results_root / ".tmp"
    native_tmp.mkdir(mode=0o700, parents=True, exist_ok=True)
    native_tmp_metadata = native_tmp.lstat()
    if (
        not stat.S_ISDIR(native_tmp_metadata.st_mode)
        or native_tmp_metadata.st_uid != os.getuid()
        or stat.S_IMODE(native_tmp_metadata.st_mode) != 0o700
    ):
        raise CampaignError(
            f"trusted native temporary path is not a private owned directory: {native_tmp}"
        )
    local_bin = Path.home() / ".local" / "bin"
    path_entries: list[str] = []
    resolved_z3: Path | None = None
    if z3_value := env.get("Z3_BIN"):
        try:
            resolved_z3 = Path(z3_value).resolve(strict=True)
        except OSError as error:
            raise CampaignError(
                f"cannot resolve trusted Z3 binary {z3_value}: {error}"
            ) from error
        if (
            not resolved_z3.is_file()
            or resolved_z3.is_symlink()
            or not os.access(resolved_z3, os.X_OK)
        ):
            raise CampaignError(
                f"trusted Z3 binary is not an executable regular file: {resolved_z3}"
            )
        path_entries.append(str(resolved_z3.parent))
    path_entries.extend((str(local_bin), "/usr/local/bin", "/usr/bin", "/bin"))
    value = {
        "HOME": str(trusted_home),
        "USER": os.environ.get("USER", "ay-continuous"),
        "LOGNAME": os.environ.get("LOGNAME", "ay-continuous"),
        "PATH": ":".join(path_entries),
        # Native runner input snapshots must live below the launcher's private
        # results root; the candidate boundary rejects ambient /tmp inputs.
        "TMPDIR": str(native_tmp),
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "TZ": "UTC",
        # The candidate path is a trusted launcher that emits exact CPU usage
        # from inside bubblewrap. Do not let the native runner accept the
        # outer bwrap supervisor's near-zero usage as a fallback.
        "AY_BENCH_REQUIRE_SANDBOX_CPU_TIME_V1": "1",
    }
    for key in (
        "AY_BENCH_RESULTS_ROOT",
        "AY_BENCH_STORE_PATH",
        BENCH_CORPUS_ROOT_ENV,
        "MEMLIMIT",
        "NBCORE",
        "Z3_BIN",
        "Z3_LIB",
    ):
        if key in env:
            value[key] = env[key]
    if corpus_value := value.get(BENCH_CORPUS_ROOT_ENV):
        value[BENCH_CORPUS_ROOT_ENV] = str(
            validate_shared_corpus_root(Path(corpus_value))
        )
    if resolved_z3 is not None:
        value["Z3_BIN"] = str(resolved_z3)
    return value


def build_trusted_supervisor(
    repo: Path,
    worktree: Path,
    run_dir: Path,
    env: dict[str, str],
    target: Path,
    writable_paths: list[Path],
    *,
    timeout_sec: float,
) -> tuple[CommandRecord, Path, str]:
    """Build and freeze the base revision's benchmark supervisor."""

    cargo = shutil.which("cargo")
    if cargo is None:
        user_cargo = Path.home() / ".cargo" / "bin" / "cargo"
        cargo = str(user_cargo) if os.access(user_cargo, os.X_OK) else None
    if cargo is None:
        raise CampaignError("cargo is not on PATH")
    cargo_jobs = build_jobs_from_environment(env, "trusted supervisor")
    argv = enforce_direct_build_jobs(
        [
            cargo,
            "build",
            "--release",
            "-p",
            "ay",
            "--features",
            "bench",
        ],
        cargo_jobs,
    )
    sandboxed = sandbox_command(
        argv,
        repo=repo,
        worktree=worktree,
        writable_paths=writable_paths,
        env=env,
    )
    try:
        memory_limit_mb = int(env["AY_CONTINUOUS_MEMLIMIT_MB"])
    except (KeyError, TypeError, ValueError) as error:
        raise CampaignError("trusted supervisor memory plan is missing") from error
    guarded = watchdog_command(
        sandboxed,
        memory_limit_mb=memory_limit_mb,
        timeout_sec=timeout_sec,
        label="continuous-trusted-supervisor-build",
    )
    record = run_command(
        guarded,
        worktree,
        run_dir / "gates" / "00-trusted-supervisor.log",
        env=env,
        timeout=timeout_sec + 60,
    )
    if record.exit_code != 0:
        raise CampaignError("trusted base benchmark supervisor build failed")
    source = target / "release" / "ay"
    if not source.is_file() or source.is_symlink() or not os.access(source, os.X_OK):
        raise CampaignError(f"trusted supervisor binary is invalid: {source}")
    destination = run_dir / "trusted-supervisor" / "ay"
    destination.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    with source.open("rb") as reader, destination.open("xb") as writer:
        shutil.copyfileobj(reader, writer, length=1024 * 1024)
        writer.flush()
        os.fsync(writer.fileno())
    destination.chmod(0o500)
    digest = file_sha256(destination)
    if digest != file_sha256(source):
        raise CampaignError("trusted supervisor copy hash mismatch")
    return record, destination, digest


def fetch_trusted_dependencies(
    worktree: Path,
    run_dir: Path,
    *,
    timeout_sec: float = 900,
) -> CommandRecord:
    """Populate Cargo's cache from the trusted base before offline builds.

    Candidate branches cannot change Cargo manifests or the lockfile without
    being quarantined by the integration policy. Fetching here, before any
    topic is merged, therefore gives network access only to the already
    trusted base and lets every subsequent candidate command stay offline.
    """

    cargo = shutil.which("cargo")
    if cargo is None:
        user_cargo = Path.home() / ".cargo" / "bin" / "cargo"
        cargo = str(user_cargo) if os.access(user_cargo, os.X_OK) else None
    if cargo is None:
        raise CampaignError("cargo is not on PATH")
    return run_command(
        [cargo, "fetch", "--locked"],
        worktree,
        run_dir / "gates" / "00-dependency-fetch.log",
        env={"CARGO_NET_OFFLINE": "false"},
        timeout=timeout_sec,
    )


def execute_build_gates(
    manifest: dict[str, Any],
    repo: Path,
    worktree: Path,
    run_dir: Path,
    env: dict[str, str],
    target: Path,
    writable_paths: list[Path],
) -> list[CommandRecord]:
    cargo = shutil.which("cargo")
    if cargo is None:
        user_cargo = Path.home() / ".cargo" / "bin" / "cargo"
        cargo = str(user_cargo) if os.access(user_cargo, os.X_OK) else None
    if cargo is None:
        raise CampaignError("cargo is not on PATH")
    ay = target / "release" / "ay"
    commands = manifest.get("build", {}).get("commands", [])
    if not commands:
        raise CampaignError("lane manifest contains no build.commands")
    timeout_sec = float(manifest.get("build", {}).get("timeout_sec", 3600))
    gate_env = dict(env)
    gate_evidence = target / "gate-evidence"
    gate_results = gate_evidence / "results"
    gate_store = gate_evidence / "store"
    gate_results.mkdir(mode=0o700, parents=True, exist_ok=True)
    gate_store.mkdir(mode=0o700, parents=True, exist_ok=True)
    gate_env["AY_BENCH_RESULTS_ROOT"] = str(gate_results)
    gate_env["AY_BENCH_STORE_PATH"] = str(gate_store / "results.sqlite")
    cargo_jobs = build_jobs_from_environment(gate_env, "build gate")
    try:
        memory_limit_mb = int(gate_env["AY_CONTINUOUS_MEMLIMIT_MB"])
    except (KeyError, TypeError, ValueError) as error:
        raise CampaignError("build gate memory plan is missing") from error
    records: list[CommandRecord] = []
    for index, row in enumerate(commands, start=1):
        if not isinstance(row, list) or not all(isinstance(v, str) for v in row):
            raise CampaignError("each build command must be an argv string array")
        argv = expand_command(row, cargo=cargo, target=target, ay=ay)
        argv = enforce_direct_build_jobs(argv, cargo_jobs)
        sandboxed = sandbox_command(
            argv,
            repo=repo,
            worktree=worktree,
            writable_paths=writable_paths,
            env=gate_env,
        )
        guarded = watchdog_command(
            sandboxed,
            memory_limit_mb=memory_limit_mb,
            timeout_sec=timeout_sec,
            label=f"continuous-build-gate-{index}",
        )
        record = run_command(
            guarded,
            worktree,
            run_dir / "gates" / f"{index:02d}.log",
            env=gate_env,
            timeout=timeout_sec + 60,
        )
        records.append(record)
        if record.exit_code != 0:
            break
    return records


def _yaml_scalar(value: str) -> str:
    value = value.split(" #", 1)[0].strip()
    if (
        len(value) >= 2
        and value[0] == value[-1]
        and value[0] in {'"', "'"}
    ):
        return value[1:-1]
    return value


def eval_registry_inputs(worktree: Path, eval_id: str) -> dict[str, Any]:
    path = worktree / "evals" / "registry" / f"{eval_id}.yaml"
    try:
        text = read_bounded_regular_text(path)
    except CampaignError as error:
        raise CampaignError(f"cannot read eval registry entry {path}: {error}") from error

    inputs: dict[str, Any] = {}
    declared_id: str | None = None
    in_inputs = False
    list_key: str | None = None
    for line_number, raw in enumerate(text.splitlines(), start=1):
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            continue
        indent = len(raw) - len(raw.lstrip(" "))
        if "\t" in raw[: len(raw) - len(raw.lstrip())]:
            raise CampaignError(f"{path}:{line_number}: tabs are not supported")
        if indent == 0:
            in_inputs = stripped == "inputs:"
            list_key = None
            if stripped.startswith("id:"):
                declared_id = _yaml_scalar(stripped.split(":", 1)[1])
            continue
        if not in_inputs:
            continue
        if indent == 2 and ":" in stripped:
            key, value = stripped.split(":", 1)
            key = key.strip()
            value = _yaml_scalar(value)
            if key == "suite_dirs" and not value:
                inputs[key] = []
                list_key = key
            else:
                inputs[key] = value
                list_key = None
            continue
        if (
            indent == 4
            and list_key == "suite_dirs"
            and stripped.startswith("- ")
        ):
            inputs[list_key].append(_yaml_scalar(stripped[2:]))
            continue
        if indent <= 2:
            list_key = None

    if declared_id not in (None, eval_id):
        raise CampaignError(
            f"eval registry identity mismatch: expected {eval_id!r}, "
            f"found {declared_id!r}"
        )
    return inputs


def _normalized_repo_relative(value: str, label: str) -> Path:
    relative = Path(value)
    if (
        not value
        or relative.is_absolute()
        or any(part in {"", ".", ".."} for part in relative.parts)
        or any(
            ord(character) < 0x20 or 0x7F <= ord(character) <= 0x9F
            for character in value
        )
        or str(relative) != value
    ):
        raise CampaignError(f"{label} is not a normalized repo-relative path: {value!r}")
    return relative


def _repo_relative_input(worktree: Path, value: str, label: str) -> Path:
    return worktree / _normalized_repo_relative(value, label)


def validate_shared_corpus_root(root: Path) -> Path:
    """Validate the trusted persistent checkout used only for corpus payloads."""

    if not root.is_absolute():
        raise CampaignError(
            f"{BENCH_CORPUS_ROOT_ENV} must be an absolute repository root: {root}"
        )
    try:
        resolved = root.resolve(strict=True)
        metadata = root.lstat()
        cargo_metadata = (root / "Cargo.toml").lstat()
        benchmarks_metadata = (root / "benchmarks").lstat()
    except OSError as error:
        raise CampaignError(
            f"cannot validate {BENCH_CORPUS_ROOT_ENV} repository root {root}: {error}"
        ) from error
    if resolved != root:
        raise CampaignError(
            f"{BENCH_CORPUS_ROOT_ENV} must already be canonical: "
            f"{root} resolves to {resolved}"
        )
    if (
        not stat.S_ISDIR(metadata.st_mode)
        or not stat.S_ISREG(cargo_metadata.st_mode)
        or not stat.S_ISDIR(benchmarks_metadata.st_mode)
    ):
        raise CampaignError(
            f"{BENCH_CORPUS_ROOT_ENV} must contain a regular Cargo.toml and "
            f"non-symlink benchmarks directory: {root}"
        )
    return root


def _benchmark_input(
    worktree: Path,
    corpus_root: Path | None,
    value: str,
    label: str,
) -> Path:
    relative = _normalized_repo_relative(value, label)
    if corpus_root is None:
        return worktree / relative
    if not relative.parts or relative.parts[0] != "benchmarks":
        raise CampaignError(
            f"{label} must remain below benchmarks/ when "
            f"{BENCH_CORPUS_ROOT_ENV} is set: {value!r}"
        )
    return corpus_root / relative


def _required_lane_path(
    worktree: Path,
    corpus_root: Path | None,
    value: str,
) -> Path:
    relative = _normalized_repo_relative(value, "lane requires_paths entry")
    candidate = worktree / relative
    # Candidate-worktree controls win whenever they exist. Ignored downloaded
    # corpus paths are absent there and fall back to the persistent checkout.
    if candidate.exists() or candidate.is_symlink():
        return candidate
    if corpus_root is not None and relative.parts[0] == "benchmarks":
        return corpus_root / relative
    return candidate


def _benchmark_file(path: Path, eval_id: str) -> bool:
    name = path.name.lower()
    if eval_id.startswith("sat-") or eval_id.startswith("satcomp-"):
        return name.endswith((".cnf", ".cnf.gz", ".cnf.bz2", ".cnf.xz", ".dimacs"))
    if eval_id.startswith("hwmcc"):
        return name.endswith((".aig", ".aag", ".aig.gz", ".aag.gz"))
    return name.endswith((".smt2", ".smt2.gz", ".smt2.bz2", ".smt2.xz"))


def _yaml_value_without_comment(raw: str) -> str:
    """Strip a YAML comment marker only when it is outside a quoted scalar."""

    value = raw.strip()
    quote: str | None = None
    index = 0
    while index < len(value):
        character = value[index]
        if quote == '"' and character == "\\":
            index += 2
            continue
        if (
            quote == "'"
            and character == "'"
            and index + 1 < len(value)
            and value[index + 1] == "'"
        ):
            index += 2
            continue
        if quote is not None and character == quote:
            quote = None
        elif quote is None and character in {'"', "'"}:
            quote = character
        elif (
            quote is None
            and character == "#"
            and (index == 0 or value[index - 1].isspace())
        ):
            return value[:index].strip()
        index += 1
    return value


def _task_definition_scalar(raw: str, path: Path, line_number: int) -> str:
    """Parse the same narrow YAML string-scalar subset as the native runner."""

    if len(raw.encode("utf-8")) > MAX_YAML_PATH_SCALAR_BYTES + 2:
        raise CampaignError(
            f"set_file task definition {path}:{line_number}: input_files "
            f"exceeds the {MAX_YAML_PATH_SCALAR_BYTES}-byte scalar limit"
        )
    rendered = _yaml_value_without_comment(raw)
    quoted = rendered.startswith(('"', "'"))
    if rendered.startswith('"'):
        body = rendered[1:]
        if "\\" in body:
            raise CampaignError(
                f"set_file task definition {path}:{line_number}: input_files "
                "uses an unsupported double-quoted YAML escape"
            )
        close = body.find('"')
        if close < 0:
            raise CampaignError(
                f"set_file task definition {path}:{line_number}: input_files "
                "has an unterminated double-quoted scalar"
            )
        if body[close + 1 :].strip():
            raise CampaignError(
                f"set_file task definition {path}:{line_number}: input_files "
                "has content after its quoted scalar"
            )
        value = body[:close]
    elif rendered.startswith("'"):
        body = rendered[1:]
        segments: list[str] = []
        segment_start = 0
        index = 0
        while index < len(body):
            if body[index] != "'":
                index += 1
                continue
            segments.append(body[segment_start:index])
            if index + 1 < len(body) and body[index + 1] == "'":
                segments.append("'")
                index += 2
                segment_start = index
                continue
            if body[index + 1 :].strip():
                raise CampaignError(
                    f"set_file task definition {path}:{line_number}: "
                    "input_files has content after its quoted scalar"
                )
            value = "".join(segments)
            break
        else:
            raise CampaignError(
                f"set_file task definition {path}:{line_number}: input_files "
                "has an unterminated single-quoted scalar"
            )
    else:
        value = rendered

    reserved_plain = (
        value == "~"
        or value.lower() == "null"
        or (value and value[0] in ">|[{&*!@`")
    )
    if (
        not value
        or len(value.encode("utf-8")) > MAX_YAML_PATH_SCALAR_BYTES
        or (not quoted and reserved_plain)
    ):
        raise CampaignError(
            f"set_file task definition {path}:{line_number}: input_files must "
            "be a non-empty, well-formed scalar of at most "
            f"{MAX_YAML_PATH_SCALAR_BYTES} bytes"
        )
    return value


def _resolve_set_benchmark_entry(
    benchmarks_dir: Path,
    entry: str,
    *,
    eval_id: str,
) -> Path:
    # Organizer-generated CHC-COMP sets use one harmless "./" prefix. Strip
    # only that exact prefix so repeated or other non-normal components still
    # fail in the shared normalized-path validator.
    normalized_entry = entry[2:] if entry.startswith("./") else entry
    relative = _normalized_repo_relative(
        normalized_entry,
        f"eval {eval_id} set entry",
    )
    declared = benchmarks_dir / relative
    if declared.suffix not in {".yml", ".yaml"}:
        return declared

    try:
        metadata = declared.lstat()
    except OSError as error:
        raise CampaignError(
            f"set_file task definition {declared} cannot be inspected: {error}"
        ) from error
    if not stat.S_ISREG(metadata.st_mode):
        raise CampaignError(
            "set_file task definition must be a regular non-symlink file: "
            f"{declared}"
        )
    try:
        text = read_bounded_regular_text(
            declared,
            max_bytes=MAX_TASK_DEFINITION_BYTES,
        )
    except CampaignError as error:
        raise CampaignError(
            f"cannot read set_file task definition {declared}: {error}"
        ) from error

    input_file: str | None = None
    for line_number, raw_line in enumerate(text.splitlines(), start=1):
        if ":" not in raw_line.lstrip():
            continue
        raw_key, raw_value = raw_line.lstrip().split(":", 1)
        if raw_key.strip() != "input_files":
            continue
        if input_file is not None:
            raise CampaignError(
                f"set_file task definition {declared} repeats input_files"
            )
        value = _task_definition_scalar(raw_value, declared, line_number)
        if value.startswith(("[", "{")):
            raise CampaignError(
                f"set_file task definition {declared} must declare exactly "
                "one scalar input_files path"
            )
        input_file = value

    if input_file is None:
        raise CampaignError(
            f"set_file task definition {declared} has no scalar input_files path"
        )
    input_relative = _normalized_repo_relative(
        input_file,
        "task-definition input_files path",
    )
    return declared.parent / input_relative


def eval_corpus_preflight(
    worktree: Path,
    eval_id: str,
    *,
    corpus_root: Path | None = None,
) -> tuple[int, list[str]]:
    if corpus_root is not None:
        corpus_root = validate_shared_corpus_root(corpus_root)
    inputs = eval_registry_inputs(worktree, eval_id)
    benchmarks_dir_value = str(inputs.get("benchmarks_dir", "")).strip()
    if benchmarks_dir_value:
        candidate_benchmarks_dir = _repo_relative_input(
            worktree,
            benchmarks_dir_value.rstrip("/"),
            f"eval {eval_id} benchmarks_dir",
        )
        benchmarks_dir = _benchmark_input(
            worktree,
            corpus_root,
            benchmarks_dir_value.rstrip("/"),
            f"eval {eval_id} benchmarks_dir",
        )
    else:
        domain = "sat" if eval_id.startswith("sat") else "smt"
        relative_default = f"benchmarks/{domain}"
        candidate_benchmarks_dir = worktree / "benchmarks" / domain
        benchmarks_dir = _benchmark_input(
            worktree,
            corpus_root,
            relative_default,
            f"eval {eval_id} inferred benchmarks_dir",
        )

    errors: list[str] = []
    paths: list[Path] = []
    list_file = str(inputs.get("list_file", "")).strip()
    set_file = str(inputs.get("set_file", "")).strip()
    suite_dirs = inputs.get("suite_dirs")
    try:
        if list_file:
            manifest = _repo_relative_input(
                worktree,
                list_file,
                f"eval {eval_id} list_file",
            )
            text = read_bounded_regular_text(manifest)
            for raw in text.splitlines():
                stripped = raw.strip()
                if not stripped or stripped.startswith("#"):
                    continue
                value = stripped.split()[0]
                path = _benchmark_input(
                    worktree,
                    corpus_root,
                    value,
                    f"eval {eval_id} list entry",
                )
                paths.append(path)
        elif set_file:
            set_relative = _normalized_repo_relative(
                set_file,
                f"eval {eval_id} set_file",
            )
            candidate_manifest = candidate_benchmarks_dir / set_relative
            manifest = (
                candidate_manifest
                if candidate_manifest.is_file()
                and not candidate_manifest.is_symlink()
                else benchmarks_dir / set_relative
            )
            text = read_bounded_regular_text(manifest)
            for raw in text.splitlines():
                stripped = raw.strip()
                if not stripped or stripped.startswith("#"):
                    continue
                paths.append(
                    _resolve_set_benchmark_entry(
                        benchmarks_dir,
                        stripped,
                        eval_id=eval_id,
                    )
                )
        else:
            roots = [benchmarks_dir]
            if isinstance(suite_dirs, list) and suite_dirs:
                roots = []
                for value in suite_dirs:
                    relative = _normalized_repo_relative(
                        str(value),
                        f"eval {eval_id} suite directory",
                    )
                    roots.append(benchmarks_dir / relative)
            for root in roots:
                if not root.is_dir() or root.is_symlink():
                    errors.append(f"benchmark directory is missing: {root}")
                    continue
                paths.extend(
                    path
                    for path in root.rglob("*")
                    if path.is_file()
                    and not path.is_symlink()
                    and _benchmark_file(path, eval_id)
                )
    except FileNotFoundError as error:
        errors.append(f"manifest input is missing: {error.filename}")

    missing = [path for path in paths if not path.is_file() or path.is_symlink()]
    if missing:
        examples = ", ".join(str(path) for path in missing[:8])
        suffix = f", ... ({len(missing) - 8} more)" if len(missing) > 8 else ""
        errors.append(
            f"{len(missing)}/{len(paths)} benchmark input(s) are missing: "
            f"{examples}{suffix}"
        )
    existing = [
        path for path in paths if path.is_file() and not path.is_symlink()
    ]
    try:
        canonical_root = benchmarks_dir.resolve(strict=True)
    except OSError as error:
        errors.append(f"benchmark corpus root cannot be resolved: {error}")
        canonical_root = benchmarks_dir.resolve()
    outside: list[Path] = []
    relative_ids: list[Path] = []
    for path in existing:
        resolved = path.resolve()
        try:
            relative_ids.append(resolved.relative_to(canonical_root))
        except ValueError:
            outside.append(path)
    if outside:
        examples = ", ".join(str(path) for path in outside[:8])
        errors.append(
            f"{len(outside)} benchmark input(s) escape the corpus root: {examples}"
        )
    if (
        eval_id.startswith(("sat-", "satcomp-"))
        and not str(inputs.get("reference_solver", "")).strip()
    ):
        unlabeled = []
        conflicting = []
        for relative in relative_ids:
            labels = {
                part.lower()
                for part in relative.parts
                if part.lower() in {"sat", "unsat"}
            }
            if not labels:
                unlabeled.append(relative)
            elif len(labels) > 1:
                conflicting.append(relative)
        if unlabeled:
            examples = ", ".join(str(path) for path in unlabeled[:8])
            errors.append(
                f"{len(unlabeled)} SAT input(s) lack an authoritative sat/unsat "
                f"path label and no reference solver is configured: {examples}"
            )
        if conflicting:
            examples = ", ".join(str(path) for path in conflicting[:8])
            errors.append(
                f"{len(conflicting)} SAT input(s) have conflicting sat/unsat "
                f"path labels: {examples}"
            )
    canonical = {str(path.resolve()) for path in existing}
    if len(canonical) != len(
        existing
    ):
        errors.append("benchmark manifest contains duplicate or aliased inputs")
    return len(canonical), errors


def lane_blocker(
    lane: dict[str, Any],
    worktree: Path,
    *,
    corpus_root: Path | None = None,
) -> str | None:
    if not lane.get("enabled", True):
        return lane.get("blocked_reason", "lane is disabled")
    if (
        lane.get("kind") == "official" or lane.get("official") is True
    ) and not is_fixed_official_chc_lane(lane):
        return (
            "verified official replay is not implemented: `bench compare` must "
            "verify run class, host, corpus, checker, and reference packet; only "
            "the exact bounded CHC competition-mode lane is admitted"
        )
    try:
        if corpus_root is not None:
            corpus_root = validate_shared_corpus_root(corpus_root)
        missing_paths = [
            value
            for value in lane.get("requires_paths", [])
            if (
                not (
                    required := _required_lane_path(
                        worktree,
                        corpus_root,
                        value,
                    )
                ).exists()
                or required.is_symlink()
            )
        ]
    except CampaignError as error:
        return str(error)
    if missing_paths:
        return "missing path(s): " + ", ".join(missing_paths)
    try:
        benchmark_count, corpus_errors = eval_corpus_preflight(
            worktree,
            str(lane["eval_id"]),
            corpus_root=corpus_root,
        )
    except CampaignError as error:
        return str(error)
    if corpus_errors:
        return "; ".join(corpus_errors)
    minimum = lane.get("min_benchmarks", 1)
    if benchmark_count < minimum:
        return (
            f"corpus admission requires at least {minimum} benchmarks, "
            f"found {benchmark_count}"
        )
    missing_tools = [
        value for value in lane.get("requires_tools", []) if shutil.which(value) is None
    ]
    if missing_tools:
        return "missing tool(s): " + ", ".join(missing_tools)
    return None


def is_fixed_official_chc_lane(lane: dict[str, Any]) -> bool:
    command_timeout = lane.get("command_timeout_sec")
    runs = lane.get("runs")
    shard_index = lane.get("shard_index")
    shard_size = lane.get("shard_size")
    return (
        lane.get("id") == FIXED_OFFICIAL_CHC_LANE_ID
        and lane.get("kind") == "official"
        and lane.get("eval_id") == FIXED_OFFICIAL_CHC_EVAL_ID
        and lane.get("official") is True
        and lane.get("enabled", True) is True
        and isinstance(runs, int)
        and not isinstance(runs, bool)
        and runs == 1
        and isinstance(shard_index, int)
        and not isinstance(shard_index, bool)
        and shard_index == FIXED_OFFICIAL_CHC_SHARD_INDEX
        and isinstance(shard_size, int)
        and not isinstance(shard_size, bool)
        and shard_size == FIXED_OFFICIAL_CHC_SHARD_SIZE
        and "timeout_sec" not in lane
        and isinstance(command_timeout, int)
        and not isinstance(command_timeout, bool)
        and command_timeout == FIXED_OFFICIAL_CHC_COMMAND_TIMEOUT_SEC
        and lane.get("min_benchmarks") == FIXED_OFFICIAL_CHC_MIN_BENCHMARKS
        and lane.get("requires_tools") == ["z3"]
        and lane.get("requires_paths") == [FIXED_OFFICIAL_CHC_SET_PATH]
        and lane.get("competition_refs") == [FIXED_OFFICIAL_CHC_EVAL_ID]
    )


def select_lanes(
    manifest: dict[str, Any],
    state: dict[str, Any],
    worktree: Path,
    *,
    smoke_only: bool,
    include_official: bool,
    corpus_root: Path | None = None,
) -> tuple[list[dict[str, Any]], list[LaneOutcome], int, int]:
    lanes = manifest.get("lane", [])
    canaries = [lane for lane in lanes if lane.get("kind") == "canary"]
    selected = list(canaries)
    blocked: list[LaneOutcome] = []
    rolling = [lane for lane in lanes if lane.get("kind") == "rolling"]
    cursor = int(state.get("rolling_cursor", 0))
    next_cursor = cursor
    next_official_cursor = int(state.get("official_cursor", 0))
    if not smoke_only and rolling:
        for offset in range(len(rolling)):
            index = (cursor + offset) % len(rolling)
            lane = rolling[index]
            blocker = lane_blocker(
                lane,
                worktree,
                corpus_root=corpus_root,
            )
            next_cursor = (index + 1) % len(rolling)
            if blocker is None:
                selected_lane = dict(lane)
                shard_state = state.get("lane_shards", {})
                saved = (
                    shard_state.get(str(lane["id"]), {})
                    if isinstance(shard_state, dict)
                    else {}
                )
                requested_index = (
                    saved.get("next_index", 0) if isinstance(saved, dict) else 0
                )
                if (
                    not isinstance(requested_index, int)
                    or isinstance(requested_index, bool)
                    or requested_index < 0
                ):
                    requested_index = 0
                selected_lane["_shard_index"] = requested_index
                selected.append(selected_lane)
                break
            blocked.append(
                LaneOutcome(
                    lane_id=lane["id"],
                    eval_id=lane["eval_id"],
                    status="blocked",
                    detail=blocker,
                )
            )
    if include_official:
        official = [lane for lane in lanes if lane.get("kind") == "official"]
        if official:
            cursor = next_official_cursor % len(official)
            for offset in range(len(official)):
                index = (cursor + offset) % len(official)
                lane = official[index]
                next_official_cursor = (index + 1) % len(official)
                blocker = lane_blocker(
                    lane,
                    worktree,
                    corpus_root=corpus_root,
                )
                if blocker is None:
                    selected_lane = dict(lane)
                    if is_fixed_official_chc_lane(selected_lane):
                        selected_lane["_shard_index"] = int(
                            selected_lane["shard_index"]
                        )
                    selected.append(selected_lane)
                    break
                blocked.append(
                    LaneOutcome(
                        lane_id=lane["id"],
                        eval_id=lane["eval_id"],
                        status="blocked",
                        detail=blocker,
                    )
                )
    return selected, blocked, next_cursor, next_official_cursor


def numeric_alarm(value: Any, key: str = "") -> bool:
    alarm_keys = {
        "wrong",
        "wrong_answers",
        "invalid",
        "invalidated",
        "disagree",
        "errors",
        "error_count",
        "disqualified",
    }
    normalized = key.lower().replace("-", "_")
    if normalized in alarm_keys:
        if isinstance(value, bool):
            return value
        if isinstance(value, (int, float)):
            return value > 0
        if isinstance(value, list):
            return bool(value)
    if isinstance(value, dict):
        return any(numeric_alarm(child, child_key) for child_key, child in value.items())
    if isinstance(value, list):
        return any(numeric_alarm(child) for child in value)
    return False


def valid_sha256(value: Any) -> bool:
    return (
        isinstance(value, str)
        and value.startswith("sha256:")
        and len(value) == 71
        and all(character in "0123456789abcdef" for character in value[7:])
    )


def exact_cpu_timing_row(
    row: dict[str, Any],
    *,
    expected_source: str,
) -> bool:
    return (
        expected_source in EXACT_CPU_TIME_SOURCES
        and row.get("cpu_time_source") == expected_source
        and finite_nonnegative_number(row.get("cpu_time_sec"))
    )


def finite_nonnegative_number(value: Any) -> bool:
    if not isinstance(value, (int, float)) or isinstance(value, bool):
        return False
    try:
        numeric = float(value)
    except (OverflowError, ValueError):
        return False
    return math.isfinite(numeric) and numeric >= 0


def same_evidence_number(left: Any, right: Any) -> bool:
    return (
        finite_nonnegative_number(left)
        and finite_nonnegative_number(right)
        and math.isclose(float(left), float(right), rel_tol=0.0, abs_tol=1e-9)
    )


def native_reference_agreement(ay_result: str, reference_result: str) -> str:
    ay_definitive = ay_result in {"sat", "unsat"}
    reference_definitive = reference_result in {"sat", "unsat"}
    if ay_definitive and reference_definitive:
        return "agree" if ay_result == reference_result else "disagree"
    if ay_definitive:
        return "ay_only"
    if reference_definitive:
        return "ref_only"
    return "both_unknown"


def round_nonnegative_6(value: float) -> float:
    # Rust's f64::round rounds halfway cases away from zero. CPU and wall
    # aggregates are non-negative, so floor(x + 0.5) reproduces it exactly.
    if not math.isfinite(value):
        return value
    scaled = value * 1_000_000.0
    if not math.isfinite(scaled):
        return value
    return math.floor(scaled + 0.5) / 1_000_000.0


def native_score_evidence(
    items: list[Any],
    *,
    domain: Any,
    timeout_sec: Any,
) -> tuple[dict[str, int | float] | None, list[str]]:
    """Recompute promoted score fields from the native per-instance rows."""

    if domain not in {"sat", "smt", "chc"}:
        return None, [f"cannot reconstruct native score for domain {domain!r}"]
    if domain == "smt" and (
        not finite_nonnegative_number(timeout_sec) or float(timeout_sec) <= 0
    ):
        return None, ["cannot reconstruct SMT score without a positive timeout"]

    errors: list[str] = []
    solved = 0
    solved_sat = 0
    solved_unsat = 0
    cpu_time = 0.0
    for index, item in enumerate(items):
        if not isinstance(item, dict):
            # The outer native-evidence validator reports malformed rows.
            continue
        actual_value = item.get("result")
        if not isinstance(actual_value, str):
            errors.append(
                f"native scoring row {index} lacks a string result identity"
            )
            continue
        actual = actual_value.lower()
        if actual not in {"sat", "unsat"}:
            continue

        expected_value = item.get("expected")
        if expected_value is not None and not isinstance(expected_value, str):
            errors.append(
                f"native scoring row {index} has a malformed expected result"
            )
            continue
        if (
            isinstance(expected_value, str)
            and expected_value.lower() != actual
        ):
            # The Rust scorers exclude wrong answers from solved/CPU totals.
            continue

        item_cpu = 0.0
        if domain in {"smt", "chc"}:
            cpu_value = item.get("cpu_time_sec")
            if not finite_nonnegative_number(cpu_value):
                errors.append(
                    f"native scoring row {index} has an invalid CPU time"
                )
                continue
            item_cpu = float(cpu_value)
            # SMT-COMP sequential scoring discards an otherwise definitive
            # result when CPU time exceeds the timeout.
            if domain == "smt" and item_cpu > float(timeout_sec):
                continue

        solved += 1
        if actual == "sat":
            solved_sat += 1
        else:
            solved_unsat += 1
        cpu_time += item_cpu

    evidence: dict[str, int | float] = {
        "solved": solved,
        "solved_sat": solved_sat,
        "solved_unsat": solved_unsat,
    }
    if domain in {"smt", "chc"}:
        scaled_cpu = cpu_time * 1_000.0
        if not math.isfinite(cpu_time) or not math.isfinite(scaled_cpu):
            errors.append("native scoring CPU total is not finite")
        else:
            # Rust's score serializer rounds non-negative CPU totals to 3 places.
            evidence["cpu_time"] = math.floor(scaled_cpu + 0.5) / 1_000.0
    return evidence, errors


def native_reference_comparison_evidence(
    items: list[Any],
    reference_comparisons: list[Any],
    references: Any,
    *,
    expected_runs: Any,
) -> tuple[set[str], set[str], int | None, list[str]]:
    """Recompute reference identities and summaries from per-run evidence.

    The native runner copies candidate fields into every comparison row and
    selects the lower wall-time median reference run. Treat those copies and
    summaries as checksums, not independent assertions: reconstruct them from
    the candidate item plus nested reference runs and reject any mismatch.
    """

    errors: list[str] = []
    if not reference_comparisons and not isinstance(references, list):
        return set(), set(), None, errors

    candidate_by_file: dict[str, dict[str, Any]] = {}
    ambiguous_candidate_files: set[str] = set()
    for item in items:
        if not isinstance(item, dict):
            continue
        file_name = item.get("file")
        if not isinstance(file_name, str) or not file_name:
            continue
        if file_name in candidate_by_file:
            ambiguous_candidate_files.add(file_name)
            continue
        candidate_by_file[file_name] = item
    for file_name in sorted(ambiguous_candidate_files):
        candidate_by_file.pop(file_name, None)
        errors.append(
            f"candidate benchmark identity {file_name!r} occurs more than once"
        )

    summary_by_name: dict[str, dict[str, Any]] = {}
    duplicate_summary_names: set[str] = set()
    if isinstance(references, list):
        for summary in references:
            if not isinstance(summary, dict):
                continue
            name = summary.get("reference_solver")
            if not isinstance(name, str) or not name:
                continue
            if name in summary_by_name:
                duplicate_summary_names.add(name)
                continue
            summary_by_name[name] = summary
    for name in sorted(duplicate_summary_names):
        summary_by_name.pop(name, None)
        errors.append(f"reference summary {name!r} occurs more than once")

    validated_agree_files: set[str] = set()
    agreeing_reference_names: set[str] = set()
    comparison_names: set[str] = set()
    duplicate_comparison_names: set[str] = set()
    computed_disagreements = 0
    saw_valid_comparison_block = False

    integer_summary_fields = (
        "agree",
        "disagree",
        "ay_only",
        "ref_only",
        "both_solved",
        "ay_faster",
        "ref_faster",
        "cpu_comparable",
        "ay_cpu_faster",
        "ref_cpu_faster",
    )
    numeric_summary_fields = (
        "ay_total_time",
        "ref_total_time",
        "ay_total_cpu_time",
        "ref_total_cpu_time",
    )

    for reference in reference_comparisons:
        if not isinstance(reference, dict):
            continue
        reference_name = reference.get("reference_solver")
        comparisons = reference.get("items")
        if (
            not isinstance(reference_name, str)
            or not reference_name
            or not isinstance(comparisons, list)
        ):
            continue
        if reference_name in comparison_names:
            duplicate_comparison_names.add(reference_name)
            continue
        comparison_names.add(reference_name)
        saw_valid_comparison_block = True

        aggregate: dict[str, int | float] = {
            field: 0 for field in integer_summary_fields
        }
        aggregate.update({field: 0.0 for field in numeric_summary_fields})
        seen_files: set[str] = set()

        for comparison_index, comparison in enumerate(comparisons):
            prefix = (
                f"reference comparison {reference_name!r} item "
                f"{comparison_index}"
            )
            if not isinstance(comparison, dict):
                continue
            file_name = comparison.get("file")
            if not isinstance(file_name, str) or not file_name:
                errors.append(f"{prefix} lacks a benchmark file identity")
                continue
            if file_name in seen_files:
                errors.append(
                    f"reference comparison {reference_name!r} repeats "
                    f"benchmark {file_name!r}"
                )
                continue
            seen_files.add(file_name)
            candidate = candidate_by_file.get(file_name)
            if candidate is None:
                errors.append(
                    f"{prefix} does not identify exactly one candidate item"
                )
                continue

            row_valid = True
            candidate_hash = candidate.get("solver_input_hash")
            comparison_hash = comparison.get("solver_input_hash")
            if not valid_sha256(candidate_hash):
                errors.append(
                    f"candidate item {file_name!r} lacks a valid solver input hash"
                )
                row_valid = False
            if comparison_hash != candidate_hash:
                errors.append(
                    f"{prefix} solver input hash does not match the candidate item"
                )
                row_valid = False

            candidate_result = candidate.get("result")
            if not isinstance(candidate_result, str) or not candidate_result:
                errors.append(
                    f"candidate item {file_name!r} lacks a result identity"
                )
                row_valid = False
                candidate_result = ""
            if comparison.get("ay_result") != candidate_result:
                errors.append(
                    f"{prefix} AY result does not match the candidate item"
                )
                row_valid = False
            candidate_time = candidate.get("time_sec")
            candidate_wall_valid = finite_nonnegative_number(candidate_time)
            if not candidate_wall_valid:
                errors.append(
                    f"candidate item {file_name!r} has an invalid wall time"
                )
                row_valid = False
            if not same_evidence_number(
                comparison.get("ay_time_sec"),
                candidate_time,
            ):
                errors.append(
                    f"{prefix} AY wall time does not match the candidate item"
                )
                row_valid = False
            candidate_cpu_time = candidate.get("cpu_time_sec")
            if not finite_nonnegative_number(candidate_cpu_time):
                errors.append(
                    f"candidate item {file_name!r} has an invalid CPU time"
                )
                row_valid = False
            if not same_evidence_number(
                comparison.get("ay_cpu_time_sec"),
                candidate_cpu_time,
            ):
                errors.append(
                    f"{prefix} AY CPU time does not match the candidate item"
                )
                row_valid = False
            candidate_cpu_source = candidate.get("cpu_time_source")
            if comparison.get("ay_cpu_time_source") != candidate_cpu_source:
                errors.append(
                    f"{prefix} AY CPU source does not match the candidate item"
                )
                row_valid = False
            if (
                candidate_result in {"sat", "unsat"}
                and not exact_cpu_timing_row(
                    candidate,
                    expected_source=CANDIDATE_EXACT_CPU_TIME_SOURCE,
                )
            ):
                row_valid = False

            reference_runs = comparison.get("reference_runs")
            if not isinstance(reference_runs, list) or not reference_runs:
                continue
            if (
                isinstance(expected_runs, int)
                and not isinstance(expected_runs, bool)
                and expected_runs > 0
                and len(reference_runs) != expected_runs
            ):
                errors.append(
                    f"{prefix} has {len(reference_runs)} reference run(s), "
                    f"expected {expected_runs}"
                )
                row_valid = False

            valid_runs: list[dict[str, Any]] = []
            for run_index, reference_run in enumerate(reference_runs):
                run_prefix = f"{prefix} reference run {run_index}"
                if not isinstance(reference_run, dict):
                    row_valid = False
                    continue
                run_result = reference_run.get("result")
                run_time = reference_run.get("time_sec")
                run_cpu_time = reference_run.get("cpu_time_sec")
                run_cpu_source = reference_run.get("cpu_time_source")
                if not isinstance(run_result, str) or not run_result:
                    errors.append(f"{run_prefix} lacks a result identity")
                    row_valid = False
                if not finite_nonnegative_number(run_time):
                    errors.append(f"{run_prefix} has an invalid wall time")
                    row_valid = False
                if not finite_nonnegative_number(run_cpu_time):
                    errors.append(f"{run_prefix} has an invalid CPU time")
                    row_valid = False
                if not isinstance(run_cpu_source, str) or not run_cpu_source:
                    errors.append(f"{run_prefix} lacks a CPU timing source")
                    row_valid = False
                if reference_run.get("solver_input_hash") != comparison_hash:
                    errors.append(
                        f"{run_prefix} solver input hash does not match "
                        "the comparison row"
                    )
                    row_valid = False
                if (
                    run_result in {"sat", "unsat"}
                    and not exact_cpu_timing_row(
                        reference_run,
                        expected_source=REFERENCE_EXACT_CPU_TIME_SOURCE,
                    )
                ):
                    row_valid = False
                if (
                    isinstance(run_result, str)
                    and run_result
                    and finite_nonnegative_number(run_time)
                    and finite_nonnegative_number(run_cpu_time)
                    and isinstance(run_cpu_source, str)
                    and run_cpu_source
                ):
                    valid_runs.append(reference_run)

            if len(valid_runs) != len(reference_runs):
                continue
            consistent_runs = all(
                run["result"] == valid_runs[0]["result"] for run in valid_runs
            )
            if not consistent_runs:
                errors.append(f"{prefix} has inconsistent reference run results")
                row_valid = False
            representative = sorted(
                valid_runs,
                key=lambda run: float(run["time_sec"]),
            )[(len(valid_runs) - 1) // 2]
            representative_result = (
                representative["result"] if consistent_runs else "error"
            )
            if comparison.get("ref_result") != representative_result:
                errors.append(
                    f"{prefix} reference result does not match its repeated runs"
                )
                row_valid = False
            if not same_evidence_number(
                comparison.get("ref_time_sec"),
                representative.get("time_sec"),
            ):
                errors.append(
                    f"{prefix} reference wall time does not match its "
                    "wall-median run"
                )
                row_valid = False
            if not same_evidence_number(
                comparison.get("ref_cpu_time_sec"),
                representative.get("cpu_time_sec"),
            ):
                errors.append(
                    f"{prefix} reference CPU time does not match its "
                    "wall-median run"
                )
                row_valid = False
            if (
                comparison.get("ref_cpu_time_source")
                != representative.get("cpu_time_source")
            ):
                errors.append(
                    f"{prefix} reference CPU source does not match its "
                    "wall-median run"
                )
                row_valid = False

            expected_agreement = native_reference_agreement(
                candidate_result,
                representative_result,
            )
            if comparison.get("agreement") != expected_agreement:
                errors.append(
                    f"{prefix} agreement does not match AY/reference results"
                )
                row_valid = False

            if expected_agreement == "agree":
                aggregate["agree"] += 1
                aggregate["both_solved"] += 1
                if candidate_wall_valid:
                    aggregate["ay_total_time"] += float(candidate_time)
                    aggregate["ref_total_time"] += float(
                        representative["time_sec"]
                    )
                    if float(candidate_time) < float(
                        representative["time_sec"]
                    ):
                        aggregate["ay_faster"] += 1
                    elif float(candidate_time) > float(
                        representative["time_sec"]
                    ):
                        aggregate["ref_faster"] += 1
                if exact_cpu_timing_row(
                    candidate,
                    expected_source=CANDIDATE_EXACT_CPU_TIME_SOURCE,
                ) and exact_cpu_timing_row(
                    representative,
                    expected_source=REFERENCE_EXACT_CPU_TIME_SOURCE,
                ):
                    aggregate["cpu_comparable"] += 1
                    aggregate["ay_total_cpu_time"] += float(candidate_cpu_time)
                    aggregate["ref_total_cpu_time"] += float(
                        representative["cpu_time_sec"]
                    )
                    if float(candidate_cpu_time) < float(
                        representative["cpu_time_sec"]
                    ):
                        aggregate["ay_cpu_faster"] += 1
                    elif float(candidate_cpu_time) > float(
                        representative["cpu_time_sec"]
                    ):
                        aggregate["ref_cpu_faster"] += 1
            elif expected_agreement == "disagree":
                aggregate["disagree"] += 1
                computed_disagreements += 1
            elif expected_agreement == "ay_only":
                aggregate["ay_only"] += 1
            elif expected_agreement == "ref_only":
                aggregate["ref_only"] += 1

            if row_valid and expected_agreement == "agree":
                validated_agree_files.add(file_name)
                agreeing_reference_names.add(reference_name)

        missing_files = sorted(set(candidate_by_file) - seen_files)
        if missing_files:
            errors.append(
                f"reference comparison {reference_name!r} lacks "
                f"{len(missing_files)} candidate benchmark row(s)"
            )

        summary = summary_by_name.get(reference_name)
        if summary is None:
            errors.append(
                f"reference comparison {reference_name!r} lacks a matching summary"
            )
            continue
        for field in integer_summary_fields:
            observed = summary.get(field)
            expected = aggregate[field]
            if (
                isinstance(observed, int)
                and not isinstance(observed, bool)
                and observed >= 0
                and observed != expected
            ):
                errors.append(
                    f"reference summary {reference_name!r} {field}={observed} "
                    f"does not match recomputed {expected}"
                )
        for field in numeric_summary_fields:
            observed = summary.get(field)
            expected = round_nonnegative_6(float(aggregate[field]))
            if (
                finite_nonnegative_number(observed)
                and not math.isclose(
                    float(observed),
                    expected,
                    rel_tol=0.0,
                    abs_tol=1e-9,
                )
            ):
                errors.append(
                    f"reference summary {reference_name!r} {field}={observed} "
                    f"does not match recomputed {expected}"
                )

    for name in sorted(duplicate_comparison_names):
        errors.append(f"reference comparison {name!r} occurs more than once")
    for name in sorted(summary_by_name.keys() - comparison_names):
        errors.append(f"reference summary {name!r} lacks per-benchmark comparisons")

    return (
        validated_agree_files,
        agreeing_reference_names,
        computed_disagreements if saw_valid_comparison_block else None,
        errors,
    )


def native_evidence_summary(
    payload: Any,
    *,
    expected_commit: str | None = None,
    expected_runs: int | None = None,
    expected_timeout_sec: float | None = None,
    expected_corpus_root: Path | None = None,
    expected_official: bool | None = None,
    expected_domain: str | None = None,
) -> dict[str, Any] | None:
    if not isinstance(payload, dict):
        return None
    items = payload.get("items")
    settings = payload.get("settings")
    environment = payload.get("environment")
    if not isinstance(items, list) or not isinstance(settings, dict):
        return None
    environment = environment if isinstance(environment, dict) else {}

    malformed_reference_comparison_rows = 0
    inexact_reference_cpu_rows = 0
    reference_harness_error_rows = 0
    explicit_reference_error_rows = 0
    raw_reference_comparisons = payload.get("reference_comparisons")
    if raw_reference_comparisons is None:
        reference_comparisons: list[Any] = []
    elif isinstance(raw_reference_comparisons, list):
        reference_comparisons = raw_reference_comparisons
    else:
        reference_comparisons = []
        malformed_reference_comparison_rows += 1
    for reference in reference_comparisons:
        if not isinstance(reference, dict):
            malformed_reference_comparison_rows += 1
            continue
        reference_name = reference.get("reference_solver")
        comparisons = reference.get("items")
        if (
            not isinstance(reference_name, str)
            or not reference_name
            or not isinstance(comparisons, list)
        ):
            malformed_reference_comparison_rows += 1
            continue
        for comparison in comparisons:
            if not isinstance(comparison, dict):
                malformed_reference_comparison_rows += 1
                continue
            reference_runs = comparison.get("reference_runs")
            if not isinstance(reference_runs, list) or not reference_runs:
                malformed_reference_comparison_rows += 1
                continue
            for reference_run in reference_runs:
                if not isinstance(reference_run, dict):
                    malformed_reference_comparison_rows += 1
                    continue
                reference_result = str(
                    reference_run.get("result", "")
                ).lower()
                if reference_result == "error":
                    explicit_reference_error_rows += 1
                if reference_run.get("harness_error") not in (None, ""):
                    reference_harness_error_rows += 1
                if (
                    reference_result in DEFINITIVE_RESULTS
                    and not exact_cpu_timing_row(
                        reference_run,
                        expected_source=REFERENCE_EXACT_CPU_TIME_SOURCE,
                    )
                ):
                    inexact_reference_cpu_rows += 1

    corpus_rows: list[tuple[str, str]] = []
    expected_sources: dict[str, int] = {}
    proof_validation: dict[str, int] = {}
    result_counts: dict[str, int] = {}
    candidate_solver_invocations: list[dict[str, Any]] = []
    incomplete_corpus_rows = 0
    malformed_item_rows = 0
    harness_error_rows = 0
    explicit_error_rows = 0
    inexact_candidate_cpu_rows = 0
    for item in items:
        candidate_solver_invocations.append(
            {
                "file": item.get("file") if isinstance(item, dict) else None,
                "solver_input_path": (
                    item.get("solver_input_path")
                    if isinstance(item, dict)
                    else None
                ),
                "solver_argv": (
                    item.get("solver_argv") if isinstance(item, dict) else None
                ),
            }
        )
        if not isinstance(item, dict):
            malformed_item_rows += 1
            continue
        path_value = item.get("benchmark_path", item.get("file"))
        content_hash_value = item.get("benchmark_content_hash")
        path = path_value if isinstance(path_value, str) else ""
        content_hash = (
            content_hash_value if isinstance(content_hash_value, str) else ""
        )
        corpus_rows.append((path, content_hash))
        if not path or not valid_sha256(content_hash):
            incomplete_corpus_rows += 1
        source = str(item.get("expected_source", "unknown"))
        expected_sources[source] = expected_sources.get(source, 0) + 1
        result = str(item.get("result", "")).lower()
        result_counts[result or "missing"] = result_counts.get(result or "missing", 0) + 1
        if result == "error":
            explicit_error_rows += 1
        if item.get("harness_error") not in (None, ""):
            harness_error_rows += 1
        if result in DEFINITIVE_RESULTS and not exact_cpu_timing_row(
            item,
            expected_source=CANDIDATE_EXACT_CPU_TIME_SOURCE,
        ):
            inexact_candidate_cpu_rows += 1
        artifacts = item.get("artifacts")
        if isinstance(artifacts, dict):
            validation = str(artifacts.get("proof_validation", "missing"))
            proof_validation[validation] = proof_validation.get(validation, 0) + 1

    corpus_bytes = json.dumps(sorted(corpus_rows), separators=(",", ":")).encode()
    references = payload.get("references")
    reference_disagreements = 0
    reference_provenance: list[dict[str, Any]] = []
    reference_names: set[str] = set()
    malformed_reference_rows = 0
    if isinstance(references, list):
        for reference in references:
            if not isinstance(reference, dict):
                malformed_reference_rows += 1
                continue
            disagree = reference.get("disagree", 0)
            if isinstance(disagree, int) and not isinstance(disagree, bool):
                reference_disagreements += disagree
            reference_name = reference.get("reference_solver")
            if isinstance(reference_name, str) and reference_name:
                reference_names.add(reference_name)
            reference_provenance.append(
                {
                    key: reference.get(key)
                    for key in (
                        "reference_solver",
                        "reference_solver_path",
                        "reference_solver_sha256",
                        "reference_solver_size_bytes",
                        "reference_solver_version",
                        "reference_solver_build_version",
                        "reference_solver_build_commit",
                        "reference_solver_build_datetime_utc",
                        "reference_solver_build_stamp",
                        "reference_resource_enforcement",
                        "reference_resource_envelope",
                        "agree",
                        "disagree",
                        "ay_only",
                        "ref_only",
                        "both_solved",
                        "ay_faster",
                        "ref_faster",
                        "ay_total_time",
                        "ref_total_time",
                        "cpu_comparable",
                        "ay_cpu_faster",
                        "ref_cpu_faster",
                        "ay_total_cpu_time",
                        "ref_total_cpu_time",
                    )
                }
            )
    elif references is not None:
        malformed_reference_rows += 1
    (
        reference_agree,
        agreeing_reference_names,
        computed_reference_disagreements,
        reference_comparison_evidence_errors,
    ) = native_reference_comparison_evidence(
        items,
        reference_comparisons,
        references,
        expected_runs=settings.get("runs"),
    )
    if computed_reference_disagreements is not None:
        reference_disagreements = computed_reference_disagreements
    unverified_definitive = 0
    for item in items:
        if not isinstance(item, dict):
            continue
        result = str(item.get("result", "")).lower()
        file_value = item.get("file")
        file_name = file_value if isinstance(file_value, str) else ""
        if (
            result in DEFINITIVE_RESULTS
            and item.get("expected") is None
            and file_name not in reference_agree
        ):
            unverified_definitive += 1
    resource_plan = settings.get("resource_plan")
    resource_enforcement = settings.get("resource_enforcement")
    artifact_max_bytes = settings.get("artifact_max_bytes")
    artifact_size_enforcement = settings.get("artifact_size_enforcement")
    native_timeout_sec = settings.get("timeout_sec")
    native_benchmark_count = settings.get("benchmark_count")
    native_runs = settings.get("runs")
    native_shard = settings.get("shard")
    native_benchmarks_dir = settings.get("benchmarks_dir")
    raw_solver_args = settings.get("solver_args", [])
    native_solver_args = (
        list(raw_solver_args)
        if isinstance(raw_solver_args, list)
        and all(isinstance(argument, str) for argument in raw_solver_args)
        else None
    )
    score_evidence, score_evidence_errors = native_score_evidence(
        items,
        domain=settings.get("domain"),
        timeout_sec=native_timeout_sec,
    )
    errors: list[str] = []
    errors.extend(reference_comparison_evidence_errors)
    errors.extend(score_evidence_errors)
    git_commit = environment.get("git_commit")
    if expected_commit is not None and git_commit != expected_commit:
        errors.append(
            f"results commit {git_commit!r} does not match tested commit "
            f"{expected_commit!r}"
        )
    if environment.get("git_dirty") is not False:
        errors.append("results were not produced from a clean Git worktree")
    if not environment.get("ay_sha256"):
        errors.append("solver executable hash is missing")
    if not environment.get("ay_build_stamp"):
        errors.append("solver build stamp is missing")
    if not items:
        errors.append("native result contains no benchmark items")
    if malformed_item_rows:
        errors.append(f"{malformed_item_rows} native benchmark item(s) are malformed")
    if malformed_reference_comparison_rows:
        errors.append(
            f"{malformed_reference_comparison_rows} reference comparison "
            "row(s) are malformed"
        )
    if malformed_reference_rows:
        errors.append(
            f"{malformed_reference_rows} reference provenance row(s) are malformed"
        )
    if inexact_candidate_cpu_rows:
        errors.append(
            f"{inexact_candidate_cpu_rows} definitive candidate result(s) lack "
            "exact child CPU timing"
        )
    if inexact_reference_cpu_rows:
        errors.append(
            f"{inexact_reference_cpu_rows} definitive reference result(s) lack "
            "exact child CPU timing"
        )
    if reference_harness_error_rows:
        errors.append(
            f"{reference_harness_error_rows} reference run(s) contain a "
            "harness error"
        )
    if explicit_reference_error_rows:
        errors.append(
            f"{explicit_reference_error_rows} reference run(s) have an "
            "explicit error result"
        )
    if harness_error_rows:
        errors.append(
            f"{harness_error_rows} benchmark item(s) contain a harness error"
        )
    if explicit_error_rows:
        errors.append(
            f"{explicit_error_rows} benchmark item(s) have an explicit error result"
        )
    if incomplete_corpus_rows:
        errors.append(
            f"{incomplete_corpus_rows} benchmark item(s) lack path/content identity"
        )
    if not isinstance(resource_plan, dict):
        errors.append("native resource plan is missing")
    if not isinstance(resource_enforcement, str) or not resource_enforcement:
        errors.append("native resource enforcement is missing")
    if expected_domain is not None and settings.get("domain") != expected_domain:
        errors.append(
            f"native domain {settings.get('domain')!r} does not match lane "
            f"domain {expected_domain!r}"
        )
    if expected_official is not None and expected_domain == "chc":
        expected_mode = "competition" if expected_official else "dev"
        if native_solver_args is None:
            errors.append(
                f"native CHC {expected_mode} solver_args are missing or malformed"
            )
        elif expected_official:
            expected_solver_args = [
                "--competition",
                "--timeout",
                CHC_COMPETITION_TIMEOUT_MS,
            ]
            if native_solver_args != expected_solver_args:
                errors.append(
                    "native CHC competition solver_args must be exactly "
                    f"{expected_solver_args!r}"
                )
            if (
                not isinstance(native_timeout_sec, (int, float))
                or isinstance(native_timeout_sec, bool)
                or float(native_timeout_sec) != CHC_COMPETITION_TIMEOUT_SEC
            ):
                errors.append(
                    "native CHC competition timeout must equal the standard "
                    f"{CHC_COMPETITION_TIMEOUT_SEC:g}s"
                )
        elif any(
            solver_mode_control_or_delimiter(argument)
            for argument in native_solver_args
        ):
            errors.append(
                "native CHC dev solver_args must omit competition/timeout controls "
                "and argument delimiters"
            )

        memory_mib = (
            resource_plan.get("memlimit_mb_per_child")
            if isinstance(resource_plan, dict)
            else None
        )
        if native_solver_args is not None:
            for index, (item, invocation) in enumerate(
                zip(items, candidate_solver_invocations, strict=True)
            ):
                if not isinstance(item, dict):
                    continue
                solver_input_path = invocation.get("solver_input_path")
                solver_argv = invocation.get("solver_argv")
                expected_suffix = [
                    "--chc",
                    *native_solver_args,
                    "--memory",
                    str(memory_mib),
                    "--",
                    solver_input_path,
                ]
                if (
                    not isinstance(memory_mib, int)
                    or isinstance(memory_mib, bool)
                    or memory_mib < 1
                    or not isinstance(solver_input_path, str)
                    or not solver_input_path
                    or not isinstance(solver_argv, list)
                    or not solver_argv
                    or not all(
                        isinstance(argument, str) for argument in solver_argv
                    )
                    or not solver_argv[0]
                    or solver_argv[1:] != expected_suffix
                ):
                    errors.append(
                        f"native CHC {expected_mode} candidate solver_argv row "
                        f"{index} does not match settings and the enforced envelope"
                    )
    if settings.get("domain") == "sat":
        if (
            not isinstance(artifact_max_bytes, int)
            or isinstance(artifact_max_bytes, bool)
            or artifact_max_bytes < 1
        ):
            errors.append("native SAT proof-artifact size limit is missing")
        if (
            not isinstance(artifact_size_enforcement, str)
            or not artifact_size_enforcement
        ):
            errors.append("native SAT proof-artifact enforcement is missing")
    if (
        not isinstance(native_timeout_sec, (int, float))
        or isinstance(native_timeout_sec, bool)
        or not math.isfinite(float(native_timeout_sec))
        or float(native_timeout_sec) <= 0
    ):
        errors.append("native timeout_sec is not a finite positive number")
    elif expected_timeout_sec is not None and not math.isclose(
        float(native_timeout_sec),
        float(expected_timeout_sec),
        rel_tol=0.0,
        abs_tol=1e-9,
    ):
        errors.append(
            f"native timeout_sec {native_timeout_sec!r} does not match lane "
            f"timeout {expected_timeout_sec!r}"
        )
    if (
        not isinstance(native_benchmark_count, int)
        or isinstance(native_benchmark_count, bool)
        or native_benchmark_count != len(items)
    ):
        errors.append(
            f"native settings benchmark_count {native_benchmark_count!r} does "
            f"not match {len(items)} result item(s)"
        )
    if (
        not isinstance(native_runs, int)
        or isinstance(native_runs, bool)
        or native_runs < 1
    ):
        errors.append("native runs is not a positive integer")
    elif expected_runs is not None and native_runs != expected_runs:
        errors.append(
            f"native runs {native_runs} does not match lane runs {expected_runs}"
        )
    if expected_corpus_root is not None:
        expected_benchmarks_root = expected_corpus_root / "benchmarks"
        if not isinstance(native_benchmarks_dir, str):
            errors.append("native benchmarks_dir is missing")
        else:
            try:
                native_root_path = Path(native_benchmarks_dir)
                resolved_native_root = native_root_path.resolve(strict=True)
                if (
                    not native_root_path.is_absolute()
                    or resolved_native_root != native_root_path
                ):
                    raise ValueError
                native_root_path.relative_to(expected_benchmarks_root)
            except (OSError, ValueError):
                errors.append(
                    f"native benchmarks_dir {native_benchmarks_dir!r} is outside "
                    f"or not canonical below trusted shared corpus root "
                    f"{expected_benchmarks_root}"
                )
    if native_shard is not None:
        if not isinstance(native_shard, dict):
            errors.append("native shard metadata is malformed")
        else:
            shard_integers = (
                "requested_index",
                "shard_index",
                "shard_size",
                "shard_count",
                "corpus_benchmark_count",
                "selected_benchmark_count",
            )
            for field in shard_integers:
                value = native_shard.get(field)
                minimum = 0 if field in {"requested_index", "shard_index"} else 1
                if (
                    not isinstance(value, int)
                    or isinstance(value, bool)
                    or value < minimum
                ):
                    errors.append(f"native shard field {field} is invalid")
            if (
                isinstance(native_shard.get("selected_benchmark_count"), int)
                and native_shard["selected_benchmark_count"] != len(items)
            ):
                errors.append(
                    "native shard selected_benchmark_count does not match result items"
                )
            if (
                isinstance(native_shard.get("shard_index"), int)
                and isinstance(native_shard.get("shard_count"), int)
                and native_shard["shard_index"] >= native_shard["shard_count"]
            ):
                errors.append("native shard index is outside its shard count")
            if not valid_sha256(
                native_shard.get("corpus_path_inventory_sha256")
            ):
                errors.append("native shard corpus path inventory hash is malformed")
            if (
                native_shard.get("selector")
                != "sorted-normalized-id-contiguous-v1"
            ):
                errors.append("native shard selector is unrecognized")
    if unverified_definitive:
        errors.append(
            f"{unverified_definitive} definitive answer(s) lack an authoritative "
            "expected label or agreeing reference"
        )
    if reference_disagreements:
        errors.append(
            f"{reference_disagreements} reference comparison disagreement(s)"
        )
    for index, reference in enumerate(reference_provenance):
        name = reference.get("reference_solver")
        prefix = f"reference provenance row {index}"
        for key in (
            "reference_solver",
            "reference_solver_path",
            "reference_solver_version",
            "reference_solver_build_stamp",
            "reference_resource_enforcement",
            "reference_resource_envelope",
        ):
            if not isinstance(reference.get(key), str) or not reference[key]:
                errors.append(f"{prefix} lacks {key}")
        solver_hash = reference.get("reference_solver_sha256")
        if not valid_sha256(solver_hash):
            errors.append(f"{prefix} has a malformed solver hash")
        solver_size = reference.get("reference_solver_size_bytes")
        if (
            not isinstance(solver_size, int)
            or isinstance(solver_size, bool)
            or solver_size < 1
            or solver_size > MAX_SOLVER_BYTES
        ):
            errors.append(f"{prefix} has an invalid solver size")
        for key in (
            "agree",
            "disagree",
            "ay_only",
            "ref_only",
            "both_solved",
            "ay_faster",
            "ref_faster",
            "cpu_comparable",
            "ay_cpu_faster",
            "ref_cpu_faster",
        ):
            value = reference.get(key)
            if (
                not isinstance(value, int)
                or isinstance(value, bool)
                or value < 0
            ):
                errors.append(f"{prefix} has an invalid {key} counter")
        for key in (
            "ay_total_time",
            "ref_total_time",
            "ay_total_cpu_time",
            "ref_total_cpu_time",
        ):
            value = reference.get(key)
            if (
                not isinstance(value, (int, float))
                or isinstance(value, bool)
                or not math.isfinite(float(value))
                or float(value) < 0
            ):
                errors.append(f"{prefix} has an invalid {key}")
        enforcement = reference.get("reference_resource_enforcement")
        if isinstance(enforcement, str) and not enforcement.startswith(
            "ay-resource-v1:"
        ):
            errors.append(f"{prefix} has an unrecognized resource enforcement")
        if not isinstance(name, str) or not name:
            continue
    missing_reference_provenance = agreeing_reference_names - reference_names
    if missing_reference_provenance:
        errors.append(
            "agreeing reference result lacks provenance for: "
            + ", ".join(sorted(missing_reference_provenance))
        )
    return {
        "git_commit": environment.get("git_commit"),
        "git_dirty": environment.get("git_dirty"),
        "ay_sha256": environment.get("ay_sha256"),
        "ay_build_stamp": environment.get("ay_build_stamp"),
        "benchmark_count": len(items),
        "settings_benchmark_count": native_benchmark_count,
        "timeout_sec": native_timeout_sec,
        "runs": native_runs,
        "domain": settings.get("domain"),
        "expected_domain": expected_domain,
        "solver_role": "candidate",
        "solver_mode": (
            "competition"
            if expected_official is True
            else "dev"
            if expected_official is False
            else None
        ),
        "solver_args": native_solver_args,
        "candidate_solver_invocations": candidate_solver_invocations,
        "benchmarks_dir": native_benchmarks_dir,
        "shard": native_shard,
        "corpus_identity_sha256": hashlib.sha256(corpus_bytes).hexdigest(),
        "resource_plan": resource_plan,
        "resource_enforcement": resource_enforcement,
        "artifact_max_bytes": artifact_max_bytes,
        "artifact_size_enforcement": artifact_size_enforcement,
        "expected_sources": dict(sorted(expected_sources.items())),
        "unverified_definitive": unverified_definitive,
        "reference_disagreements": reference_disagreements,
        "reference_provenance": reference_provenance,
        "harness_error_count": harness_error_rows,
        "explicit_error_count": explicit_error_rows,
        "inexact_candidate_cpu_count": inexact_candidate_cpu_rows,
        "inexact_reference_cpu_count": inexact_reference_cpu_rows,
        "reference_harness_error_count": reference_harness_error_rows,
        "explicit_reference_error_count": explicit_reference_error_rows,
        "proof_validation": dict(sorted(proof_validation.items())),
        "result_counts": dict(sorted(result_counts.items())),
        "score_evidence": score_evidence,
        "evidence_errors": errors,
    }


def _score_count_errors(
    score: dict[str, Any],
    fields: Iterable[str],
) -> list[str]:
    errors: list[str] = []
    for field in fields:
        value = score.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            errors.append(f"score field {field} is not a non-negative integer")
    return errors


def _score_number_errors(
    score: dict[str, Any],
    fields: Iterable[str],
    *,
    positive: bool = False,
) -> list[str]:
    errors: list[str] = []
    for field in fields:
        value = score.get(field)
        valid = (
            isinstance(value, (int, float))
            and not isinstance(value, bool)
            and math.isfinite(float(value))
            and (float(value) > 0 if positive else float(value) >= 0)
        )
        if not valid:
            qualifier = "positive" if positive else "non-negative"
            errors.append(f"score field {field} is not a finite {qualifier} number")
    return errors


def score_shape_errors(score: dict[str, Any], domain: Any) -> list[str]:
    """Validate the exact native score schema and zero all soundness alarms."""

    schemas = {
        "sat": {
            "par2_total",
            "par2_avg",
            "solved",
            "solved_sat",
            "solved_unsat",
            "unsolved",
            "wrong",
            "disqualified",
            "total",
            "timeout_sec",
            "wrong_answers",
        },
        "smt": {
            "division",
            "errors",
            "solved",
            "wall_time",
            "cpu_time",
            "total",
            "solved_sat",
            "solved_unsat",
            "timeout_count",
            "sound",
            "wrong_answers",
        },
        "chc": {
            "track",
            "solved",
            "solved_sat",
            "solved_unsat",
            "cpu_time",
            "unsolved",
            "wrong",
            "total",
            "timeout_sec",
            "wrong_answers",
        },
    }
    if domain not in schemas:
        return [f"unsupported native score domain: {domain!r}"]
    expected = schemas[domain]
    errors: list[str] = []
    missing = sorted(expected - score.keys())
    unknown = sorted(score.keys() - expected)
    if missing:
        errors.append("score lacks required field(s): " + ", ".join(missing))
    if unknown:
        errors.append("score has unknown field(s): " + ", ".join(unknown))

    common_counts = ("total", "solved", "solved_sat", "solved_unsat")
    errors.extend(_score_count_errors(score, common_counts))
    counts_valid = not any(
        not isinstance(score.get(field), int)
        or isinstance(score.get(field), bool)
        or score[field] < 0
        for field in common_counts
    )
    if counts_valid:
        if score["solved_sat"] + score["solved_unsat"] != score["solved"]:
            errors.append("score solved subtype counts do not sum to solved")
        if score["solved"] > score["total"]:
            errors.append("score solved exceeds total")

    wrong_answers = score.get("wrong_answers")
    if not isinstance(wrong_answers, list) or wrong_answers:
        errors.append("score wrong_answers must be an empty array")
    if domain == "sat":
        errors.extend(_score_count_errors(score, ("unsolved", "wrong")))
        errors.extend(_score_number_errors(score, ("par2_total", "par2_avg")))
        errors.extend(_score_number_errors(score, ("timeout_sec",), positive=True))
        if score.get("wrong") != 0:
            errors.append("SAT score has a nonzero wrong-answer count")
        if score.get("disqualified") is not False:
            errors.append("SAT score is disqualified or has malformed status")
        if counts_valid and isinstance(score.get("unsolved"), int):
            if score["solved"] + score["unsolved"] != score["total"]:
                errors.append("SAT solved and unsolved counts do not sum to total")
    elif domain == "smt":
        errors.extend(_score_count_errors(score, ("errors", "timeout_count")))
        errors.extend(_score_number_errors(score, ("wall_time", "cpu_time")))
        if score.get("errors") != 0:
            errors.append("SMT score has a nonzero error count")
        if score.get("sound") is not True:
            errors.append("SMT score is unsound or has malformed status")
        if not isinstance(score.get("division"), str) or not score["division"]:
            errors.append("SMT score division is missing")
    elif domain == "chc":
        errors.extend(_score_count_errors(score, ("unsolved", "wrong")))
        errors.extend(_score_number_errors(score, ("cpu_time",)))
        errors.extend(_score_number_errors(score, ("timeout_sec",), positive=True))
        if score.get("wrong") != 0:
            errors.append("CHC score has a nonzero wrong-answer count")
        if counts_valid and isinstance(score.get("unsolved"), int):
            if score["solved"] + score["unsolved"] != score["total"]:
                errors.append("CHC solved and unsolved counts do not sum to total")
        if not isinstance(score.get("track"), str) or not score["track"]:
            errors.append("CHC score track is missing")
    return errors


def scorecard_evidence_errors(
    scorecard: Any,
    evidence: dict[str, Any],
    *,
    eval_id: str,
    official: bool,
) -> list[str]:
    errors: list[str] = []
    results = scorecard.get("results") if isinstance(scorecard, dict) else None
    if not isinstance(results, list) or len(results) != 1:
        return ["scorecard must contain exactly one eval result"]
    row = results[0]
    if not isinstance(row, dict) or row.get("eval_id") != eval_id:
        return ["scorecard eval identity does not match the selected lane"]
    if row.get("error") is not None:
        errors.append("scorecard contains an eval error")
    if row.get("shard") != evidence.get("shard"):
        errors.append("scorecard shard metadata does not match native evidence")
    score = row.get("score")
    if not isinstance(score, dict):
        return [*errors, "scorecard result lacks a score object"]
    errors.extend(score_shape_errors(score, evidence.get("domain")))
    if evidence.get("domain") in {"sat", "chc"}:
        score_timeout = score.get("timeout_sec")
        evidence_timeout = evidence.get("timeout_sec")
        if (
            not isinstance(score_timeout, (int, float))
            or isinstance(score_timeout, bool)
            or not isinstance(evidence_timeout, (int, float))
            or isinstance(evidence_timeout, bool)
            or not math.isfinite(float(score_timeout))
            or not math.isfinite(float(evidence_timeout))
            or not math.isclose(
                float(score_timeout),
                float(evidence_timeout),
                rel_tol=0.0,
                abs_tol=1e-9,
            )
        ):
            errors.append(
                f"score timeout {score_timeout!r} does not match native "
                f"timeout {evidence_timeout!r}"
            )
    total = score.get("total")
    count = evidence.get("benchmark_count")
    if (
        not isinstance(total, int)
        or isinstance(total, bool)
        or total < 1
        or total != count
    ):
        errors.append(
            f"score total {total!r} does not match native benchmark count {count!r}"
        )
    solved = score.get("solved")
    if solved is not None and (
        not isinstance(solved, int)
        or isinstance(solved, bool)
        or solved < 0
        or not isinstance(total, int)
        or solved > total
    ):
        errors.append(f"score solved count is invalid: {solved!r}")
    raw_score = evidence.get("score_evidence")
    if not isinstance(raw_score, dict):
        errors.append("validated native score evidence is missing")
    else:
        for field in ("solved", "solved_sat", "solved_unsat"):
            expected_value = raw_score.get(field)
            score_value = score.get(field)
            if (
                not isinstance(expected_value, int)
                or isinstance(expected_value, bool)
                or expected_value < 0
            ):
                errors.append(
                    f"validated native score evidence has invalid {field}"
                )
            elif score_value != expected_value:
                errors.append(
                    f"score {field}={score_value!r} does not match raw native "
                    f"{field}={expected_value}"
                )
        if evidence.get("domain") in {"smt", "chc"}:
            expected_cpu = raw_score.get("cpu_time")
            score_cpu = score.get("cpu_time")
            if not same_evidence_number(score_cpu, expected_cpu):
                errors.append(
                    f"score cpu_time={score_cpu!r} does not match raw native "
                    f"cpu_time={expected_cpu!r}"
                )
    for field in ("ay_sha256", "solver_launcher_sha256", "candidate_sha256"):
        solver_hash = evidence.get(field)
        if not valid_sha256(solver_hash):
            errors.append(f"{field} is missing or malformed")
    candidate_size = evidence.get("candidate_size_bytes")
    if (
        not isinstance(candidate_size, int)
        or isinstance(candidate_size, bool)
        or candidate_size < 1
        or candidate_size > MAX_SOLVER_BYTES
    ):
        errors.append("frozen candidate size is missing or invalid")
    if evidence.get("candidate_sandbox") != "candidate-only-bubblewrap-v1":
        errors.append("candidate-only sandbox provenance is missing")
    plan = evidence.get("resource_plan")
    if not isinstance(plan, dict) or any(
        not isinstance(plan.get(key), int)
        or isinstance(plan.get(key), bool)
        or plan[key] < 1
        for key in ("jobs", "memlimit_mb_per_child", "nbcore_per_child")
    ):
        errors.append("native resource plan lacks positive enforced limits")
    enforcement = evidence.get("resource_enforcement")
    if not isinstance(enforcement, str) or not enforcement.startswith(
        "ay-resource-v1:"
    ):
        errors.append("native resource enforcement tag is not recognized")
    if official and evidence.get("domain") == "sat":
        results_by_verdict = evidence.get("result_counts", {})
        validations = evidence.get("proof_validation", {})
        unsat = int(results_by_verdict.get("unsat", 0))
        checked = int(validations.get("checked", 0))
        if unsat > checked:
            errors.append(
                "official SAT UNSAT answers lack per-result checked certificates"
            )
        if int(results_by_verdict.get("sat", 0)) > 0:
            errors.append(
                "official SAT answers lack independently checked model evidence"
            )
    return errors


def new_native_evidence(
    root: Path,
    eval_id: str,
    before: set[Path],
    *,
    expected_commit: str,
    expected_runs: int | None = None,
    expected_timeout_sec: float | None = None,
    expected_corpus_root: Path | None = None,
    expected_official: bool | None = None,
    expected_domain: str | None = None,
) -> tuple[Path | None, dict[str, Any] | None]:
    eval_root = root / eval_id
    if not eval_root.is_dir() or eval_root.is_symlink():
        return None, None
    candidates = sorted(
        (
            path / "results.json"
            for path in eval_root.iterdir()
            if path.is_dir()
            and not path.is_symlink()
            and path.resolve() not in before
            and (path / "results.json").is_file()
            and not (path / "results.json").is_symlink()
        ),
        key=lambda path: path.stat().st_mtime_ns if path.exists() else 0,
    )
    if not candidates:
        return None, None
    evidence_path = candidates[-1]
    payload = read_json(evidence_path, None)
    return evidence_path, native_evidence_summary(
        payload,
        expected_commit=expected_commit,
        expected_runs=expected_runs,
        expected_timeout_sec=expected_timeout_sec,
        expected_corpus_root=expected_corpus_root,
        expected_official=expected_official,
        expected_domain=expected_domain,
    )


def execute_lane(
    lane: dict[str, Any],
    repo: Path,
    worktree: Path,
    run_dir: Path,
    env: dict[str, str],
    supervisor_ay: Path,
    supervisor_sha256: str,
    candidate: dict[str, Any],
    suffix: str = "",
) -> LaneOutcome:
    blocker = lane_blocker(lane, worktree, corpus_root=repo)
    if blocker is not None:
        return LaneOutcome(
            lane_id=lane["id"],
            eval_id=lane["eval_id"],
            status="blocked",
            detail=blocker,
        )
    lane_dir = run_dir / "benchmarks" / f"{lane['id']}{suffix}"
    lane_dir.mkdir(mode=0o700, parents=True, exist_ok=False)
    scorecard = lane_dir / "scorecard.json"
    launcher = Path(str(candidate["launcher_path"]))
    frozen_solver = Path(str(candidate["path"]))
    if file_sha256(launcher) != candidate["launcher_sha256"]:
        raise CampaignError("trusted solver launcher changed before lane execution")
    if file_sha256(frozen_solver) != candidate["sha256"]:
        raise CampaignError("frozen candidate changed before lane execution")
    native_root = Path(env["AY_BENCH_RESULTS_ROOT"])
    eval_root = native_root / lane["eval_id"]
    before = (
        {
            path.resolve()
            for path in eval_root.iterdir()
            if path.is_dir() and not path.is_symlink()
        }
        if eval_root.is_dir() and not eval_root.is_symlink()
        else set()
    )
    argv = [
        str(supervisor_ay),
        "bench",
        "run",
        lane["eval_id"],
        "--ay",
        str(launcher),
        "--runs",
        str(int(lane.get("runs", 1))),
        "--output",
        str(scorecard),
    ]
    if "shard_size" in lane:
        argv.extend(
            [
                "--shard-index",
                str(int(lane.get("_shard_index", 0))),
                "--shard-size",
                str(int(lane["shard_size"])),
            ]
        )
    if lane.get("official", False):
        argv.append("--competition")
    elif "timeout_sec" in lane:
        argv.extend(["--timeout", str(lane["timeout_sec"])])
    timeout = float(lane.get("command_timeout_sec", 2 * 60 * 60))
    record = run_command(
        argv,
        worktree,
        lane_dir / "run.log",
        env=trusted_lane_environment(env, run_dir),
        timeout=timeout,
        abort_on_concurrent_build=True,
        inherit_env=False,
    )
    payload = read_json(scorecard, None)
    expected_commit = git(worktree, "rev-parse", "HEAD")
    evidence_path, evidence = new_native_evidence(
        native_root,
        lane["eval_id"],
        before,
        expected_commit=expected_commit,
        expected_runs=int(lane.get("runs", 1)),
        expected_timeout_sec=(
            float(lane["timeout_sec"]) if "timeout_sec" in lane else None
        ),
        expected_corpus_root=repo,
        expected_official=bool(lane.get("official", False)),
        expected_domain=(
            "chc"
            if lane["eval_id"].startswith(("chccomp-", "chc-"))
            else None
        ),
    )
    supervisor_hash_after = file_sha256(supervisor_ay)
    launcher_hash_after = file_sha256(launcher)
    candidate_hash_after = file_sha256(frozen_solver)
    if evidence is not None:
        evidence["trusted_supervisor_sha256"] = supervisor_hash_after
        evidence["trusted_supervisor_path"] = str(supervisor_ay)
        evidence["solver_launcher_sha256"] = launcher_hash_after
        evidence["solver_launcher_path"] = str(launcher)
        evidence["candidate_sha256"] = candidate_hash_after
        evidence["candidate_path"] = str(frozen_solver)
        evidence["candidate_source_sha"] = candidate.get("source_sha")
        evidence["candidate_size_bytes"] = candidate.get("size_bytes")
        evidence["candidate_sandbox"] = candidate.get("sandbox")
        if evidence.get("ay_sha256") != candidate["launcher_sha256"]:
            evidence.setdefault("evidence_errors", []).append(
                "native solver-launcher hash does not match the trusted launcher"
            )
        if supervisor_hash_after != supervisor_sha256:
            evidence.setdefault("evidence_errors", []).append(
                "trusted benchmark supervisor changed during lane execution"
            )
        if launcher_hash_after != candidate["launcher_sha256"]:
            evidence.setdefault("evidence_errors", []).append(
                "trusted solver launcher changed during lane execution"
            )
        if candidate_hash_after != candidate["sha256"]:
            evidence.setdefault("evidence_errors", []).append(
                "frozen candidate changed during lane execution"
            )
        if candidate.get("source_sha") != expected_commit:
            evidence.setdefault("evidence_errors", []).append(
                "frozen candidate source commit does not match the tested commit"
            )
        shard = evidence.get("shard")
        if "shard_size" in lane:
            if not isinstance(shard, dict):
                evidence.setdefault("evidence_errors", []).append(
                    "selected sharded lane lacks native shard metadata"
                )
            else:
                if shard.get("requested_index") != int(
                    lane.get("_shard_index", 0)
                ):
                    evidence.setdefault("evidence_errors", []).append(
                        "native requested shard index does not match scheduler state"
                    )
                if shard.get("shard_size") != int(lane["shard_size"]):
                    evidence.setdefault("evidence_errors", []).append(
                        "native shard size does not match the lane envelope"
                    )
        elif shard is not None:
            evidence.setdefault("evidence_errors", []).append(
                "unsharded lane unexpectedly produced shard metadata"
            )
        evidence.setdefault("evidence_errors", []).extend(
            scorecard_evidence_errors(
                payload,
                evidence,
                eval_id=lane["eval_id"],
                official=bool(lane.get("official", False)),
            )
        )
    alarm = numeric_alarm(payload) if payload is not None else False
    if evidence is not None:
        alarm = (
            alarm
            or int(evidence.get("unverified_definitive", 0)) > 0
            or int(evidence.get("reference_disagreements", 0)) > 0
            or bool(evidence.get("evidence_errors"))
        )
    if record.exit_code != 0:
        status = "failed"
        detail = f"benchmark command exited {record.exit_code}"
    elif payload is None:
        status = "failed"
        detail = "scorecard missing or invalid"
    elif evidence is None:
        status = "failed"
        detail = "native results evidence missing or invalid"
    elif alarm:
        status = "correctness-alarm"
        detail = "evidence contains wrong, invalid, disputed, or unverified answers"
    else:
        status = "passed"
        detail = "scorecard recorded"
    return LaneOutcome(
        lane_id=lane["id"],
        eval_id=lane["eval_id"],
        status=status,
        detail=detail,
        command=record,
        scorecard_path=str(scorecard) if scorecard.exists() else None,
        scorecard=payload,
        evidence_path=str(evidence_path) if evidence_path is not None else None,
        evidence=evidence,
        shard=(
            dict(evidence["shard"])
            if isinstance(evidence, dict)
            and isinstance(evidence.get("shard"), dict)
            else None
        ),
        correctness_alarm=alarm,
    )


def execute_lanes(
    lanes: list[dict[str, Any]],
    repo: Path,
    worktree: Path,
    run_dir: Path,
    env: dict[str, str],
    supervisor_ay: Path,
    supervisor_sha256: str,
    candidate: dict[str, Any],
    suffix: str = "",
) -> list[LaneOutcome]:
    return [
        execute_lane(
            lane,
            repo,
            worktree,
            run_dir,
            env,
            supervisor_ay,
            supervisor_sha256,
            candidate,
            suffix=suffix,
        )
        for lane in lanes
    ]


def outcomes_clean(outcomes: list[LaneOutcome]) -> bool:
    return all(outcome.status in {"passed", "blocked"} for outcome in outcomes)


def canaries_clean(
    selected: list[dict[str, Any]],
    outcomes: list[LaneOutcome],
) -> bool:
    canary_ids = {
        str(lane["id"]) for lane in selected if lane.get("kind") == "canary"
    }
    if not canary_ids:
        return False
    statuses = {outcome.lane_id: outcome.status for outcome in outcomes}
    return all(statuses.get(lane_id) == "passed" for lane_id in canary_ids)


def official_selection_clean(
    requested: bool,
    selected: list[dict[str, Any]],
    outcomes: list[LaneOutcome],
) -> bool:
    """An official request succeeds only after a selected official lane passes."""

    if not requested:
        return True
    official_ids = {
        str(lane["id"]) for lane in selected if lane.get("kind") == "official"
    }
    if not official_ids:
        return False
    statuses = {outcome.lane_id: outcome.status for outcome in outcomes}
    return all(statuses.get(lane_id) == "passed" for lane_id in official_ids)


def integrations_clean(branches: list[BranchRecord]) -> bool:
    """Return whether every snapshotted topic was integrated or redundant."""

    return all(
        branch.classification not in {"conflicted", "policy-review"}
        for branch in branches
    )


def changed_paths(worktree: Path) -> list[str]:
    tracked = git_nul_paths(
        worktree,
        "diff",
        "-z",
        "--name-only",
        "--diff-filter=ACDMRTUXB",
        "HEAD",
        "--",
    )
    untracked = git_nul_paths(
        worktree,
        "ls-files",
        "-z",
        "--others",
        "--exclude-standard",
    )
    return sorted(set(tracked + untracked))


def repair_residue(worktree: Path) -> bool:
    """Detect any tracked, untracked, or ignored state after repair commit."""

    completed = subprocess.run(
        [
            "git",
            "status",
            "--porcelain=v1",
            "-z",
            "--untracked-files=all",
            "--ignored=matching",
        ],
        cwd=worktree,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        raise CampaignError(
            "cannot verify repair worktree cleanliness: "
            + os.fsdecode(completed.stderr).strip()
        )
    return bool(completed.stdout)


def repair_path_is_protected(path: str) -> bool:
    normalized = normalized_repo_path(path)
    if normalized is None:
        return True
    name = normalized.rsplit("/", 1)[-1]
    return (
        normalized in {"Cargo.lock", "rust-toolchain.toml", "rust-toolchain"}
        or name in {"AGENTS.md", "Cargo.toml", "build.rs"}
        or normalized.startswith(REPAIR_PROTECTED_PREFIXES)
    )


def protected_repair_changes(worktree: Path) -> list[str]:
    return [path for path in changed_paths(worktree) if repair_path_is_protected(path)]


def codex_repair(
    worktree: Path,
    run_dir: Path,
    reason: str,
    *,
    timeout_sec: int,
    memory_limit_mb: int,
    nbcore: int,
    cargo_target: Path,
) -> CommandRecord:
    if not isinstance(nbcore, int) or isinstance(nbcore, bool) or nbcore < 1:
        raise CampaignError("continuous Codex repair requires a positive NBCORE")
    codex = shutil.which("codex")
    if codex is None:
        raise CampaignError("repair requested but codex is not on PATH")
    output = run_dir / "repair" / "last-message.md"
    repair_target = cargo_target
    repair_target.mkdir(mode=0o700, parents=True, exist_ok=True)
    prompt = f"""\
You are repairing a candidate integration in the AY solver repository.

Failure evidence: {reason}
Logs and scorecards are under: {run_dir}

Read AGENTS.md and the failing logs. Fix only the build, correctness, proof,
or benchmark defect demonstrated by that evidence. Solver soundness is the
hard constraint: unknown is preferable to an unsupported definitive answer.
Do not change benchmark expected labels, scoring formulas, resource limits,
or corpus inputs to make a failure disappear. Add focused regression tests.
Do not fetch, merge, commit, push, publish, or run a full-corpus sweep. Run the
smallest relevant checks, then leave the verified edits in this worktree for
the supervising campaign to gate and commit.
"""
    argv = [
        codex,
        "exec",
        "--ephemeral",
        "--color",
        "never",
        "--sandbox",
        "workspace-write",
        "--cd",
        str(worktree),
        "--add-dir",
        str(run_dir),
        "--add-dir",
        str(repair_target),
        "--output-last-message",
        str(output),
        prompt,
    ]
    guarded = watchdog_command(
        file_size_limited_command(argv),
        memory_limit_mb=memory_limit_mb,
        timeout_sec=float(timeout_sec),
        label="continuous Codex repair",
    )
    return run_command(
        guarded,
        worktree,
        run_dir / "repair" / "codex.log",
        env={
            "CARGO_TARGET_DIR": str(repair_target),
            CARGO_BUILD_JOBS_ENV: str(nbcore),
            "MEMLIMIT": str(memory_limit_mb),
            "NBCORE": str(nbcore),
            "AY_CONTINUOUS_MEMLIMIT_MB": str(memory_limit_mb),
        },
        timeout=timeout_sec + 60,
    )


def commit_repairs(worktree: Path, run_name: str) -> str | None:
    if not git(worktree, "status", "--porcelain"):
        return None
    git(worktree, "add", "--all")
    git(
        worktree,
        "commit",
        "-m",
        f"fix(continuous): repair failed integration {run_name}",
    )
    return git(worktree, "rev-parse", "HEAD")


def remote_slug(repo: Path, remote: str) -> str | None:
    url = git(repo, "remote", "get-url", remote)
    if url.startswith("https://github.com/"):
        slug = url.removeprefix("https://github.com/").removesuffix(".git")
    elif url.startswith("git@github.com:"):
        slug = url.removeprefix("git@github.com:").removesuffix(".git")
    else:
        return None
    return slug if slug.count("/") == 1 else None


def gh_json(
    argv: list[str],
    cwd: Path,
    *,
    input_value: dict[str, Any] | None = None,
) -> Any:
    completed = subprocess.run(
        argv,
        cwd=cwd,
        input=json.dumps(input_value) if input_value is not None else None,
        stdin=None if input_value is not None else subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise CampaignError(
            f"{command_text(argv)} failed: "
            f"{completed.stderr.strip() or completed.stdout.strip()}"
        )
    return json.loads(completed.stdout)


def publish_issue(
    repo: Path,
    remote: str,
    markdown: str,
    state: dict[str, Any],
) -> int:
    gh = shutil.which("gh")
    slug = remote_slug(repo, remote)
    if gh is None or slug is None:
        raise CampaignError("GitHub publication requires gh and a github.com remote")
    issue_number = state.get("issue_number")
    if issue_number is None:
        issues = gh_json(
            [
                gh,
                "api",
                "-H",
                "Accept: application/vnd.github+json",
                f"repos/{slug}/issues?state=open&per_page=100",
            ],
            repo,
        )
        match = next(
            (
                issue
                for issue in issues
                if "pull_request" not in issue and issue.get("title") == ISSUE_TITLE
            ),
            None,
        )
        if match is None:
            match = gh_json(
                [
                    gh,
                    "api",
                    "--method",
                    "POST",
                    "-H",
                    "Accept: application/vnd.github+json",
                    f"repos/{slug}/issues",
                    "--input",
                    "-",
                ],
                repo,
                input_value={"title": ISSUE_TITLE, "body": markdown},
            )
        issue_number = int(match["number"])
    gh_json(
        [
            gh,
            "api",
            "--method",
            "PATCH",
            "-H",
            "Accept: application/vnd.github+json",
            f"repos/{slug}/issues/{issue_number}",
            "--input",
            "-",
        ],
        repo,
        input_value={"body": markdown},
    )
    return int(issue_number)

def git_with_text_input(repo: Path, argv: list[str], value: str) -> str:
    completed = subprocess.run(
        ["git", *argv],
        cwd=repo,
        input=value,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise CampaignError(
            f"{command_text(['git', *argv])} failed with "
            f"{completed.returncode}: {detail}"
        )
    return completed.stdout.strip()


def full_git_sha(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 40
        and all(character in "0123456789abcdef" for character in value)
    )


def publish_status_ref(
    repo: Path,
    remote: str,
    run_dir: Path,
    run_name: str,
) -> str:
    """Publish the current compact packet without changing the checkout."""

    packet_blob = git(repo, "hash-object", "-w", str(run_dir / "packet.json"))
    markdown_blob = git(repo, "hash-object", "-w", str(run_dir / "status.md"))
    if not full_git_sha(packet_blob) or not full_git_sha(markdown_blob):
        raise CampaignError("Git status publication produced a malformed blob ID")
    tree = git_with_text_input(
        repo,
        ["mktree"],
        (
            f"100644 blob {packet_blob}\tlatest.json\n"
            f"100644 blob {markdown_blob}\tlatest.md\n"
        ),
    )
    if not full_git_sha(tree):
        raise CampaignError("Git status publication produced a malformed tree ID")

    live = capture(
        ["git", "ls-remote", remote, STATUS_REF],
        repo,
    )
    parent = live.split()[0] if live else ""
    if parent and not full_git_sha(parent):
        raise CampaignError("remote status ref has a malformed commit ID")
    if parent and git_code(repo, "cat-file", "-e", f"{parent}^{{commit}}") != 0:
        fetch = run_command(
            [
                "git",
                "fetch",
                "--no-tags",
                remote,
                STATUS_REF,
            ],
            repo,
            run_dir / "git" / "status-fetch.log",
            timeout=120,
        )
        if fetch.exit_code != 0:
            raise CampaignError("cannot fetch the current status ref parent")

    commit_args = ["commit-tree", tree, "-m", f"continuous status {run_name}"]
    if parent:
        commit_args.extend(["-p", parent])
    commit = git(repo, *commit_args)
    if not full_git_sha(commit):
        raise CampaignError("Git status publication produced a malformed commit ID")
    push = run_command(
        [
            "git",
            "push",
            remote,
            f"{commit}:{STATUS_REF}",
        ],
        repo,
        run_dir / "git" / "status-push.log",
        timeout=120,
    )
    if push.exit_code != 0:
        raise CampaignError("status ref changed concurrently or could not be published")
    return commit


def catalog_rows(path: Path) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    if not path.exists():
        return {}, []
    value = load_toml(path)
    rows: list[dict[str, Any]] = []
    for key in ("track", "event", "competition"):
        candidate = value.get(key)
        if isinstance(candidate, list):
            rows = [row for row in candidate if isinstance(row, dict)]
            break
    return value, rows


def counter(rows: list[dict[str, Any]], key: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in rows:
        value = str(row.get(key, "unknown"))
        counts[value] = counts.get(value, 0) + 1
    return dict(sorted(counts.items()))


def declared_packet_rows(path: Path, key: str) -> list[dict[str, Any]] | None:
    value = read_json(path, None)
    if not isinstance(value, dict):
        return None
    rows = value.get(key)
    if (
        not isinstance(rows, list)
        or not all(
            isinstance(row, dict)
            and isinstance(row.get("disposition"), str)
            and bool(row["disposition"])
            for row in rows
        )
    ):
        return None
    return rows


def normalized_packet_declarations(catalog_path: Path) -> dict[str, Any]:
    """Summarize checked-in packet declarations without treating them as wins."""

    official_path = catalog_path.with_name(OFFICIAL_FIELD_PACKET)
    ay_path = catalog_path.with_name(AY_SCOREBOARD_PACKET)
    official_rows = declared_packet_rows(official_path, "leaderboards")
    ay_rows = declared_packet_rows(ay_path, "rows")
    summary: dict[str, Any] = {
        "source": "checked-in packet declarations",
        "official_field": {
            "present": official_rows is not None,
            "path": official_path.name,
        },
        "ay_scoreboard": {
            "present": ay_rows is not None,
            "path": ay_path.name,
        },
    }
    if official_rows is not None:
        competitors = [row.get("competitors") for row in official_rows]
        if all(
            isinstance(entries, list)
            and all(isinstance(entry, dict) for entry in entries)
            for entries in competitors
        ):
            summary["official_field"].update(
                {
                    "dispositions": counter(official_rows, "disposition"),
                    "competitor_count": sum(
                        len(entries) for entries in competitors
                    ),
                }
            )
        else:
            summary["official_field"]["present"] = False
    if ay_rows is not None:
        scored_rows = [
            row for row in ay_rows if row.get("disposition") == "scored"
        ]
        summary["ay_scoreboard"].update(
            {
                "dispositions": counter(ay_rows, "disposition"),
                "scored_rows": len(scored_rows),
                "declared_win_rows": sum(
                    row.get("win") is True for row in scored_rows
                ),
            }
        )
    return summary


def campaign_check_gate_passed(
    commands: Any,
    records: list[CommandRecord] | None,
) -> bool | None:
    """Return the gate result only when command/record ordering proves it."""

    if not isinstance(commands, list) or not isinstance(records, list):
        return None
    matches = [
        index for index, command in enumerate(commands)
        if command == CAMPAIGN_CHECK_COMMAND
    ]
    if len(matches) != 1 or len(records) > len(commands):
        return None
    index = matches[0]
    if index >= len(records) or not all(
        isinstance(record, CommandRecord) for record in records[: index + 1]
    ):
        return None
    return records[index].exit_code == 0


def competition_summary(
    path: Path,
    *,
    build_commands: Any = None,
    gate_records: list[CommandRecord] | None = None,
) -> dict[str, Any]:
    value, rows = catalog_rows(path)
    if not value:
        return {"catalog_present": False, "total": 0, "statuses": {}}
    statuses: dict[str, int] = {}
    for row in rows:
        status = str(row.get("status", row.get("readiness", "unknown")))
        statuses[status] = statuses.get(status, 0) + 1
    packet_declarations = normalized_packet_declarations(path)
    gate_passed = campaign_check_gate_passed(build_commands, gate_records)
    if gate_passed is not None:
        packet_declarations["campaign_check_passed"] = gate_passed
    if gate_passed is True:
        ay_declarations = packet_declarations.get("ay_scoreboard", {})
        if ay_declarations.get("present"):
            # The ordered Rust campaign gate hashes and parses these exact
            # packets, then recomputes every scored row's rank and win claim.
            ay_declarations["recomputed_retroactive_wins"] = (
                ay_declarations["declared_win_rows"]
            )
    return {
        "catalog_present": True,
        "total": len(rows),
        "statuses": dict(sorted(statuses.items())),
        "readiness": counter(rows, "readiness"),
        "solver_capabilities": counter(rows, "ay_adapter_status"),
        "competitions": counter(rows, "competition"),
        "retrieved_at": value.get("retrieved_at"),
        "scope": value.get("scope", "unknown"),
        "campaign_packet_status": value.get("campaign_packet_status", "unknown"),
        "normalized_packet_declarations": packet_declarations,
    }


def validate_lane_manifest(manifest: dict[str, Any], catalog_path: Path) -> None:
    _, official_rows = catalog_rows(catalog_path)
    official_ids = {str(row.get("id")) for row in official_rows}
    excluded = manifest.get("git", {}).get("exclude", [])
    if not isinstance(excluded, list) or not all(
        isinstance(pattern, str) for pattern in excluded
    ):
        raise CampaignError("git.exclude must be a list of branch glob strings")
    seen: set[str] = set()
    allowed_kinds = {"canary", "rolling", "official"}
    for lane in manifest.get("lane", []):
        lane_id = lane.get("id")
        if not isinstance(lane_id, str) or not lane_id:
            raise CampaignError("every lane requires a non-empty string id")
        if lane_id in seen:
            raise CampaignError(f"duplicate lane id {lane_id}")
        seen.add(lane_id)
        if lane.get("kind") not in allowed_kinds:
            raise CampaignError(
                f"lane {lane_id}: kind must be one of {sorted(allowed_kinds)}"
            )
        kind_is_official = lane.get("kind") == "official"
        flag_is_official = lane.get("official") is True
        if kind_is_official != flag_is_official:
            raise CampaignError(
                f"lane {lane_id}: kind='official' and official=true must agree"
            )
        fixed_official_chc = is_fixed_official_chc_lane(lane)
        if (
            kind_is_official
            and lane.get("enabled", True)
            and not fixed_official_chc
        ):
            raise CampaignError(
                f"lane {lane_id}: only the exact enabled fixed CHC competition-mode "
                "shard-0 lane is admitted; other official replay lanes must remain "
                "disabled"
            )
        eval_id = lane.get("eval_id")
        if (
            not isinstance(eval_id, str)
            or not eval_id
            or not all(
                character.isalnum() or character in {".", "-", "_"}
                for character in eval_id
            )
        ):
            raise CampaignError(f"lane {lane_id}: eval_id is required")
        minimum = lane.get("min_benchmarks", 1)
        if (
            not isinstance(minimum, int)
            or isinstance(minimum, bool)
            or minimum < 1
        ):
            raise CampaignError(
                f"lane {lane_id}: min_benchmarks must be a positive integer"
            )
        shard_size = lane.get("shard_size")
        shard_index = lane.get("shard_index")
        if lane.get("kind") == "rolling":
            if (
                not isinstance(shard_size, int)
                or isinstance(shard_size, bool)
                or not 1 <= shard_size <= 4096
            ):
                raise CampaignError(
                    f"lane {lane_id}: rolling lanes require shard_size in 1..=4096"
                )
            if shard_index is not None:
                raise CampaignError(
                    f"lane {lane_id}: rolling shard indices come from persisted "
                    "scheduler state, not shard_index"
                )
        elif fixed_official_chc:
            pass
        elif shard_size is not None or shard_index is not None:
            raise CampaignError(
                f"lane {lane_id}: fixed shard controls are supported only for the "
                "exact bounded official CHC lane"
            )
        command_timeout = lane.get("command_timeout_sec", 2 * 60 * 60)
        max_command_timeout = (
            FIXED_OFFICIAL_CHC_COMMAND_TIMEOUT_SEC
            if fixed_official_chc
            else 2 * 60 * 60
        )
        if (
            not isinstance(command_timeout, (int, float))
            or isinstance(command_timeout, bool)
            or not math.isfinite(float(command_timeout))
            or not 60 <= float(command_timeout) <= max_command_timeout
        ):
            raise CampaignError(
                f"lane {lane_id}: command_timeout_sec must be between 60 and "
                f"{max_command_timeout}"
            )
        unknown = [
            value
            for value in lane.get("competition_refs", [])
            if value not in official_ids
        ]
        if unknown:
            raise CampaignError(
                f"lane {lane_id}: unknown competition_refs {unknown}"
            )
    if not manifest.get("build", {}).get("commands"):
        raise CampaignError("lane manifest requires build.commands")
    if not any(lane.get("kind") == "canary" for lane in manifest.get("lane", [])):
        raise CampaignError("lane manifest requires at least one canary")
    max_runs = manifest.get("retention", {}).get("max_runs", 720)
    if not isinstance(max_runs, int) or isinstance(max_runs, bool) or max_runs < 1:
        raise CampaignError("retention.max_runs must be a positive integer")


def score_brief(scorecard: dict[str, Any] | None) -> str:
    if not scorecard:
        return "-"
    results = scorecard.get("results")
    if not isinstance(results, list) or not results:
        return "scorecard"
    score = results[0].get("score") if isinstance(results[0], dict) else None
    if not isinstance(score, dict):
        return "scorecard"
    keys = [
        "solved",
        "total",
        "wrong",
        "par2_avg",
        "correct",
        "errors",
        "wall_time_sec",
        "cpu_time_sec",
    ]
    parts = [f"{key}={score[key]}" for key in keys if key in score]
    return ", ".join(parts) if parts else "score recorded"


def primary_score(scorecard: dict[str, Any] | None) -> dict[str, Any] | None:
    if not isinstance(scorecard, dict):
        return None
    results = scorecard.get("results")
    if not isinstance(results, list) or not results or not isinstance(results[0], dict):
        return None
    score = results[0].get("score")
    return dict(score) if isinstance(score, dict) else None


def update_scoreboard(
    existing: Any,
    outcomes: list[LaneOutcome],
    *,
    current_run: str,
    tested_sha: str,
    promote_scores: bool,
) -> dict[str, dict[str, Any]]:
    """Retain the latest status and latest score for every rotating lane."""

    scoreboard = dict(existing) if isinstance(existing, dict) else {}
    for outcome in outcomes:
        previous = scoreboard.get(outcome.lane_id)
        entry = dict(previous) if isinstance(previous, dict) else {}
        entry.update(
            {
                "eval_id": outcome.eval_id,
                "last_run_id": current_run,
                "last_tested_sha": tested_sha,
                "last_status": outcome.status,
                "last_detail": outcome.detail,
            }
        )
        if outcome.shard is not None:
            entry["last_shard"] = dict(outcome.shard)
        else:
            entry.pop("last_shard", None)
        score = primary_score(outcome.scorecard)
        if promote_scores and outcome.status == "passed" and score is not None:
            solved = score.get("solved")
            total = score.get("total")
            if (
                isinstance(solved, (int, float))
                and not isinstance(solved, bool)
                and isinstance(total, (int, float))
                and not isinstance(total, bool)
                and total > 0
            ):
                score["solved_rate"] = round(float(solved) / float(total), 6)
            entry.update(
                {
                    "score": score,
                    "score_run_id": current_run,
                    "score_tested_sha": tested_sha,
                    "scorecard_path": outcome.scorecard_path,
                    "evidence_path": outcome.evidence_path,
                    "evidence": outcome.evidence,
                }
            )
        scoreboard[outcome.lane_id] = entry
    return dict(sorted(scoreboard.items()))


def update_lane_shards(
    existing: Any,
    outcomes: list[LaneOutcome],
    *,
    current_run: str,
    tested_sha: str,
    promote: bool,
) -> dict[str, dict[str, Any]]:
    """Advance bounded coverage cursors without aggregating mixed snapshots."""

    progress = dict(existing) if isinstance(existing, dict) else {}
    if not promote:
        return dict(sorted(progress.items()))
    for outcome in outcomes:
        shard = outcome.shard
        if outcome.status != "passed" or not isinstance(shard, dict):
            continue
        lane_id = outcome.lane_id
        previous = progress.get(lane_id)
        entry = dict(previous) if isinstance(previous, dict) else {}
        identity = {
            "corpus_path_inventory_sha256": shard[
                "corpus_path_inventory_sha256"
            ],
            "corpus_benchmark_count": shard["corpus_benchmark_count"],
            "shard_size": shard["shard_size"],
            "shard_count": shard["shard_count"],
            "selector": shard["selector"],
        }
        same_sweep = all(entry.get(key) == value for key, value in identity.items())
        completed = (
            {
                value
                for value in entry.get("completed_indices", [])
                if isinstance(value, int)
                and not isinstance(value, bool)
                and 0 <= value < shard["shard_count"]
            }
            if same_sweep
            else set()
        )
        candidate_shas = (
            {
                value
                for value in entry.get("candidate_shas", [])
                if isinstance(value, str) and value
            }
            if same_sweep
            else set()
        )
        if not same_sweep:
            entry["completed_sweeps"] = 0
        completed.add(shard["shard_index"])
        candidate_shas.add(tested_sha)
        entry.update(identity)
        entry.update(
            {
                "next_index": (shard["shard_index"] + 1)
                % shard["shard_count"],
                "completed_indices": sorted(completed),
                "candidate_shas": sorted(candidate_shas),
                "coverage_benchmarks_upper_bound": min(
                    len(completed) * shard["shard_size"],
                    shard["corpus_benchmark_count"],
                ),
                "coverage_fraction": round(
                    len(completed) / shard["shard_count"], 6
                ),
                "last_run_id": current_run,
                "last_tested_sha": tested_sha,
                "score_aggregation": (
                    "forbidden-across-shards-unless-one-frozen-campaign-"
                    "and-a-validated-aggregator"
                ),
            }
        )
        if len(completed) == shard["shard_count"]:
            completed_sweeps = entry.get("completed_sweeps", 0)
            if (
                not isinstance(completed_sweeps, int)
                or isinstance(completed_sweeps, bool)
                or completed_sweeps < 0
            ):
                completed_sweeps = 0
            entry["completed_sweeps"] = completed_sweeps + 1
            entry["last_completed_sweep"] = {
                **identity,
                "completed_run_id": current_run,
                "candidate_shas": sorted(candidate_shas),
                "single_candidate_sha": len(candidate_shas) == 1,
            }
            entry["completed_indices"] = []
            entry["candidate_shas"] = []
            entry["coverage_benchmarks_upper_bound"] = 0
            entry["coverage_fraction"] = 0.0
        progress[lane_id] = entry
    return dict(sorted(progress.items()))


def score_dict_brief(score: Any) -> str:
    if not isinstance(score, dict):
        return "-"
    keys = [
        "solved",
        "total",
        "solved_rate",
        "wrong",
        "par2_avg",
        "correct",
        "errors",
        "wall_time_sec",
        "cpu_time_sec",
    ]
    parts = [f"{key}={score[key]}" for key in keys if key in score]
    return ", ".join(parts) if parts else "score recorded"


def markdown_cell(value: Any) -> str:
    """Escape data before placing it in a GitHub Markdown cell or code span."""

    return (
        str(value)
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace("|", "&#124;")
        .replace("`", "&#96;")
        .replace("\r", "")
        .replace("\n", "<br>")
    )


def render_markdown(packet: dict[str, Any]) -> str:
    integration = packet.get("integration_admission", {})
    quarantined = integration.get("quarantined", [])
    integration_label = (
        "pending"
        if "complete" not in integration
        else ("complete" if integration.get("complete") else "safe subset")
    )
    lines = [
        f"# {ISSUE_TITLE}",
        "",
        "<!-- ay-continuous-benchmark -->",
        "",
        f"Latest cycle: `{packet['run_id']}` — **{packet['status']}**",
        "",
        f"- Base: `{packet.get('base_sha', 'unknown')}`",
        f"- Tested: `{packet.get('tested_sha', 'unknown')}`",
        f"- Push: {packet.get('push', {}).get('status', 'not-requested')}",
        f"- Score class: `{packet.get('score_claim_class', 'development-proxy')}`",
        f"- Integration: {integration_label} "
        f"({len(quarantined) if isinstance(quarantined, list) else 0} quarantined)",
        f"- Started: {packet.get('started_at', 'unknown')}",
        f"- Finished: {packet.get('finished_at', 'unknown')}",
    ]
    if packet.get("error"):
        lines.extend(["", f"Failure: `{markdown_cell(packet['error'])}`"])
    lines.extend(
        [
            "",
            "## Branch integration",
            "",
            "| Branch | SHA | Classification | Detail |",
            "| --- | --- | --- | --- |",
        ]
    )
    for row in packet.get("branches", []):
        lines.append(
            f"| `{markdown_cell(row['name'])}` | "
            f"`{markdown_cell(row['sha'][:12])}` | "
            f"{markdown_cell(row['classification'])} | "
            f"{markdown_cell(row.get('detail', ''))} |"
        )
    lines.extend(
        [
            "",
            "## Benchmark lanes",
            "",
            "| Lane | Eval | Status | Score |",
            "| --- | --- | --- | --- |",
        ]
    )
    for row in packet.get("benchmarks", []):
        lines.append(
            f"| `{markdown_cell(row['lane_id'])}` | "
            f"`{markdown_cell(row['eval_id'])}` | "
            f"{markdown_cell(row['status'])} | "
            f"{markdown_cell(score_brief(row.get('scorecard')))} |"
        )
    lines.extend(
        [
            "",
            "## Persistent lane scoreboard",
            "",
            "| Lane | Last attempt / score run | Status | Latest passing score |",
            "| --- | --- | --- | --- |",
        ]
    )
    for lane_id, row in packet.get("scoreboard", {}).items():
        lines.append(
            f"| `{markdown_cell(lane_id)}` | "
            f"`{markdown_cell(row.get('last_run_id', '-'))}` "
            f"(score `{markdown_cell(row.get('score_run_id', '-'))}`) | "
            f"{markdown_cell(row.get('last_status', '-'))} | "
            f"{markdown_cell(score_dict_brief(row.get('score')))} |"
        )
    coverage = packet.get("competition_catalog", {})
    declarations = coverage.get("normalized_packet_declarations", {})
    official = declarations.get("official_field", {})
    ay = declarations.get("ay_scoreboard", {})
    if official.get("present"):
        official_declarations = (
            "official dispositions "
            f"`{json.dumps(official.get('dispositions', {}), sort_keys=True)}`, "
            f"official competitors {official['competitor_count']}"
        )
    else:
        official_declarations = "official field packet unavailable"
    if ay.get("present"):
        ay_declarations = [
            "AY dispositions "
            f"`{json.dumps(ay.get('dispositions', {}), sort_keys=True)}`, "
            f"AY scored rows {ay['scored_rows']}, "
            f"declared win rows {ay['declared_win_rows']}"
        ]
        if "recomputed_retroactive_wins" in ay:
            ay_declarations.append(
                ", recomputed retroactive wins "
                f"{ay['recomputed_retroactive_wins']}"
            )
        ay_declarations = "".join(ay_declarations)
    else:
        ay_declarations = "AY scoreboard packet unavailable"
    lines.extend(
        [
            "",
            "## Official catalog",
            "",
            f"Tracked rows: {coverage.get('total', 0)}. "
            f"Scope: `{markdown_cell(coverage.get('scope', 'unknown'))}`. "
            f"States: `{json.dumps(coverage.get('statuses', {}), sort_keys=True)}`. "
            "Readiness: "
            f"`{json.dumps(coverage.get('readiness', {}), sort_keys=True)}`.",
            "Checked-in packet declarations: "
            f"{official_declarations}; {ay_declarations}.",
            *(
                [
                    "Candidate campaign-check build gate: "
                    + (
                        "passed."
                        if declarations["campaign_check_passed"]
                        else "failed."
                    )
                ]
                if "campaign_check_passed" in declarations
                else []
            ),
            "",
            "Raw logs, scorecards, binary provenance, corpus identity, and enforced "
            "resource envelopes remain in the host-local evidence store; only this "
            "compact status is published.",
            "",
        ]
    )
    return "\n".join(lines)


def checkpoint_progress(
    repo: Path,
    remote: str,
    state_root: Path,
    run_dir: Path,
    state_path: Path,
    packet: dict[str, Any],
    state: dict[str, Any],
    *,
    publish: bool,
    publish_status: bool = False,
    persist_state: bool = True,
) -> bool:
    """Persist progress and refresh each explicitly requested remote channel."""

    # The exact status-ref commit is a host-local publication receipt. It
    # cannot be embedded in the commit that it identifies without creating a
    # self-reference, so never copy a prior checkpoint's receipt into the next
    # remote payload.
    if publish_status:
        # Drop both the current receipt and the legacy branch receipt so neither
        # can become a stale/impossible self-reference in the remote packet.
        packet.pop("status_ref_publication", None)
        packet.pop("status_branch_publication", None)
    markdown = render_markdown(packet)
    atomic_json(run_dir / "packet.json", packet)
    atomic_text(run_dir / "status.md", markdown)
    atomic_json(state_root / "latest.json", packet)
    atomic_text(state_root / "latest.md", markdown)
    published = True
    if publish:
        try:
            issue = publish_issue(repo, remote, markdown, state)
            state["issue_number"] = issue
            packet["publication"] = {
                "status": "published",
                "issue_number": issue,
            }
        except Exception as error:
            published = False
            packet["publication"] = {
                "status": "failed",
                "error": f"{type(error).__name__}: {error}",
            }
    if publish_status:
        try:
            commit = publish_status_ref(
                repo,
                remote,
                run_dir,
                str(packet["run_id"]),
            )
            packet["status_ref_publication"] = {
                "status": "published",
                "ref": STATUS_REF,
                "commit": commit,
            }
        except Exception as error:
            published = False
            packet["status_ref_publication"] = {
                "status": "failed",
                "ref": STATUS_REF,
                "error": f"{type(error).__name__}: {error}",
            }
    if publish or publish_status:
        atomic_json(run_dir / "packet.json", packet)
        atomic_json(state_root / "latest.json", packet)
    if persist_state:
        atomic_json(state_path, state)
    return published


def cleanup_worktree(repo: Path, path: Path) -> None:
    if not path.exists():
        return
    completed = subprocess.run(
        ["git", "worktree", "remove", "--force", str(path)],
        cwd=repo,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if completed.returncode != 0:
        raise CampaignError(
            f"cannot remove disposable worktree {path}: "
            f"{completed.stderr.strip() or completed.stdout.strip()}"
        )


def cleanup_run_target(state_root: Path, target: Path) -> None:
    expected_parent = continuous_target_root(state_root).resolve()
    if target.parent.resolve() != expected_parent:
        raise CampaignError(f"refusing to remove unexpected target path {target}")
    if target.is_symlink():
        raise CampaignError(f"refusing to remove symlinked target path {target}")
    if target.exists():
        shutil.rmtree(target)
    with contextlib.suppress(OSError):
        expected_parent.rmdir()


def continuous_target_root(state_root: Path) -> Path:
    """Place untrusted build output on the host's bounded tmpfs."""

    shared_memory = Path("/dev/shm")
    if not shared_memory.is_dir() or not os.access(shared_memory, os.W_OK):
        raise CampaignError("/dev/shm is required for bounded build output")
    identity = hashlib.sha256(str(state_root.resolve()).encode()).hexdigest()[:16]
    root = shared_memory / f"ay-continuous-targets-{os.getuid()}-{identity}"
    root.mkdir(mode=0o700, parents=True, exist_ok=True)
    if os.name == "posix":
        root.chmod(0o700)
    return root


def cleanup_stale_scratch(repo: Path, state_root: Path) -> dict[str, list[str]]:
    """Remove scratch left by a previously interrupted lock holder."""

    removed_worktrees: list[str] = []
    worktrees_root = state_root / "worktrees"
    if worktrees_root.is_dir() and not worktrees_root.is_symlink():
        for path in sorted(worktrees_root.iterdir()):
            try:
                dt.datetime.strptime(path.name, "%Y%m%dT%H%M%SZ")
            except ValueError:
                continue
            if path.is_symlink() or not path.is_dir():
                raise CampaignError(f"unexpected stale worktree entry {path}")
            try:
                cleanup_worktree(repo, path)
            except CampaignError:
                # `git worktree add` can be killed after creating the
                # directory but before registering it. This is a validated
                # timestamped direct child under the private scratch root.
                shutil.rmtree(path)
            removed_worktrees.append(path.name)
    git(repo, "worktree", "prune")

    removed_targets: list[str] = []
    targets_root = continuous_target_root(state_root)
    for path in sorted(targets_root.iterdir()):
        try:
            dt.datetime.strptime(path.name, "%Y%m%dT%H%M%SZ")
        except ValueError:
            continue
        if path.is_symlink() or not path.is_dir():
            raise CampaignError(f"unexpected stale target entry {path}")
        shutil.rmtree(path)
        removed_targets.append(path.name)
    with contextlib.suppress(OSError):
        targets_root.rmdir()
    return {
        "worktrees": removed_worktrees,
        "targets": removed_targets,
    }


def prune_run_history(
    state_root: Path,
    *,
    max_runs: int,
    current_run: str,
    preserved_run_ids: set[str] | None = None,
) -> list[str]:
    """Bound evidence while retaining official and scoreboard-referenced runs."""

    if max_runs < 1:
        raise CampaignError("retention.max_runs must be at least 1")
    runs_root = state_root / "runs"
    if not runs_root.is_dir():
        return []
    preserved = preserved_run_ids or set()
    removable: list[Path] = []
    retained = 0
    for path in sorted(runs_root.iterdir(), key=lambda entry: entry.name):
        timestamp = path.name.split("-controller-", 1)[0]
        try:
            dt.datetime.strptime(timestamp, "%Y%m%dT%H%M%SZ")
        except ValueError:
            continue
        if not path.is_dir() or path.is_symlink():
            continue
        packet = read_json(path / "packet.json", {})
        if (
            path.name == current_run
            or path.name in preserved
            or bool(packet.get("official_requested"))
        ):
            retained += 1
        else:
            removable.append(path)
    excess = max(0, retained + len(removable) - max_runs)
    removed: list[str] = []
    for path in removable[:excess]:
        if path.parent.resolve() != runs_root.resolve() or path.is_symlink():
            raise CampaignError(f"refusing to prune unexpected run path {path}")
        shutil.rmtree(path)
        removed.append(path.name)
    return removed


def scoreboard_run_ids(scoreboard: Any) -> set[str]:
    if not isinstance(scoreboard, dict):
        return set()
    return {
        value
        for entry in scoreboard.values()
        if isinstance(entry, dict)
        and isinstance((value := entry.get("score_run_id")), str)
    }


def validate_campaign_state(state: dict[str, Any]) -> None:
    scoreboard = state.get("scoreboard", {})
    if not isinstance(scoreboard, dict) or any(
        not isinstance(key, str) or not isinstance(value, dict)
        for key, value in scoreboard.items()
    ):
        raise CampaignError("persistent scoreboard has an invalid shape")
    for key in ("rolling_cursor", "official_cursor"):
        value = state.get(key, 0)
        if (
            not isinstance(value, int)
            or isinstance(value, bool)
            or value < 0
        ):
            raise CampaignError(f"persistent {key} is not a non-negative integer")
    lane_shards = state.get("lane_shards", {})
    if not isinstance(lane_shards, dict) or any(
        not isinstance(key, str) or not isinstance(value, dict)
        for key, value in lane_shards.items()
    ):
        raise CampaignError("persistent lane_shards has an invalid shape")
    for lane_id, value in lane_shards.items():
        next_index = value.get("next_index", 0)
        if (
            not isinstance(next_index, int)
            or isinstance(next_index, bool)
            or next_index < 0
        ):
            raise CampaignError(
                f"persistent shard cursor for {lane_id!r} is invalid"
            )
        completed = value.get("completed_indices", [])
        if not isinstance(completed, list) or any(
            not isinstance(index, int)
            or isinstance(index, bool)
            or index < 0
            for index in completed
        ):
            raise CampaignError(
                f"persistent shard coverage for {lane_id!r} is invalid"
            )
    issue_number = state.get("issue_number")
    if issue_number is not None and (
        not isinstance(issue_number, int)
        or isinstance(issue_number, bool)
        or issue_number < 1
    ):
        raise CampaignError("persistent issue_number is invalid")


def record_control_plane_failure(
    repo: Path,
    state_root: Path,
    remote: str,
    *,
    publish: bool,
    publish_status: bool = False,
    official_requested: bool,
    error: BaseException,
) -> dict[str, Any]:
    """Publish a local/remote failure packet even before manifests are trusted."""

    failure_run = f"{run_id()}-controller-{os.getpid()}"
    run_dir = state_root / "runs" / failure_run
    run_dir.mkdir(mode=0o700, parents=True, exist_ok=False)
    state_path = state_root / "state.json"
    loaded_state = read_json(state_path, None)
    state_valid = isinstance(loaded_state, dict)
    state = dict(loaded_state) if state_valid else {}
    raw_scoreboard = state.get("scoreboard")
    scoreboard = (
        {
            str(key): dict(value)
            for key, value in raw_scoreboard.items()
            if isinstance(key, str) and isinstance(value, dict)
        }
        if isinstance(raw_scoreboard, dict)
        else {}
    )
    state["scoreboard"] = scoreboard
    issue_number = state.get("issue_number")
    if (
        not isinstance(issue_number, int)
        or isinstance(issue_number, bool)
        or issue_number < 1
    ):
        state.pop("issue_number", None)
    now = utc_now().isoformat()
    packet: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "run_id": failure_run,
        "started_at": now,
        "finished_at": now,
        "status": "failed",
        "phase": "controller-bootstrap",
        "repo": str(repo),
        "state_root": str(state_root),
        "branches": [],
        "benchmarks": [],
        "scoreboard": scoreboard,
        "competition_catalog": {"catalog_present": False, "total": 0},
        "push": {"status": "not-attempted"},
        "official_requested": official_requested,
        "score_claim_class": (
            "official-replay-requested"
            if official_requested
            else "development-proxy"
        ),
        "error": f"{type(error).__name__}: {error}",
    }
    markdown = render_markdown(packet)
    atomic_json(run_dir / "packet.json", packet)
    atomic_text(run_dir / "status.md", markdown)
    atomic_json(state_root / "latest.json", packet)
    atomic_text(state_root / "latest.md", markdown)
    if publish and (repo / ".git").exists():
        try:
            issue = publish_issue(repo, remote, markdown, state)
            state["issue_number"] = issue
            packet["publication"] = {
                "status": "published",
                "issue_number": issue,
            }
            if state_valid:
                atomic_json(state_path, state)
        except Exception as publication_error:
            packet["publication"] = {
                "status": "failed",
                "error": (
                    f"{type(publication_error).__name__}: {publication_error}"
                ),
            }
        atomic_json(run_dir / "packet.json", packet)
        atomic_json(state_root / "latest.json", packet)
    if publish_status and (repo / ".git").exists():
        try:
            ensure_git_identity(repo)
            commit = publish_status_ref(
                repo,
                remote,
                run_dir,
                failure_run,
            )
            packet["status_ref_publication"] = {
                "status": "published",
                "ref": STATUS_REF,
                "commit": commit,
            }
        except Exception as publication_error:
            packet["status_ref_publication"] = {
                "status": "failed",
                "ref": STATUS_REF,
                "error": (
                    f"{type(publication_error).__name__}: {publication_error}"
                ),
            }
        atomic_json(run_dir / "packet.json", packet)
        atomic_json(state_root / "latest.json", packet)
    return packet


def cycle(args: argparse.Namespace) -> int:
    publish_status = bool(getattr(args, "publish_status_ref", False))
    if args.repair_with_codex and (
        args.push or args.publish_issue or publish_status
    ):
        raise CampaignError(
            "--repair-with-codex is laboratory-only and cannot be combined "
            "with remote publication"
        )
    repo = Path(args.repo).resolve()
    corpus_root = validate_shared_corpus_root(repo)
    state_root = Path(args.state_root).resolve()
    bootstrap_remote = getattr(args, "bootstrap_remote", "origin")
    bootstrap_branch = getattr(args, "bootstrap_branch", "main")
    prepare_state_root(state_root)
    with (state_root / "campaign.lock").open("a+") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print("continuous benchmark cycle already running; skipping")
            return 0

        previous_signal_handlers = arm_cycle_deadline(
            int(getattr(args, "cycle_timeout_sec", DEFAULT_CYCLE_TIMEOUT_SEC))
        )
        try:
            updated_sha = bootstrap_checkout(
                repo,
                bootstrap_remote,
                bootstrap_branch,
            )
            if updated_sha is not None:
                reexec_updated_controller(repo, updated_sha)
            startup_cleanup = cleanup_stale_scratch(repo, state_root)
            lane_manifest_path = (repo / args.lanes).resolve()
            catalog_path = (repo / args.catalog).resolve()
            git_identity = ensure_git_identity(repo)
            manifest = load_toml(lane_manifest_path)
            validate_lane_manifest(manifest, catalog_path)
            git_config = manifest.get("git", {})
            remote = git_config.get("remote", "origin")
            base_branch = git_config.get("base_branch", "main")
            if remote != bootstrap_remote or base_branch != bootstrap_branch:
                raise CampaignError(
                    "lane manifest git base must match the independently trusted "
                    f"bootstrap root {bootstrap_remote}/{bootstrap_branch}"
                )
            exclude = list(git_config.get("exclude", []))
            state_path = state_root / "state.json"
            state = read_json(state_path, {})
            if not isinstance(state, dict):
                raise CampaignError("persistent state.json is not a JSON object")
            validate_campaign_state(state)
            current_run = run_id()
            run_dir = state_root / "runs" / current_run
            if run_dir.exists():
                raise CampaignError(f"run directory collision: {run_dir}")
            run_dir.mkdir(parents=True)
        except (Exception, CycleInterrupted) as error:
            failure = record_control_plane_failure(
                repo,
                state_root,
                bootstrap_remote,
                publish=bool(args.publish_issue),
                publish_status=publish_status,
                official_requested=bool(args.official),
                error=error,
            )
            disarm_cycle_deadline(previous_signal_handlers)
            print(render_markdown(failure))
            return 1
        packet: dict[str, Any] = {
            "schema_version": SCHEMA_VERSION,
            "run_id": current_run,
            "started_at": utc_now().isoformat(),
            "status": "running",
            "repo": str(repo),
            "state_root": str(state_root),
            "branches": [],
            "gates": [],
            "benchmarks": [],
            "push": {"status": "not-requested"},
            "repair": None,
            "startup_cleanup": startup_cleanup,
            "competition_catalog": competition_summary(catalog_path),
            "scoreboard": state.get("scoreboard", {}),
            "git_identity": git_identity,
            "official_requested": bool(args.official),
            "cycle_timeout_sec": int(
                getattr(args, "cycle_timeout_sec", DEFAULT_CYCLE_TIMEOUT_SEC)
            ),
            "build_file_size_limit_bytes": MAX_CHILD_FILE_BYTES,
            "score_claim_class": (
                "official-replay-requested"
                if args.official
                else "development-proxy"
            ),
            "shared_corpus": {
                "root": str(corpus_root),
                "environment": BENCH_CORPUS_ROOT_ENV,
                "payload_scope": "normalized-repo-relative-benchmarks-only",
                "registry_and_controls": "candidate-worktree",
                "candidate_solver_visibility": "private-input-snapshots-only",
            },
        }
        worktree = state_root / "worktrees" / current_run
        target = continuous_target_root(state_root) / current_run
        target_filesystem = os.statvfs(target.parent)
        packet["build_target_envelope"] = {
            "kind": "tmpfs",
            "path": str(target.parent),
            "capacity_bytes": target_filesystem.f_blocks
            * target_filesystem.f_frsize,
            "available_bytes_at_start": target_filesystem.f_bavail
            * target_filesystem.f_frsize,
        }
        results_root = run_dir / "native-results"
        store_root = run_dir / "native-store"
        build_writable_paths = [target]
        env = {
            "CARGO_TARGET_DIR": str(target),
            "AY_BENCH_RESULTS_ROOT": str(results_root),
            "AY_BENCH_STORE_PATH": str(store_root / "results.sqlite"),
            BENCH_CORPUS_ROOT_ENV: str(corpus_root),
        }
        for key in (
            "CC",
            "CXX",
            "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER",
        ):
            value = os.environ.get(key)
            if value:
                env[key] = value
        z3 = shutil.which("z3")
        z3_lib = Path.home() / ".local" / "bin" / "libz3.so"
        if z3 is not None:
            env["Z3_BIN"] = str(Path(z3).resolve())
        if z3_lib.is_file():
            env["Z3_LIB"] = str(z3_lib)

        selected: list[dict[str, Any]] = []
        scoreboard_outcomes: list[LaneOutcome] = []
        next_cursor = int(state.get("rolling_cursor", 0))
        next_official_cursor = int(state.get("official_cursor", 0))
        tested_sha = str(packet.get("tested_sha", "unknown"))
        admission_clean = False
        try:
            heads = remote_heads(repo, remote)
            if base_branch not in heads:
                raise CampaignError(f"remote branch {remote}/{base_branch} not found")
            base_sha = heads[base_branch]
            local_sha = git(repo, "rev-parse", "HEAD")
            if base_sha != local_sha:
                updated_sha = bootstrap_checkout(repo, remote, base_branch)
                if updated_sha is not None:
                    reexec_updated_controller(repo, updated_sha)
                raise CampaignError(
                    "remote base changed after controller bootstrap; refusing "
                    "to evaluate it with an older loaded policy"
                )
            packet["fetch"] = {
                "status": "completed-before-policy-load",
                "remote": remote,
                "base_branch": base_branch,
                "base_sha": base_sha,
                "bootstrap_attempts": int(
                    os.environ.get("AY_CONTINUOUS_BOOTSTRAP_ATTEMPTS", "0")
                ),
            }
            packet["base_sha"] = base_sha
            packet["remote_snapshot"] = heads
            branches = classify_branches(
                repo, remote, base_branch, heads, exclude
            )
            packet["branches"] = [row.as_json() for row in branches]

            worktree.parent.mkdir(parents=True, exist_ok=True)
            add = run_command(
                ["git", "worktree", "add", "--detach", str(worktree), base_sha],
                repo,
                run_dir / "git" / "worktree-add.log",
            )
            if add.exit_code != 0:
                raise CampaignError("cannot create disposable integration worktree")

            packet["tested_sha"] = base_sha
            packet["progress"] = "trusted-supervisor-build"
            initial_published = checkpoint_progress(
                repo,
                remote,
                state_root,
                run_dir,
                state_path,
                packet,
                state,
                publish=args.publish_issue,
                publish_status=publish_status,
            )
            if (args.publish_issue or publish_status) and not initial_published:
                raise CampaignError(
                    "requested progress publication preflight failed; refusing "
                    "a cycle that could push without its dashboard"
                )

            dependency_fetch = fetch_trusted_dependencies(
                worktree,
                run_dir,
                timeout_sec=min(
                    900.0,
                    float(manifest.get("build", {}).get("timeout_sec", 3600)),
                ),
            )
            packet["trusted_dependency_fetch"] = dependency_fetch.as_json()
            if dependency_fetch.exit_code != 0:
                raise CampaignError(
                    "cannot populate the trusted base dependency cache"
                )

            with planned_build_resources(f"continuous build {current_run}") as plan:
                packet["build_resource_plan"] = resource_plan_json(plan)
                packet["build_resource_enforcement"] = (
                    "scripts/_oom_guard.py run: whole-process-group RSS watchdog "
                    "with zero grace; CARGO_BUILD_JOBS/direct -j match "
                    "the admitted NBCORE; service cgroup MemoryMax when "
                    "systemd-launched"
                )
                build_env = parent_lease_build_environment(env, plan)
                env.update(
                    {
                        "MEMLIMIT": str(plan.memlimit_mb),
                        "NBCORE": str(plan.nbcore),
                    }
                )
                supervisor_record, supervisor_ay, supervisor_sha256 = (
                    build_trusted_supervisor(
                        repo,
                        worktree,
                        run_dir,
                        build_env,
                        target,
                        build_writable_paths,
                        timeout_sec=float(
                            manifest.get("build", {}).get("timeout_sec", 3600)
                        ),
                    )
                )
                packet["trusted_supervisor"] = {
                    "source_sha": base_sha,
                    "path": str(supervisor_ay),
                    "sha256": supervisor_sha256,
                    "build": supervisor_record.as_json(),
                }

                for branch in sort_unique_branches(repo, base_sha, branches):
                    before = git(worktree, "rev-parse", "HEAD")
                    merge = run_command(
                        ["git", "merge", "--no-ff", "--no-edit", branch.sha],
                        worktree,
                        run_dir
                        / "git"
                        / f"merge-{branch.name.replace('/', '_')}.log",
                    )
                    if merge.exit_code != 0:
                        git_code(worktree, "merge", "--abort")
                        git(worktree, "reset", "--hard", before)
                        branch.classification = "conflicted"
                        branch.detail = f"merge failed; see {merge.log}"
                packet["branches"] = [row.as_json() for row in branches]
                packet["tested_sha"] = git(worktree, "rev-parse", "HEAD")
                packet["progress"] = "build-gates"
                checkpoint_progress(
                    repo,
                    remote,
                    state_root,
                    run_dir,
                    state_path,
                    packet,
                    state,
                    publish=args.publish_issue,
                    publish_status=publish_status,
                )
                gates = execute_build_gates(
                    manifest,
                    repo,
                    worktree,
                    run_dir,
                    build_env,
                    target,
                    build_writable_paths,
                )
            packet["gates"] = [record.as_json() for record in gates]
            packet["competition_catalog"] = competition_summary(
                (worktree / args.catalog).resolve(),
                build_commands=manifest.get("build", {}).get("commands"),
                gate_records=gates,
            )
            gates_clean = bool(gates) and all(
                record.exit_code == 0 for record in gates
            )
            packet["progress"] = "selected-benchmarks"
            checkpoint_progress(
                repo,
                remote,
                state_root,
                run_dir,
                state_path,
                packet,
                state,
                publish=args.publish_issue,
                publish_status=publish_status,
            )

            selected, blocked, next_cursor, next_official_cursor = select_lanes(
                manifest,
                state,
                worktree,
                smoke_only=args.smoke_only,
                include_official=args.official,
                corpus_root=corpus_root,
            )
            outcomes: list[LaneOutcome] = blocked
            scoreboard_outcomes = outcomes
            if gates_clean and selected:
                solver_ay = target / "release" / "ay"
                if not os.access(solver_ay, os.X_OK):
                    raise CampaignError(
                        f"release binary not executable: {solver_ay}"
                    )
                candidate = prepare_candidate_solver(
                    solver_ay,
                    run_dir,
                    results_root,
                    tested_sha=str(packet["tested_sha"]),
                    label="initial",
                )
                packet["candidate"] = candidate
                outcomes.extend(
                    execute_lanes(
                        selected,
                        repo,
                        worktree,
                        run_dir,
                        env,
                        supervisor_ay,
                        supervisor_sha256,
                        candidate,
                    )
                )
                scoreboard_outcomes = outcomes
            packet["benchmarks"] = [row.as_json() for row in outcomes]
            integration_clean = integrations_clean(branches)
            packet["integration_admission"] = {
                "complete": integration_clean,
                "quarantined": [
                    row.as_json()
                    for row in branches
                    if row.classification in {"conflicted", "policy-review"}
                ],
                "safe_subset_publishable": True,
            }
            official_clean = official_selection_clean(
                args.official,
                selected,
                outcomes,
            )
            packet["official_admission"] = {
                "requested": bool(args.official),
                "selected": [
                    str(lane["id"])
                    for lane in selected
                    if lane.get("kind") == "official"
                ],
                "passed": official_clean,
            }
            clean = (
                gates_clean
                and outcomes_clean(outcomes)
                and canaries_clean(selected, outcomes)
                and official_clean
            )

            if not clean and args.repair_with_codex and integration_clean:
                reason = (
                    "one or more build gates or selected benchmark lanes failed; "
                    f"inspect {run_dir}"
                )
                with planned_build_resources(
                    f"continuous repair {current_run}"
                ) as repair_plan:
                    packet["repair_resource_plan"] = resource_plan_json(repair_plan)
                    repair = codex_repair(
                        worktree,
                        run_dir,
                        reason,
                        timeout_sec=args.repair_timeout,
                        memory_limit_mb=int(repair_plan.memlimit_mb),
                        nbcore=int(repair_plan.nbcore),
                        cargo_target=target / "codex-repair",
                    )
                packet["repair"] = repair.as_json()
                if repair.exit_code == 0:
                    protected_changes = protected_repair_changes(worktree)
                    packet["repair_protected_changes"] = protected_changes
                    if protected_changes:
                        packet["repair_rejected"] = (
                            "repair changed protected admission, corpus, proof-checker, "
                            "or resource-enforcement files"
                        )
                        clean = False
                        continue_repair = False
                    else:
                        continue_repair = True
                else:
                    continue_repair = False
                if continue_repair:
                    packet["repair_commit"] = commit_repairs(
                        worktree,
                        current_run,
                    )
                    if repair_residue(worktree):
                        packet["repair_rejected"] = (
                            "repair left tracked, untracked, or ignored state "
                            "outside its committed source snapshot"
                        )
                        continue_repair = False
                if continue_repair:
                    with planned_build_resources(
                        f"continuous repair gates {current_run}"
                    ) as repair_gate_plan:
                        packet["repair_gate_resource_plan"] = resource_plan_json(
                            repair_gate_plan
                        )
                        repair_gate_env = parent_lease_build_environment(
                            env,
                            repair_gate_plan,
                        )
                        repair_gates = execute_build_gates(
                            manifest,
                            repo,
                            worktree,
                            run_dir / "repair-rerun",
                            repair_gate_env,
                            target,
                            build_writable_paths,
                        )
                    packet["repair_gates"] = [
                        record.as_json() for record in repair_gates
                    ]
                    packet["competition_catalog"] = competition_summary(
                        (worktree / args.catalog).resolve(),
                        build_commands=manifest.get("build", {}).get("commands"),
                        gate_records=repair_gates,
                    )
                    gates_clean = bool(repair_gates) and all(
                        record.exit_code == 0 for record in repair_gates
                    )
                    if gates_clean:
                        solver_ay = target / "release" / "ay"
                        repair_candidate = prepare_candidate_solver(
                            solver_ay,
                            run_dir,
                            results_root,
                            tested_sha=git(worktree, "rev-parse", "HEAD"),
                            label="repair",
                        )
                        packet["repair_candidate"] = repair_candidate
                        rerun = execute_lanes(
                            selected,
                            repo,
                            worktree,
                            run_dir,
                            env,
                            supervisor_ay,
                            supervisor_sha256,
                            repair_candidate,
                            suffix="-repair",
                        )
                        packet["benchmarks"].extend(
                            row.as_json() for row in rerun
                        )
                        scoreboard_outcomes = [*blocked, *rerun]
                        official_clean = official_selection_clean(
                            args.official,
                            selected,
                            rerun,
                        )
                        packet["official_admission"]["passed"] = official_clean
                        clean = (
                            outcomes_clean(rerun)
                            and canaries_clean(selected, rerun)
                            and official_clean
                        )

            tested_sha = git(worktree, "rev-parse", "HEAD")
            packet["tested_sha"] = tested_sha
            if clean and args.push and tested_sha != base_sha:
                if args.publish_issue or publish_status:
                    packet["progress"] = "pre-push-publication"
                    pre_push_published = checkpoint_progress(
                        repo,
                        remote,
                        state_root,
                        run_dir,
                        state_path,
                        packet,
                        state,
                        publish=args.publish_issue,
                        publish_status=publish_status,
                    )
                    packet.pop("progress", None)
                    if not pre_push_published:
                        packet["push"] = {
                            "status": "publication-blocked",
                            "reason": (
                                "requested GitHub dashboard could not be "
                                "updated immediately before remote mutation"
                            ),
                        }
                        clean = False
                if not clean:
                    admission_clean = False
                elif (
                    git_code(
                        worktree,
                        "merge-base",
                        "--is-ancestor",
                        base_sha,
                        tested_sha,
                    )
                    != 0
                ):
                    packet["push"] = {
                        "status": "unsafe-non-fast-forward-rejected",
                        "expected_base": base_sha,
                        "tested_sha": tested_sha,
                    }
                    clean = False
                else:
                    live = capture(
                        ["git", "ls-remote", remote, f"refs/heads/{base_branch}"],
                        worktree,
                    )
                    live_sha = live.split()[0] if live else ""
                    if live_sha != base_sha:
                        packet["push"] = {
                            "status": "race-rejected",
                            "expected_base": base_sha,
                            "live_base": live_sha,
                        }
                        clean = False
                    else:
                        push = run_command(
                            [
                                "git",
                                "push",
                                (
                                    "--force-with-lease="
                                    f"refs/heads/{base_branch}:{base_sha}"
                                ),
                                remote,
                                f"{tested_sha}:refs/heads/{base_branch}",
                            ],
                            worktree,
                            run_dir / "git" / "push.log",
                        )
                        packet["push"] = {
                            "status": "pushed"
                            if push.exit_code == 0
                            else "failed",
                            "command": push.as_json(),
                        }
                        clean = push.exit_code == 0
            elif clean and args.push:
                live = capture(
                    ["git", "ls-remote", remote, f"refs/heads/{base_branch}"],
                    worktree,
                )
                live_sha = live.split()[0] if live else ""
                if live_sha != base_sha:
                    packet["push"] = {
                        "status": "race-rejected",
                        "expected_base": base_sha,
                        "live_base": live_sha,
                    }
                    clean = False
                else:
                    packet["push"] = {"status": "no-change"}

            admission_clean = clean
            packet["status"] = "passed" if clean else "failed"
        except CycleInterrupted as error:
            packet["status"] = "failed"
            packet["error"] = f"{type(error).__name__}: {error}"
        except Exception as error:
            packet["status"] = "failed"
            packet["error"] = f"{type(error).__name__}: {error}"
        finally:
            packet["finished_at"] = utc_now().isoformat()
            try:
                cleanup_worktree(repo, worktree)
            except Exception as error:
                packet["worktree_cleanup_error"] = (
                    f"{type(error).__name__}: {error}"
                )
                packet["status"] = "failed"
            try:
                cleanup_run_target(state_root, target)
            except Exception as error:
                packet["target_cleanup_error"] = (
                    f"{type(error).__name__}: {error}"
                )
                packet["status"] = "failed"
            try:
                current_branch = git(repo, "branch", "--show-current")
                if current_branch != base_branch:
                    raise CampaignError(
                        f"automation checkout is on {current_branch!r}, "
                        f"expected {base_branch!r}"
                    )
                update_to = packet.get("base_sha")
                if packet.get("push", {}).get("status") == "pushed":
                    update_to = packet.get("tested_sha")
                if update_to:
                    update = run_command(
                        ["git", "merge", "--ff-only", str(update_to)],
                        repo,
                        run_dir / "git" / "self-update.log",
                    )
                    packet["self_update"] = update.as_json()
                    if update.exit_code != 0:
                        packet["status"] = "failed"
                    elif os.environ.get("INVOCATION_ID"):
                        reload_record = run_command(
                            ["systemctl", "--user", "daemon-reload"],
                            repo,
                            run_dir / "systemd" / "daemon-reload.log",
                            timeout=30,
                        )
                        packet["systemd_daemon_reload"] = reload_record.as_json()
                        if reload_record.exit_code != 0:
                            packet["status"] = "failed"
            except Exception as error:
                packet["self_update"] = {
                    "exit_code": 1,
                    "error": f"{type(error).__name__}: {error}",
                }
                packet["status"] = "failed"

        try:
            try:
                max_runs = int(manifest.get("retention", {}).get("max_runs", 720))
                preserved_score_runs = scoreboard_run_ids(state.get("scoreboard"))
                packet["retention"] = {
                    "max_runs": max_runs,
                    "official_runs_preserved": True,
                    "scoreboard_run_ids_preserved": sorted(preserved_score_runs),
                    "removed_run_ids": prune_run_history(
                        state_root,
                        max_runs=max_runs,
                        current_run=current_run,
                        preserved_run_ids=preserved_score_runs,
                    ),
                }
            except Exception as error:
                packet["retention"] = {
                    "status": "failed",
                    "error": f"{type(error).__name__}: {error}",
                }
                packet["status"] = "failed"
            packet.pop("progress", None)
            promote_scores = admission_clean and packet["status"] == "passed"
            next_state = dict(state)
            if promote_scores:
                next_state["rolling_cursor"] = next_cursor
                if args.official and any(
                    lane.get("kind") == "official" for lane in selected
                ):
                    next_state["official_cursor"] = next_official_cursor
            next_state["lane_shards"] = update_lane_shards(
                next_state.get("lane_shards"),
                scoreboard_outcomes,
                current_run=current_run,
                tested_sha=tested_sha,
                promote=promote_scores,
            )
            next_state["last_run_id"] = current_run
            next_state["last_tested_sha"] = tested_sha
            next_state["scoreboard"] = update_scoreboard(
                next_state.get("scoreboard"),
                scoreboard_outcomes,
                current_run=current_run,
                tested_sha=tested_sha,
                promote_scores=promote_scores,
            )
            for lane_id, shard_progress in next_state["lane_shards"].items():
                if (
                    lane_id in next_state["scoreboard"]
                    and isinstance(shard_progress, dict)
                ):
                    next_state["scoreboard"][lane_id]["shard_progress"] = {
                        key: shard_progress.get(key)
                        for key in (
                            "next_index",
                            "shard_count",
                            "corpus_benchmark_count",
                            "coverage_benchmarks_upper_bound",
                            "coverage_fraction",
                            "completed_sweeps",
                            "score_aggregation",
                        )
                    }
            packet["scoreboard"] = next_state["scoreboard"]
            packet["lane_shards"] = next_state["lane_shards"]
            published = checkpoint_progress(
                repo,
                remote,
                state_root,
                run_dir,
                state_path,
                packet,
                next_state,
                publish=args.publish_issue,
                publish_status=publish_status,
                persist_state=False,
            )
            if (args.publish_issue or publish_status) and not published:
                # Admission and a completed push are historical facts and their
                # state must not be rolled back. Surface the dashboard outage as
                # an operational failure while preserving those facts/cursors.
                packet["status"] = "failed"
                checkpoint_progress(
                    repo,
                    remote,
                    state_root,
                    run_dir,
                    state_path,
                    packet,
                    next_state,
                    publish=False,
                    publish_status=False,
                    persist_state=False,
                )
            atomic_json(state_path, next_state)
            markdown = render_markdown(packet)
            print(markdown)
            return 0 if packet["status"] == "passed" else 1
        finally:
            disarm_cycle_deadline(previous_signal_handlers)


def audit(args: argparse.Namespace) -> int:
    repo = Path(args.repo).resolve()
    corpus_root = validate_shared_corpus_root(repo)
    lanes = load_toml((repo / args.lanes).resolve())
    catalog_path = (repo / args.catalog).resolve()
    validate_lane_manifest(lanes, catalog_path)
    catalog = competition_summary(catalog_path)
    lane_rows = lanes.get("lane", [])
    counts: dict[str, int] = {}
    for lane in lane_rows:
        kind = str(lane.get("kind", "unknown"))
        counts[kind] = counts.get(kind, 0) + 1
    operational: dict[str, str] = {}
    for lane in lane_rows:
        blocker = lane_blocker(lane, repo, corpus_root=corpus_root)
        operational[str(lane["id"])] = blocker or "ready"
    missing_tools = [
        tool
        for tool in (
            "git",
            "bwrap",
            "prlimit",
            "python3",
            "systemd-analyze",
            "ay-zig-cc",
            "ay-zig-cxx",
        )
        if shutil.which(tool) is None
    ]
    cargo = shutil.which("cargo") or str(Path.home() / ".cargo" / "bin" / "cargo")
    if not os.access(cargo, os.X_OK):
        missing_tools.append("cargo")
    canary_blocked = [
        lane["id"]
        for lane in lane_rows
        if lane.get("kind") == "canary" and operational[str(lane["id"])] != "ready"
    ]
    enabled_official = [
        lane["id"]
        for lane in lane_rows
        if lane.get("kind") == "official" and lane.get("enabled", True)
    ]
    value = {
        "lanes": {
            "total": len(lane_rows),
            "by_kind": counts,
            "operational": operational,
            "enabled_official": enabled_official,
        },
        "competition_catalog": catalog,
        "preflight": {
            "missing_tools": missing_tools,
            "blocked_canaries": canary_blocked,
        },
    }
    print(json.dumps(value, indent=2, sort_keys=True))
    return 1 if missing_tools or canary_blocked else 0


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--repo", default=".", help="automation Git checkout")
    result.add_argument(
        "--lanes",
        default="benchmarks/continuous-lanes.toml",
        help="repo-relative executable lane manifest",
    )
    result.add_argument(
        "--catalog",
        default="benchmarks/continuous-2025-2026.toml",
        help="repo-relative official competition catalog",
    )
    sub = result.add_subparsers(dest="command", required=True)
    audit_parser = sub.add_parser("audit", help="validate and summarize manifests")
    audit_parser.set_defaults(function=audit)
    cycle_parser = sub.add_parser("cycle", help="run one integration/benchmark cycle")
    cycle_parser.add_argument(
        "--bootstrap-remote",
        default="origin",
        help="trusted remote used to update the controller before loading manifests",
    )
    cycle_parser.add_argument(
        "--bootstrap-branch",
        default="main",
        help="trusted base branch used before loading manifests",
    )
    cycle_parser.add_argument(
        "--state-root",
        default=".ay-bench/continuous",
        help="persistent evidence/state directory",
    )
    cycle_parser.add_argument(
        "--cycle-timeout-sec",
        type=int,
        default=DEFAULT_CYCLE_TIMEOUT_SEC,
        help="whole-cycle deadline, leaving cleanup headroom below systemd",
    )
    cycle_parser.add_argument(
        "--smoke-only",
        action="store_true",
        help="run canaries but no rolling lane",
    )
    cycle_parser.add_argument(
        "--official",
        action="store_true",
        help="also run the next enabled competition-time lane",
    )
    cycle_parser.add_argument(
        "--push",
        action="store_true",
        help="fast-forward the tested candidate to the remote base branch",
    )
    cycle_parser.add_argument(
        "--repair-with-codex",
        action="store_true",
        help="allow one bounded Codex repair attempt before rejecting a candidate",
    )
    cycle_parser.add_argument(
        "--repair-timeout",
        type=int,
        default=3600,
        help="maximum seconds for the one repair attempt",
    )
    cycle_parser.add_argument(
        "--publish-issue",
        action="store_true",
        help="create/update one GitHub issue dashboard",
    )
    cycle_parser.add_argument(
        "--publish-status-ref",
        "--publish-status-branch",
        dest="publish_status_ref",
        action="store_true",
        help=f"publish compact progress to the non-branch Git ref {STATUS_REF}",
    )
    cycle_parser.set_defaults(function=cycle)
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        return int(args.function(args))
    except CycleInterrupted as error:
        print(f"continuous-benchmark: {error}", file=sys.stderr)
        return 2
    except CampaignError as error:
        print(f"continuous-benchmark: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
