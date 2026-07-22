#!/usr/bin/env python3
# ay-script: chccomp-harness
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""CHC-COMP multi-solver evaluation harness.

Runs AY and competitor CHC solvers (Golem, Eldarica, Z3/Spacer) on official
CHC-COMP benchmark tracks under competition-style limits, cross-validates
answers against ground-truth verdicts and between solvers, and produces
competition-style scoreboards (score = #correct; wrong answers reported and
treated as disqualifying for the local integrity bar).

Benchmark layout: github.com/chc-comp/chc-comp{25,26}-benchmarks clones under
benchmarks/chc/. Tracks are defined by top-level `<Track>.set` files listing
benchexec `.yml` tasks; each yml points at an `.smt2` input and may carry an
`expected_verdict` (true=sat/safe, false=unsat/unsafe). 2026 caveats handled
here:
  - ymls containing "placeholder verdict (auto-added)" are NOT ground truth.
  - 2026 BV-Lin.set entries under ./binary-chc-problems/ are path-flattened
    ("dir/file" -> "dir-file"); resolved by indexing the file tree.

Usage:
  python3 scripts/chccomp_harness.py run --year 2025 --track LIA-Lin \
      --solvers ay,golem,eld,z3 --timeout 60 --jobs 4 --tag dev60
  python3 scripts/chccomp_harness.py score --year 2025 --track LIA-Lin --tag dev60
  python3 scripts/chccomp_harness.py list-tracks --year 2025

Results: evals/results/chccomp-harness/<year>/<track>/<tag>/<solver>.jsonl
(one JSON object per instance; resumable only when the recorded binary,
task-set, timeout, memory, core, and concurrency envelope matches exactly).
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, asdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _oom_guard import (  # noqa: E402
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)

REPO = Path(__file__).resolve().parent.parent
BENCH_ROOT = {
    2025: REPO / "benchmarks/chc/chc-comp25-benchmarks",
    2026: REPO / "benchmarks/chc/chc-comp26-benchmarks",
}
RESULTS_ROOT = REPO / "evals/results/chccomp-harness"
SOLVER_BIN = REPO / "reference/chc-solvers/bin"

# Solver registry: name -> argv builder (file, timeout_s).
# All solvers receive the .smt2 path; timeouts are enforced by the harness
# (process-group kill), with solver-native soft timeouts passed where cheap.
def _ay_argv(file: str, timeout_s: int) -> list[str]:
    # Pin the binary per-run (AY_BIN) so an in-flight cargo rebuild can't
    # contaminate a benchmark run with mixed binaries.
    default_bin = "target/release/ay.exe" if os.name == "nt" else "target/release/ay"
    ay_bin = os.environ.get("AY_BIN", str(REPO / default_bin))
    argv = [
        ay_bin,
        "--chc",
        "--competition",
        "--timeout",
        str(timeout_s * 1000),
    ]
    # Per-child memory envelope (scripts/_oom_guard.py): without --memory each
    # ay child self-limits at 85% of RAM, sibling-blind — N concurrent children
    # multiply that allocation. ay trips
    # its internal guard gracefully; competitors are bounded by the
    # rss_watchdog backstop in run_one instead.
    if _AY_MEMLIMIT_MB:
        argv += ["--memory", str(_AY_MEMLIMIT_MB)]
    argv.append(file)
    return argv


# Golem's official CHC-COMP 2026 per-track configurations (benchmark-defs/
# golem.xml.template in github.com/chc-comp/chc-comp-2026). Tracks Golem did
# not enter fall back to its default engine (spacer).
GOLEM_TRACK_OPTS = {
    "LIA-Lin": ["--logic=QF_LIA", "--engine=imc,pdkind,spacer,split-tpa"],
    "LRA-Lin": ["--logic=QF_LRA", "--engine=imc,kind,pdkind,split-tpa"],
    "LIA": ["--logic=QF_LIA", "--engine=spacer,pa"],
    "LIA-Lin-Arrays": ["--logic=QF_ALIA", "--engine=bmc,kind"],
}

_CURRENT_TRACK: str | None = None  # set by cmd_run for track-specific options
_AY_MEMLIMIT_MB: int = 0  # per-child --memory envelope (MiB); set by cmd_run


def _golem_argv(file: str, timeout_s: int) -> list[str]:
    opts = GOLEM_TRACK_OPTS.get(_CURRENT_TRACK or "", [])
    return [str(SOLVER_BIN / "golem"), *opts, file]


def _eld_argv(file: str, timeout_s: int) -> list[str]:
    # Official 2026 config: Eldarica with -portfolio on all tracks.
    # CAVEAT: -portfolio needs the Yices 1.x CLI that the Linux competition
    # dist bundles; with brew yices2 it dies ("null read from yices"). Until a
    # yices1 build is available locally we run the default configuration and
    # note the deviation in reports. TODO(eldarica-portfolio).
    return [str(SOLVER_BIN / "eld-native"), file]


def _z3_argv(file: str, timeout_s: int) -> list[str]:
    # Official 2026 config ran plain z3 (Spacer is the default HORN engine).
    return [str(SOLVER_BIN / "z3"), file]


SOLVERS = {
    "ay": _ay_argv,
    "golem": _golem_argv,
    "eld": _eld_argv,
    "z3": _z3_argv,
}

STATUS_LINES = {"sat", "unsat", "unknown"}

REQUIRED_ENVELOPE_FIELDS = {
    "schema", "year", "track", "task_count", "task_set_sha256",
    "benchmark_revision", "requested_jobs", "jobs",
    "memlimit_mb_per_child", "nbcore_per_child", "headroom_mb",
    "memory_enforcement", "rss_grace_mb", "solver_env", "timeout_sec",
    "parent_wall_timeout_sec", "timeout_enforcement", "capture",
    "native_memory_enforcement", "solver", "solver_command", "executable",
    "harness",
}


@dataclass
class Task:
    rel_id: str  # yml path relative to benchmark root (stable instance id)
    smt2: str  # absolute path to .smt2 input
    verdict: str | None  # "sat" | "unsat" | None (no ground truth)
    placeholder: bool  # verdict came from placeholders.py (not ground truth)


def _resolve_flattened(root: Path, entry: str, index: dict[str, str]) -> str | None:
    """Resolve 2026 BV-Lin flattened set entries via a flattened-path index."""
    return index.get(entry.lstrip("./"))


def _build_flat_index(root: Path, subdir: str) -> dict[str, str]:
    index: dict[str, str] = {}
    base = root / subdir
    if not base.is_dir():
        return index
    for p in base.rglob("*.yml"):
        rel = p.relative_to(root)
        flat = "-".join(rel.parts[:-1]) + "-" + rel.parts[-1] if len(rel.parts) > 1 else rel.parts[-1]
        # The flattening joins path components under the source dir with '-'
        # e.g. binary-chc-problems/c/VeriMAP/MAP-x/MAP-x.-O0.yml
        #   -> binary-chc-problems/c/VeriMAP-MAP-x-MAP-x.-O0.yml
        parts = rel.parts
        for k in range(1, len(parts)):
            prefix = "/".join(parts[:k])
            suffix = "-".join(parts[k:])
            index[f"{prefix}/{suffix}"] = str(rel)
    return index


_VERDICT_RE = re.compile(r"expected_verdict:\s*(true|false)")
_INPUT_RE = re.compile(r"input_files:\s*'?([^'\n]+)'?")


def load_track(year: int, track: str) -> list[Task]:
    root = BENCH_ROOT[year]
    set_file = root / f"{track}.set"
    if not set_file.is_file():
        raise SystemExit(f"no such track set: {set_file}")
    flat_index: dict[str, str] | None = None
    tasks: list[Task] = []
    missing = 0
    for raw in set_file.read_text(encoding="utf-8", errors="replace").splitlines():
        entry = raw.strip()
        if not entry or entry.startswith("#"):
            continue
        yml = root / entry
        if not yml.is_file():
            if flat_index is None:
                flat_index = _build_flat_index(root, "binary-chc-problems")
            resolved = _resolve_flattened(root, entry, flat_index)
            if resolved is None:
                missing += 1
                continue
            yml = root / resolved
            entry = resolved
        text = yml.read_text(encoding="utf-8", errors="replace")
        placeholder = "placeholder verdict" in text
        m = _VERDICT_RE.search(text)
        verdict = None
        if m and not placeholder:
            verdict = "sat" if m.group(1) == "true" else "unsat"
        im = _INPUT_RE.search(text)
        if not im:
            missing += 1
            continue
        smt2 = (yml.parent / im.group(1).strip()).resolve()
        if not smt2.is_file():
            missing += 1
            continue
        tasks.append(Task(rel_id=entry, smt2=str(smt2), verdict=verdict, placeholder=placeholder))
    if missing:
        print(f"[load_track] {year}/{track}: {missing} entries unresolved/missing", file=sys.stderr)
    return tasks


def parse_status(stdout: str) -> str:
    statuses = set()
    for line in stdout.splitlines():
        token = line.strip()
        if token in STATUS_LINES:
            statuses.add(token)
        elif token == "s SATISFIABLE":
            statuses.add("sat")
        elif token == "s UNSATISFIABLE":
            statuses.add("unsat")
    if len(statuses) > 1:
        return "conflicting-status"
    return next(iter(statuses), "no-status")


def parse_status_stream(stream) -> str:
    """Parse a seekable text stream without retaining arbitrary solver logs."""
    stream.flush()
    stream.seek(0)
    statuses = set()
    for line in stream:
        token = line.strip()
        if token in STATUS_LINES:
            statuses.add(token)
        elif token == "s SATISFIABLE":
            statuses.add("sat")
        elif token == "s UNSATISFIABLE":
            statuses.add("unsat")
    if len(statuses) > 1:
        return "conflicting-status"
    return next(iter(statuses), "no-status")


def stream_tail(stream, limit: int = 500) -> str:
    stream.flush()
    stream.seek(0)
    tail = ""
    while True:
        chunk = stream.read(8192)
        if not chunk:
            return tail
        tail = (tail + chunk)[-limit:]


def kill_process_tree(proc: subprocess.Popen) -> None:
    if os.name == "nt":
        subprocess.run(
            ["taskkill", "/F", "/T", "/PID", str(proc.pid)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def executable_provenance(command: str) -> dict:
    """Stable binary identity used to keep resumable tags homogeneous."""
    candidate = Path(command)
    if not candidate.is_absolute():
        repo_candidate = (REPO / candidate).resolve()
        resolved = repo_candidate if repo_candidate.exists() else None
    else:
        resolved = candidate.resolve()
    if resolved is None:
        found = shutil.which(command)
        resolved = Path(found).resolve() if found else candidate
    try:
        stat = resolved.stat()
        digest = hashlib.sha256()
        with resolved.open("rb") as binary:
            for chunk in iter(lambda: binary.read(1024 * 1024), b""):
                digest.update(chunk)
        return {
            "path": str(resolved),
            "size": stat.st_size,
            "sha256": digest.hexdigest(),
        }
    except OSError:
        return {"path": str(resolved), "size": None, "sha256": None}


def canonical_envelope(envelope: dict | None) -> str | None:
    if not isinstance(envelope, dict):
        return None
    return json.dumps(envelope, sort_keys=True, separators=(",", ":"))


def comparison_envelope(envelope: dict | None) -> dict | None:
    """Drop solver identity while retaining all shared score conditions."""
    if not isinstance(envelope, dict):
        return None
    return {k: v for k, v in envelope.items()
            if k not in {"solver", "solver_command", "executable",
                         "native_memory_enforcement"}}


def run_one(solver: str, task: Task, timeout_s: int, memlimit_mb: int = 0,
            nbcore: int = 1, resource_envelope: dict | None = None) -> dict:
    if memlimit_mb <= 0 or nbcore <= 0:
        raise ValueError("CHC run requires positive memory and core budgets")
    argv = SOLVERS[solver](task.smt2, timeout_s)
    start = time.monotonic()
    status = "error"
    exit_code: int | None = None
    stderr_tail = ""
    memout = False
    child_env = dict(os.environ, MEMLIMIT=str(memlimit_mb), NBCORE=str(nbcore))
    timed_out = False
    try:
        captured = run_captured(
            argv,
            memlimit_mb,
            timeout_s + 5,
            label=f"chccomp_harness.py[{solver}]",
            cwd=str(REPO),
            env=child_env,
        )
    except Exception as exc:
        stderr_tail = str(exc)[-500:]
        captured = None
    if captured is not None:
        exit_code = captured.returncode
        memout = captured.memout
        timed_out = captured.timed_out
        stderr_tail = captured.stderr[-500:]
        if captured.cancelled or captured.output_truncated:
            status = "error"
            stderr_tail = ("solver output truncated or capture cancelled; " +
                           stderr_tail)[-500:]
        else:
            status = parse_status_stream(io.StringIO(captured.stdout))
            if status == "conflicting-status":
                status = "error"
                stderr_tail = ("conflicting solver status lines; " +
                               stderr_tail)[-500:]
            elif status == "no-status":
                status = "timeout" if (timed_out or exit_code == 124) else "error"
    if memout:
        status = "memout"
    elif timed_out:
        status = "timeout"
    wall = captured.wall_sec if captured is not None else time.monotonic() - start

    correct = None
    if status in ("sat", "unsat") and task.verdict is not None:
        correct = status == task.verdict
    return {
        "instance": task.rel_id,
        "solver": solver,
        "status": status,
        "wall_sec": round(wall, 3),
        "timeout_sec": timeout_s,
        # Enforced per-child memory envelope (MiB; 0 = none). Results cached
        # in resumable JSONL files may span runs — the envelope must live on
        # each record or cross-envelope scoreboards are silently mixed.
        "memlimit_mb": memlimit_mb,
        "nbcore": nbcore,
        "resource_envelope": resource_envelope,
        "memout": memout,
        "timed_out": timed_out,
        "exit_code": exit_code,
        "verdict": task.verdict,
        "placeholder_verdict": task.placeholder,
        "correct": correct,
        "stderr_tail": stderr_tail if status == "error" else "",
    }


def results_dir(year: int, track: str, tag: str) -> Path:
    d = RESULTS_ROOT / str(year) / track / tag
    d.mkdir(parents=True, exist_ok=True)
    return d


def load_done(path: Path) -> dict[str, dict]:
    done: dict[str, dict] = {}
    if path.is_file():
        for line in path.read_text().splitlines():
            if not line.strip():
                continue
            try:
                rec = json.loads(line)
                instance = rec["instance"]
            except (json.JSONDecodeError, KeyError, TypeError):
                continue
            done[instance] = rec
    return done


def count_envelope_mismatches(path: Path, expected: str) -> int:
    """Inspect every physical JSONL record, including superseded duplicates."""
    if not path.is_file():
        return 0
    mismatches = 0
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            mismatches += 1
            continue
        if canonical_envelope(record.get("resource_envelope")) != expected:
            mismatches += 1
    return mismatches


def stratified_sample(tasks: list[Task], n: int, seed: int = 2026) -> list[Task]:
    """Deterministic stratified sample by top-level benchmark family."""
    import random

    if n >= len(tasks):
        return tasks
    by_family: dict[str, list[Task]] = {}
    for t in sorted(tasks, key=lambda t: t.rel_id):
        by_family.setdefault(t.rel_id.split("/")[0], []).append(t)
    rng = random.Random(seed)
    picked: list[Task] = []
    # proportional allocation with at least 1 per family
    total = len(tasks)
    for fam, members in sorted(by_family.items()):
        k = max(1, round(n * len(members) / total))
        picked.extend(rng.sample(members, min(k, len(members))))
    # trim/extend to exactly n deterministically
    rng.shuffle(picked)
    if len(picked) > n:
        picked = picked[:n]
    return sorted(picked, key=lambda t: t.rel_id)


def git_revision(path: Path) -> str | None:
    try:
        proc = subprocess.run(
            ["git", "-C", str(path), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        return proc.stdout.strip() if proc.returncode == 0 else None
    except (OSError, subprocess.TimeoutExpired):
        return None


def make_run_envelope(solver: str, task: Task, args: argparse.Namespace,
                      requested_jobs: int, plan, tasks: list[Task]) -> dict:
    argv = SOLVERS[solver](task.smt2, args.timeout)
    normalized_argv = ["<instance>" if value == task.smt2 else value
                       for value in argv]
    task_digest = hashlib.sha256()
    for selected in sorted(tasks, key=lambda value: value.rel_id):
        try:
            stat = Path(selected.smt2).stat()
            identity = (f"{selected.rel_id}\0{selected.verdict}\0"
                        f"{selected.placeholder}\0{stat.st_size}\0"
                        f"{stat.st_mtime_ns}\0")
        except OSError:
            identity = (f"{selected.rel_id}\0{selected.verdict}\0"
                        f"{selected.placeholder}\0missing\0")
        task_digest.update(identity.encode("utf-8", errors="surrogateescape"))
    return {
        "schema": "ay.benchmark-resource-envelope/v1",
        "year": args.year,
        "track": args.track,
        "task_count": len(tasks),
        "task_set_sha256": task_digest.hexdigest(),
        "benchmark_revision": git_revision(BENCH_ROOT[args.year]),
        "requested_jobs": requested_jobs,
        "jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "memory_enforcement": "process-group rss_watchdog",
        "rss_grace_mb": 0,
        "solver_env": {"MEMLIMIT": str(plan.memlimit_mb),
                       "NBCORE": str(plan.nbcore)},
        "native_memory_enforcement": "--memory" if solver == "ay" else None,
        "timeout_sec": args.timeout,
        "parent_wall_timeout_sec": args.timeout + 5,
        "timeout_enforcement": "process-group SIGKILL + reap",
        "capture": "temporary files (bounded parent RAM)",
        "solver": solver,
        "solver_command": normalized_argv,
        "executable": executable_provenance(argv[0]),
        "harness": executable_provenance(__file__),
    }


def cmd_run(args: argparse.Namespace) -> int:
    global _CURRENT_TRACK, _AY_MEMLIMIT_MB
    if args.jobs <= 0 or args.timeout <= 0 or args.limit < 0 or args.sample < 0:
        print("[run] jobs/timeout must be positive; limit/sample nonnegative",
              file=sys.stderr)
        return 2
    _CURRENT_TRACK = args.track
    tasks = load_track(args.year, args.track)
    if args.only_gt:
        tasks = [t for t in tasks if t.verdict is not None]
    if args.sample:
        tasks = stratified_sample(tasks, args.sample, args.seed)
    if args.limit:
        tasks = tasks[: args.limit]
    solvers = [solver.strip() for solver in args.solvers.split(",")
               if solver.strip()]
    if not solvers:
        print("[run] at least one solver is required", file=sys.stderr)
        return 2
    for s in solvers:
        if s not in SOLVERS:
            raise SystemExit(f"unknown solver {s}; known: {list(SOLVERS)}")

    # OOM guard (scripts/_oom_guard.py): N parallel children are sibling-blind;
    # each ay child would
    # default to 85% of RAM. Cap jobs to a safe RAM budget and enforce a
    # per-child envelope: --memory for ay (graceful internal guard),
    # rss_watchdog hard kill for every solver (status: memout).
    if not tasks:
        print(f"[run] {args.year}/{args.track}: no selected tasks", file=sys.stderr)
        return 2
    try:
        warn_concurrent_build()
        requested_jobs = args.jobs
        plan = plan_solver_resources(args.jobs, label="chccomp_harness.py")
    except RuntimeError as exc:
        if "REFUSING" not in str(exc):
            print(f"[run] resource planning failed: {exc}", file=sys.stderr)
        return 2
    if plan.memlimit_mb <= 0 or plan.nbcore <= 0:
        print("[run] resource planner returned an unenforceable envelope",
              file=sys.stderr)
        return 2
    if os.name == "nt" or not hasattr(os, "killpg"):
        print("[run] exact process-group RSS enforcement requires POSIX",
              file=sys.stderr)
        return 2
    args.jobs = plan.jobs
    _AY_MEMLIMIT_MB = plan.memlimit_mb

    out_dir = results_dir(args.year, args.track, args.tag)
    envelopes = {
        solver: make_run_envelope(
            solver, tasks[0], args, requested_jobs, plan, tasks,
        )
        for solver in solvers
    }
    unavailable = [
        solver for solver, envelope in envelopes.items()
        if not envelope["executable"].get("sha256")
    ]
    if unavailable:
        print("[run] solver executable(s) unavailable: " + ", ".join(
            f"{solver}={envelopes[solver]['executable']['path']}"
            for solver in unavailable
        ), file=sys.stderr)
        return 2

    # Preflight every resume file before spawning anything. A tag is one
    # measurement condition; mixing old binaries, timeouts, task sets, or
    # resource envelopes would make both cached skips and rankings unsound.
    cached_by_solver = {}
    for solver in solvers:
        out_path = out_dir / f"{solver}.jsonl"
        done = load_done(out_path)
        expected = canonical_envelope(envelopes[solver])
        mismatched = count_envelope_mismatches(out_path, expected)
        if mismatched:
            print(
                f"[run] REFUSING to mix {mismatched} stale/legacy "
                f"{solver} record(s) in {out_path}; use a new --tag for this "
                "binary/resource/timeout/task envelope",
                file=sys.stderr,
            )
            return 2
        cached_by_solver[solver] = done
        (out_dir / f"{solver}.resource-envelope.json").write_text(
            json.dumps(envelopes[solver], indent=2) + "\n"
        )

    print(f"[run] {args.year}/{args.track} tag={args.tag}: {len(tasks)} tasks, solvers={solvers}, timeout={args.timeout}s, jobs={args.jobs}")
    print(f"[run] resource plan: requested={requested_jobs}, jobs={plan.jobs}, "
          f"envelope={plan.memlimit_mb} MiB/child, NBCORE={plan.nbcore} "
          f"(exact rss watchdog; AY also --memory), "
          f"headroom={plan.headroom_mb} MiB",
          flush=True)

    for solver in solvers:
        out_path = out_dir / f"{solver}.jsonl"
        done = cached_by_solver[solver]
        todo = [t for t in tasks if t.rel_id not in done]
        if not todo:
            print(f"[run] {solver}: all {len(tasks)} done")
            continue
        print(f"[run] {solver}: {len(todo)} to run ({len(done)} cached)")
        lock = threading.Lock()
        completed = 0
        t0 = time.monotonic()
        with out_path.open("a") as fh, ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futs = {
                pool.submit(
                    run_one,
                    solver,
                    t,
                    args.timeout,
                    plan.memlimit_mb,
                    plan.nbcore,
                    envelopes[solver],
                ): t
                for t in todo
            }
            for fut in as_completed(futs):
                rec = fut.result()
                with lock:
                    fh.write(json.dumps(rec) + "\n")
                    fh.flush()
                    completed += 1
                    if completed % 25 == 0 or completed == len(todo):
                        rate = completed / max(time.monotonic() - t0, 1e-9)
                        eta = (len(todo) - completed) / max(rate, 1e-9)
                        print(f"[run] {solver}: {completed}/{len(todo)} ({rate:.2f}/s, eta {eta/60:.1f}m)", flush=True)
    report = summarize(args.year, args.track, args.tag, solvers)
    if not report["sound"]:
        return 3
    return 0 if report["comparable"] else 2


def summarize(year: int, track: str, tag: str, solvers: list[str] | None = None) -> dict:
    out_dir = results_dir(year, track, tag)
    files = sorted(out_dir.glob("*.jsonl"))
    if solvers:
        files = [f for f in files if f.stem in solvers]
    board = {}
    by_solver: dict[str, dict[str, dict]] = {}
    comparison_conditions = set()
    envelope_issues = []
    instance_sets: dict[str, set[str]] = {}
    if not files:
        envelope_issues.append("no solver result files")
    for f in files:
        recs = load_done(f)
        by_solver[f.stem] = recs
        instance_sets[f.stem] = set(recs)
        full_envelopes = {
            canonical_envelope(record.get("resource_envelope"))
            for record in recs.values()
        }
        if not recs:
            envelope_issues.append(f"{f.name}: no records")
        elif None in full_envelopes:
            envelope_issues.append(
                f"{f.name}: legacy record(s) lack a complete resource envelope"
            )
        elif len(full_envelopes) != 1:
            envelope_issues.append(
                f"{f.name}: records mix {len(full_envelopes)} run envelopes"
            )
        else:
            only = next(iter(recs.values())).get("resource_envelope")
            missing = sorted(REQUIRED_ENVELOPE_FIELDS - set(only))
            if missing:
                envelope_issues.append(
                    f"{f.name}: incomplete resource envelope (missing {missing})"
                )
            else:
                if len(recs) != only["task_count"]:
                    envelope_issues.append(
                        f"{f.name}: partial task set ({len(recs)}/"
                        f"{only['task_count']} records)"
                    )
                bad_records = [
                    instance for instance, record in recs.items()
                    if (record.get("solver") != f.stem or
                        record.get("timeout_sec") != only["timeout_sec"] or
                        record.get("memlimit_mb") !=
                        only["memlimit_mb_per_child"] or
                        record.get("nbcore") != only["nbcore_per_child"])
                ]
                if bad_records:
                    envelope_issues.append(
                        f"{f.name}: {len(bad_records)} record field(s) "
                        "disagree with the file/envelope"
                    )
                comparison_conditions.add(
                    canonical_envelope(comparison_envelope(only))
                )
        sat = sum(1 for r in recs.values() if r["status"] == "sat")
        unsat = sum(1 for r in recs.values() if r["status"] == "unsat")
        wrong = sum(1 for r in recs.values() if r.get("correct") is False)
        solved = sat + unsat - wrong
        valid_answers = [r for r in recs.values()
                         if r["status"] in ("sat", "unsat")
                         and r.get("correct") is not False]
        board[f.stem] = {
            "total_run": len(recs),
            "solved": solved,
            "sat": sat,
            "unsat": unsat,
            "wrong": wrong,
            "timeout": sum(1 for r in recs.values() if r["status"] == "timeout"),
            "memout": sum(1 for r in recs.values() if r["status"] == "memout"),
            "unknown": sum(1 for r in recs.values() if r["status"] == "unknown"),
            "error": sum(1 for r in recs.values() if r["status"] == "error"),
            # Envelopes present in this (resumable, possibly multi-run) file;
            # >1 distinct value means mixed measurement conditions.
            "memlimit_mb_values": sorted(
                {r.get("memlimit_mb", 0) for r in recs.values()}
            ),
            "resource_envelope_count": len(full_envelopes),
            "avg_wall_solved": round(
                sum(r["wall_sec"] for r in valid_answers) /
                max(len(valid_answers), 1), 2
            ),
        }
    # Cross-solver disagreements (definite answers conflicting), incl. vs placeholder-free verdicts
    disagreements = []
    all_instances = set()
    for recs in by_solver.values():
        all_instances.update(recs.keys())
    for inst in sorted(all_instances):
        answers = {}
        for s, recs in by_solver.items():
            r = recs.get(inst)
            if r and r["status"] in ("sat", "unsat"):
                answers[s] = r["status"]
        verdict = None
        for s, recs in by_solver.items():
            r = recs.get(inst)
            if r and r["verdict"] and not r["placeholder_verdict"]:
                verdict = r["verdict"]
                break
        if verdict:
            answers["_groundtruth"] = verdict
        if len(set(answers.values())) > 1:
            disagreements.append({"instance": inst, "answers": answers})
    if len(comparison_conditions) > 1:
        envelope_issues.append(
            "solver files use different shared resource/timeout/task envelopes"
        )
    if len({frozenset(instances) for instances in instance_sets.values()}) > 1:
        envelope_issues.append("solver files cover different instance sets")
    comparable = bool(files) and not envelope_issues
    sound = not disagreements and all(row["wrong"] == 0
                                      for row in board.values())
    report = {
        "year": year,
        "track": track,
        "tag": tag,
        "comparable": comparable,
        "sound": sound,
        "comparability_issues": envelope_issues,
        "scoreboard": board,
        "disagreements": disagreements,
    }
    report_path = results_dir(year, track, tag) / "scoreboard.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"\n=== {year}/{track} [{tag}] ===")
    if envelope_issues:
        print("  REFUSING performance comparison: measurement envelopes are "
              "missing or inconsistent")
        for issue in envelope_issues:
            print(f"    - {issue}")
    ordering = (sorted(board.items(), key=lambda kv: -kv[1]["solved"])
                if comparable else sorted(board.items()))
    for s, row in ordering:
        print(
            f"  {s:8s} solved={row['solved']:5d} (sat {row['sat']}, unsat {row['unsat']}) "
            f"wrong={row['wrong']} timeout={row['timeout']} memout={row['memout']} "
            f"unknown={row['unknown']} err={row['error']} "
            f"avg={row['avg_wall_solved']}s n={row['total_run']}"
        )
        if len(row["memlimit_mb_values"]) > 1:
            print(f"           !! mixed memory envelopes in {s}.jsonl: "
                  f"{row['memlimit_mb_values']} MiB — solved/timeout deltas "
                  f"may be envelope artifacts")
    if disagreements:
        print(f"  !! {len(disagreements)} disagreement(s) — see {report_path}")
    return report


def cmd_score(args: argparse.Namespace) -> int:
    report = summarize(args.year, args.track, args.tag)
    if not report["sound"]:
        return 3
    return 0 if report["comparable"] else 2


def cmd_list_tracks(args: argparse.Namespace) -> int:
    root = BENCH_ROOT[args.year]
    for s in sorted(root.glob("*.set")):
        tasks = load_track(args.year, s.stem)
        n_gt = sum(1 for t in tasks if t.verdict)
        print(f"{s.stem}: {len(tasks)} tasks ({n_gt} with ground truth)")
    return 0


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)

    rp = sub.add_parser("run")
    rp.add_argument("--year", type=int, default=2025, choices=(2025, 2026))
    rp.add_argument("--track", required=True)
    rp.add_argument("--solvers", default="ay,golem,eld,z3")
    rp.add_argument("--timeout", type=int, default=60)
    rp.add_argument("--jobs", type=int, default=4)
    rp.add_argument("--tag", required=True, help="run label, e.g. dev60, comp1800")
    rp.add_argument("--limit", type=int, default=0, help="only first N tasks (smoke)")
    rp.add_argument(
        "--only-gt",
        action="store_true",
        help="only instances with a (non-placeholder) expected_verdict — the scoreable set",
    )
    rp.add_argument("--sample", type=int, default=0, help="stratified sample of N tasks")
    rp.add_argument("--seed", type=int, default=2026, help="sample seed")
    rp.set_defaults(func=cmd_run)

    sp = sub.add_parser("score")
    sp.add_argument("--year", type=int, default=2025, choices=(2025, 2026))
    sp.add_argument("--track", required=True)
    sp.add_argument("--tag", required=True)
    sp.set_defaults(func=cmd_score)

    lp = sub.add_parser("list-tracks")
    lp.add_argument("--year", type=int, default=2025, choices=(2025, 2026))
    lp.set_defaults(func=cmd_list_tracks)

    args = ap.parse_args()
    sys.exit(args.func(args))


if __name__ == "__main__":
    main()
