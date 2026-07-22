#!/usr/bin/env python3
# ay-script: pbcomp-harness
"""PB-COMP benchmark harness for the AY pseudo-Boolean solver.

Runs AY (`ay pb solve`) over a directory of OPB/WBO instances under a hard
wall-clock timeout, parses the competition output (`s`/`o`/`v` lines), and --
critically -- VERIFIES every SAT/OPTIMUM answer against the instance so that a
wrong answer (which disqualifies an entire competition category) is caught here
rather than by the competition judges.

It produces per-category solve rates, a PAR-2 score, and an optional diff
against a baseline CSV so regressions (solved -> timeout) and soundness
conflicts (UNSAT <-> SAT) are surfaced immediately.

Solution checking has two backends:
  * python (default): a self-contained OPB/WBO evaluator in this file.
  * ay:               shells out to `ay pb verify` (authoritative; uses the
                      solver's own evaluator). Use once that subcommand exists.

Core budgeting: the solver's parallel portfolio sizes its worker pool from the
NBCORE environment variable (competition convention). With --jobs N > 1, N
concurrent solver processes that each assume they own the whole machine would
oversubscribe every core and turn wall-times into load noise, so the harness
exports NBCORE = max(1, physical_cores // jobs) into each child's environment:
every process gets a fair, honest core budget and parallel-mode measurement is
preserved (rather than disabled). The shared resource planner is authoritative
at --jobs 1 too, so inherited MEMLIMIT/NBCORE values cannot silently change the
recorded execution envelope.

Memory budgeting (scripts/_oom_guard.py; 2026-06-19 / 2026-07-11 watchdog
panics): every child gets the planner's per-child envelope, at --jobs 1 too —
via the MEMLIMIT env for ay-pb-lineage binaries (which honor it) AND an
external RSS-watchdog kill (status MEMOUT) as the backstop, because the
default `ay pb solve` binary ignores MEMLIMIT and sets no memory limit at
all. Each JSONL record carries the complete enforced memory/core/timeout and
binary envelope, so runs measured under different conditions are refused by
the scorer rather than silently compared.

Usage:
    scripts/pbcomp_harness.py run \
        --bin target/release/ay \
        --instances benchmarks/pb-comp/selected-PB25 \
        --timeout 30 --jobs 8 \
        --baseline benchmarks/pb-comp/results/pb25-baseline.csv \
        --out evals/results/pbcomp/run.jsonl

    scripts/pbcomp_harness.py score --out evals/results/pbcomp/run.jsonl
"""
from __future__ import annotations

import argparse
import concurrent.futures
import dataclasses
import hashlib
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
from pathlib import Path
from typing import Optional

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _oom_guard import (  # noqa: E402
    plan_solver_resources,
    rss_watchdog,
    warn_concurrent_build,
)


# ----------------------------------------------------------------------------
# OPB / WBO parsing + solution checking (self-contained)
# ----------------------------------------------------------------------------

_TOKEN_RE = re.compile(r"\S+")


@dataclasses.dataclass
class Constraint:
    # terms: list of (coeff, [literals]); literal is (var:int, negated:bool)
    terms: list
    op: str  # ">=", "<=", "="
    degree: int
    weight: Optional[int] = None  # None => hard; int => soft (WBO)


@dataclasses.dataclass
class Instance:
    constraints: list
    objective: Optional[list]  # list of (coeff, [literals]) or None
    n_vars: int
    is_wbo: bool
    top_cost: Optional[int]
    nonlinear: bool


def _parse_literal(tok: str):
    """Parse a single literal token like 'x12', '~x12', '-x12' -> (var, negated)."""
    neg = False
    if tok.startswith("~"):
        neg = True
        tok = tok[1:]
    elif tok.startswith("-x") or tok.startswith("-~"):
        # v-line style negation '-x5'
        neg = True
        tok = tok[1:]
    if tok.startswith("~"):
        neg = not neg
        tok = tok[1:]
    if not tok.startswith("x"):
        raise ValueError(f"bad literal token: {tok!r}")
    return int(tok[1:]), neg


def _split_constraint_terms(tokens):
    """Given the token list of one constraint/objective body (no op/degree),
    yield (coeff, [(var, negated), ...]) terms. Supports products (NLC)."""
    terms = []
    i = 0
    n = len(tokens)
    while i < n:
        tok = tokens[i]
        # coefficient (may be signed integer)
        coeff = int(tok)
        i += 1
        lits = []
        while i < n and not _is_int(tokens[i]):
            var, neg = _parse_literal(tokens[i])
            lits.append((var, neg))
            i += 1
        if not lits:
            raise ValueError(f"coefficient {coeff} without literal")
        terms.append((coeff, lits))
    return terms


def _is_int(tok: str) -> bool:
    try:
        int(tok)
        return True
    except ValueError:
        return False


def parse_instance(path: Path) -> Instance:
    text = path.read_text(errors="replace")
    is_wbo = path.suffix == ".wbo"
    constraints = []
    objective = None
    n_vars = 0
    top_cost = None
    nonlinear = False

    # Constraints are terminated by ';'. Join lines then split on ';'.
    # Strip comment lines (starting with '*').
    body_lines = []
    for raw in text.splitlines():
        s = raw.strip()
        if not s or s.startswith("*"):
            # OPB header comment may carry '#variable= N #constraint= M'
            m = re.search(r"#variable=\s*(\d+)", s)
            if m:
                n_vars = max(n_vars, int(m.group(1)))
            continue
        if s.startswith("soft:"):
            # 'soft: <top> ;'
            m = re.fullmatch(r"soft:\s*(\d+)?\s*;?", s)
            if not m:
                raise ValueError(f"malformed soft-cost declaration: {s!r}")
            if m and m.group(1):
                top_cost = int(m.group(1))
            continue
        body_lines.append(s)

    blob = " ".join(body_lines)
    statements = [st.strip() for st in blob.split(";") if st.strip()]

    for st in statements:
        if st.startswith("min:") or st.startswith("max:"):
            sense = st[:3]
            tokens = _TOKEN_RE.findall(st[4:])
            terms = _split_constraint_terms(tokens) if tokens else []
            if sense == "max":
                terms = [(-c, l) for (c, l) in terms]
            objective = terms
            for _, lits in terms:
                if len(lits) > 1:
                    nonlinear = True
                for v, _ in lits:
                    n_vars = max(n_vars, v)
            continue

        # constraint: optional [weight] prefix (WBO), then terms, op, degree
        weight = None
        m = re.match(r"\[\s*([+-]?\d+)\s*\]\s*(.*)", st)
        if m:
            weight = int(m.group(1))
            st = m.group(2)
        tokens = _TOKEN_RE.findall(st)
        # find operator
        op_idx = None
        for idx, t in enumerate(tokens):
            if t in (">=", "<=", "="):
                op_idx = idx
                break
        if op_idx is None:
            raise ValueError(f"constraint has no supported relation: {st!r}")
        if op_idx + 2 != len(tokens):
            raise ValueError(f"malformed constraint degree: {st!r}")
        body = tokens[:op_idx]
        op = tokens[op_idx]
        degree = int(tokens[op_idx + 1])
        terms = _split_constraint_terms(body)
        for _, lits in terms:
            if len(lits) > 1:
                nonlinear = True
            for v, _ in lits:
                n_vars = max(n_vars, v)
        constraints.append(Constraint(terms=terms, op=op, degree=degree, weight=weight))

    return Instance(
        constraints=constraints,
        objective=objective,
        n_vars=n_vars,
        is_wbo=is_wbo,
        top_cost=top_cost,
        nonlinear=nonlinear,
    )


def _lit_val(lit, assign) -> int:
    var, neg = lit
    v = assign.get(var, False)
    return (0 if v else 1) if neg else (1 if v else 0)


def _term_val(coeff, lits, assign) -> int:
    prod = 1
    for lit in lits:
        prod *= _lit_val(lit, assign)
        if prod == 0:
            break
    return coeff * prod


def _constraint_holds(c: Constraint, assign) -> bool:
    lhs = sum(_term_val(coeff, lits, assign) for (coeff, lits) in c.terms)
    if c.op == ">=":
        return lhs >= c.degree
    if c.op == "<=":
        return lhs <= c.degree
    return lhs == c.degree


def check_solution(inst: Instance, assign: dict):
    """Return (ok: bool, computed_objective: Optional[int], reason: str).

    For WBO: hard constraints must hold; objective = sum of weights of violated
    soft constraints. For OPB: all constraints must hold; objective = min: value.
    """
    if inst.is_wbo:
        cost = 0
        for c in inst.constraints:
            holds = _constraint_holds(c, assign)
            if c.weight is None:
                if not holds:
                    return False, None, "hard constraint violated"
            else:
                if not holds:
                    cost += c.weight
        if inst.top_cost is not None and cost >= inst.top_cost:
            return False, cost, (
                f"soft cost {cost} reaches/exceeds top {inst.top_cost}"
            )
        return True, cost, ""
    # OPB
    for i, c in enumerate(inst.constraints):
        if not _constraint_holds(c, assign):
            return False, None, f"constraint #{i} violated"
    obj = None
    if inst.objective is not None:
        obj = sum(_term_val(coeff, lits, assign) for (coeff, lits) in inst.objective)
    return True, obj, ""


# ----------------------------------------------------------------------------
# Output parsing
# ----------------------------------------------------------------------------

def parse_solver_output(stdout: str):
    """Return (status, best_obj, assignment_tokens)."""
    status = None
    best_obj = None
    v_tokens = []
    for line in stdout.splitlines():
        if line.startswith("s "):
            status = line[2:].strip()
        elif line.startswith("o "):
            try:
                best_obj = int(line[2:].strip())
            except ValueError:
                pass
        elif line.startswith("v "):
            v_tokens.extend(line[2:].split())
    return status, best_obj, v_tokens


def assignment_from_tokens(tokens, n_vars):
    assign = {}
    for tok in tokens:
        tok = tok.strip()
        if not tok:
            continue
        try:
            var, neg = _parse_literal(tok)
        except ValueError:
            continue
        assign[var] = (not neg)
    # variables not mentioned default False
    return assign


def checked_assignment_from_tokens(tokens, n_vars):
    """Parse a competition model and reject malformed/conflicting literals."""
    assign = {}
    for token in tokens:
        try:
            variable, negated = _parse_literal(token.strip())
        except (ValueError, AttributeError):
            return None, f"invalid v-line token {token!r}"
        if variable < 1 or variable > n_vars:
            return None, f"v-line variable x{variable} outside 1..{n_vars}"
        value = not negated
        if variable in assign and assign[variable] != value:
            return None, f"conflicting v-line values for x{variable}"
        assign[variable] = value
    return assign, ""


# ----------------------------------------------------------------------------
# Category detection
# ----------------------------------------------------------------------------

def detect_category(path: Path, inst: Optional[Instance]) -> str:
    # Prefer directory hints (parent dirs only, not the filename)
    parts = [p.upper() for p in path.parent.parts]
    for p in parts:
        for cat in ("DEC-LIN", "OPT-LIN", "DEC-NLC", "OPT-NLC",
                    "PARTIAL-LIN", "SOFT-LIN", "WBO"):
            if cat in p:
                return cat
    # Derive from content
    if inst is None:
        return "?"
    if inst.is_wbo:
        has_hard = any(c.weight is None for c in inst.constraints)
        return "PARTIAL-LIN" if has_hard else "SOFT-LIN"
    has_obj = inst.objective is not None
    nl = inst.nonlinear
    if has_obj:
        return "OPT-NLC" if nl else "OPT-LIN"
    return "DEC-NLC" if nl else "DEC-LIN"


# ----------------------------------------------------------------------------
# Running
# ----------------------------------------------------------------------------

def physical_core_count() -> int:
    """Physical core count (not SMT threads); falls back to os.cpu_count()."""
    try:  # macOS
        out = subprocess.check_output(
            ["sysctl", "-n", "hw.physicalcpu"],
            text=True,
            stderr=subprocess.DEVNULL,
        )
        n = int(out.strip())
        if n >= 1:
            return n
    except Exception:  # noqa: BLE001
        pass
    try:  # Linux: count unique (physical id, core id) pairs
        cores = set()
        phys = None
        for line in Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("physical id"):
                phys = line.split(":", 1)[1].strip()
            elif line.startswith("core id"):
                cores.add((phys, line.split(":", 1)[1].strip()))
        if cores:
            return len(cores)
    except Exception:  # noqa: BLE001
        pass
    return os.cpu_count() or 1


def child_solver_env(jobs: int, nbcore_override: Optional[int],
                     memlimit_mb: int = 0):
    """Return a child environment with authoritative memory/core budgets."""
    if nbcore_override is not None:
        nbcore = max(1, nbcore_override)
    else:
        nbcore = max(1, physical_core_count() // jobs)
    if nbcore is None and not memlimit_mb:
        return None
    env = dict(os.environ)
    if nbcore is not None:
        env["NBCORE"] = str(nbcore)
    if memlimit_mb:
        env["MEMLIMIT"] = str(memlimit_mb)
    return env


@dataclasses.dataclass
class Result:
    instance: str
    category: str
    status: str          # SATISFIABLE/UNSATISFIABLE/OPTIMUM FOUND/UNKNOWN/UNSUPPORTED/TIMEOUT/MEMOUT/ERROR
    objective: Optional[int]
    wall_s: float
    exit_code: Optional[int]
    verified: Optional[bool]   # None if N/A (e.g. UNSAT/timeout), True/False for SAT/OPT
    wrong_answer: bool
    incomplete_model: bool = False  # v-line did not define every variable (DQ risk)
    note: str = ""
    # Enforced per-child memory envelope (MiB; 0 = none/unknown). Recorded per
    # result so cmd_score can detect comparisons across different envelopes —
    # a solved->TIMEOUT flip under a tighter envelope may be a memout artifact,
    # not a capability loss. Old JSONL files without the field load as 0.
    memlimit_mb: int = 0
    nbcore: int = 0
    timeout_sec: float = 0.0
    resource_envelope: Optional[dict] = None
    memout: bool = False
    timed_out: bool = False


VERIFY_LOCK = threading.Lock()


def parse_solver_output_stream(stream):
    """Extract answer-bearing lines from a seekable log in bounded RAM."""
    stream.flush()
    stream.seek(0)
    status = None
    best_obj = None
    v_tokens = []
    for line in stream:
        if line.startswith("s "):
            status = line[2:].strip()
        elif line.startswith("o "):
            try:
                best_obj = int(line[2:].strip())
            except ValueError:
                pass
        elif line.startswith("v "):
            v_tokens.extend(line[2:].split())
    return status, best_obj, v_tokens


def stream_tail(stream, limit: int = 200) -> str:
    stream.flush()
    stream.seek(0)
    tail = ""
    while True:
        chunk = stream.read(8192)
        if not chunk:
            return tail
        tail = (tail + chunk)[-limit:]


def kill_process_group(proc: subprocess.Popen) -> None:
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def executable_provenance(command: str) -> dict:
    candidate = Path(command)
    if not candidate.is_absolute():
        candidate = candidate.resolve()
    if not candidate.exists():
        found = shutil.which(command)
        if found:
            candidate = Path(found).resolve()
    try:
        stat = candidate.stat()
        digest = hashlib.sha256()
        with candidate.open("rb") as binary:
            for chunk in iter(lambda: binary.read(1024 * 1024), b""):
                digest.update(chunk)
        return {"path": str(candidate), "size": stat.st_size,
                "sha256": digest.hexdigest()}
    except OSError:
        return {"path": str(candidate), "size": None, "sha256": None}


def instance_set_digest(instances) -> str:
    digest = hashlib.sha256()
    for path in sorted((Path(value) for value in instances), key=str):
        try:
            stat = path.stat()
            identity = f"{path.resolve()}\0{stat.st_size}\0{stat.st_mtime_ns}\0"
        except OSError:
            identity = f"{path.resolve()}\0missing\0"
        digest.update(identity.encode("utf-8", errors="surrogateescape"))
    return digest.hexdigest()


def make_resource_envelope(args, instances, requested_jobs, plan) -> dict:
    return {
        "schema": "ay.benchmark-resource-envelope/v1",
        "requested_jobs": requested_jobs,
        "jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "memory_enforcement": "process-group rss_watchdog",
        "rss_grace_mb": 0,
        "solver_env": {"MEMLIMIT": str(plan.memlimit_mb),
                       "NBCORE": str(plan.nbcore)},
        "timeout_sec": args.timeout,
        "parent_wall_timeout_sec": args.timeout + 5.0,
        "timeout_enforcement": "process-group SIGKILL + reap",
        "capture": "temporary files (bounded parent RAM)",
        "checker": args.checker,
        "checker_jobs": 1,
        "checker_timeout_sec": 120 if args.checker == "ay" else None,
        "solver_command": ["<binary>", "pb", "solve", "<instance>",
                           "--timeout", str(int(args.timeout * 1000))],
        "executable": executable_provenance(args.bin),
        "harness": executable_provenance(__file__),
        "instance_count": len(instances),
        "instance_set_sha256": instance_set_digest(instances),
    }


def canonical_envelope(envelope: Optional[dict]) -> Optional[str]:
    if not isinstance(envelope, dict):
        return None
    return json.dumps(envelope, sort_keys=True, separators=(",", ":"))


def validate_result_envelopes(results):
    if not results:
        return None, "result file contains no records"
    values = {canonical_envelope(result.resource_envelope) for result in results}
    if None in values:
        return None, "legacy record(s) lack a complete resource envelope"
    if len(values) != 1:
        return None, f"records mix {len(values)} resource envelopes"
    envelope = results[0].resource_envelope
    required = {
        "schema", "requested_jobs", "jobs", "memlimit_mb_per_child",
        "nbcore_per_child", "headroom_mb", "memory_enforcement",
        "rss_grace_mb", "timeout_sec", "parent_wall_timeout_sec",
        "timeout_enforcement", "solver_env", "capture", "checker",
        "checker_jobs", "checker_timeout_sec", "solver_command",
        "executable", "harness", "instance_count", "instance_set_sha256",
    }
    missing = sorted(required - set(envelope))
    if missing:
        return None, f"resource envelope is incomplete (missing {missing})"
    if len(results) != envelope["instance_count"]:
        return None, (f"partial result set ({len(results)}/"
                      f"{envelope['instance_count']} records)")
    instances = [result.instance for result in results]
    if len(set(instances)) != len(instances):
        return None, "result file contains duplicate instance records"
    if instance_set_digest(instances) != envelope["instance_set_sha256"]:
        return None, "result instance set disagrees with its envelope"
    for field in ("executable", "harness"):
        provenance = envelope.get(field)
        if not isinstance(provenance, dict) or not provenance.get("sha256"):
            return None, f"resource envelope lacks {field} provenance"
    for result in results:
        if result.memlimit_mb != envelope["memlimit_mb_per_child"]:
            return None, "record memory field disagrees with its envelope"
        if result.nbcore != envelope["nbcore_per_child"]:
            return None, "record NBCORE field disagrees with its envelope"
        if result.timeout_sec != envelope["timeout_sec"]:
            return None, "record timeout field disagrees with its envelope"
    return envelope, None


def verify_solver_answer(bin_path, inst_path, status, best_obj, v_tokens,
                         checker, child_env, memlimit_mb):
    """Verify one answer while no other parent-side instance is retained."""
    try:
        inst = parse_instance(inst_path)
    except Exception as exc:  # noqa: BLE001
        return ("?", "ERROR", None, False, False,
                f"checker could not parse instance: {exc}"[:200])
    category = detect_category(inst_path, inst)
    if not v_tokens:
        return (category, status, False, True, False,
                "no v-line for SAT/OPTIMUM")
    assign, model_error = checked_assignment_from_tokens(v_tokens, inst.n_vars)
    if model_error:
        return category, status, False, True, False, model_error

    defined = set(assign)
    missing = inst.n_vars - len(defined & set(range(1, inst.n_vars + 1)))
    incomplete = inst.n_vars > 0 and missing > 0
    wrong = incomplete
    note = (f"v-line missing {missing}/{inst.n_vars} variables (DQ risk)"
            if incomplete else "")
    if checker == "ay":
        ok, computed_obj, reason = check_solution_via_ay(
            bin_path, inst_path, v_tokens, child_env, memlimit_mb,
        )
    else:
        ok, computed_obj, reason = check_solution(inst, assign)
    checker_failure = reason.startswith((
        "ay verify spawn failed",
        "ay verify exceeded memory envelope",
        "ay verify timed out",
    ))
    if checker_failure:
        return (category, "ERROR", None, wrong, incomplete,
                f"checker infrastructure failure: {reason}")
    if not ok:
        return (category, status, False, True, incomplete,
                f"INVALID ASSIGNMENT: {reason}")
    if computed_obj is not None and best_obj is None:
        return (category, status, True, True, incomplete,
                "objective-bearing answer has no o-line")
    if (best_obj is not None and computed_obj is not None and
            best_obj != computed_obj):
        return (category, status, True, True, incomplete,
                f"objective mismatch: reported o {best_obj}, "
                f"computed {computed_obj}")
    return category, status, True, wrong, incomplete, note


def run_one(bin_path: str, inst_path: Path, timeout_s: float, checker: str,
            grace_s: float = 5.0, env: Optional[dict] = None,
            memlimit_mb: int = 0, nbcore: int = 1,
            resource_envelope: Optional[dict] = None) -> Result:
    if memlimit_mb <= 0 or nbcore <= 0:
        raise ValueError("PB-COMP run requires positive memory and core budgets")
    category = detect_category(inst_path, None)

    cmd = [bin_path, "pb", "solve", str(inst_path),
           "--timeout", str(int(timeout_s * 1000))]
    start = time.monotonic()
    timed_out = False
    child_env = dict(os.environ, MEMLIMIT=str(memlimit_mb), NBCORE=str(nbcore))
    if env:
        child_env.update({k: v for k, v in env.items()
                          if k not in {"MEMLIMIT", "NBCORE"}})
    with tempfile.TemporaryFile(mode="w+t", encoding="utf-8",
                                errors="replace") as stdout:
        with tempfile.TemporaryFile(mode="w+t", encoding="utf-8",
                                    errors="replace") as stderr:
            try:
                proc = subprocess.Popen(
                    cmd,
                    stdin=subprocess.DEVNULL,
                    stdout=stdout,
                    stderr=stderr,
                    text=True,
                    start_new_session=True,
                    env=child_env,
                )
            except OSError as exc:
                return Result(
                    str(inst_path), category, "ERROR", None, 0.0, None,
                    None, False, note=f"spawn: {exc}"[:200],
                    memlimit_mb=memlimit_mb, nbcore=nbcore,
                    timeout_sec=timeout_s, resource_envelope=resource_envelope,
                )
            # The main `ay pb` path ignores MEMLIMIT, so exact process-group
            # RSS enforcement is mandatory even when the environment is set.
            guard = rss_watchdog(proc, memlimit_mb,
                                 label="pbcomp_harness.py", grace_mb=0)
            try:
                try:
                    rc = proc.wait(timeout=timeout_s + grace_s)
                except subprocess.TimeoutExpired:
                    timed_out = True
                    kill_process_group(proc)
                    rc = proc.wait()
            finally:
                kill_process_group(proc)
                if proc.poll() is None:
                    proc.wait()
                guard.stop()
            # A complete v-line can be large. Parse and verify under the same
            # lock, then discard it before another worker builds a model in
            # parent memory.
            verified = None
            wrong = False
            incomplete = False
            note = ""
            with VERIFY_LOCK:
                status, best_obj, v_tokens = parse_solver_output_stream(stdout)
                if guard.breached:
                    status = "MEMOUT"
                elif timed_out:
                    # The run exceeded the envelope even if it streamed an
                    # incumbent.
                    status = "TIMEOUT"
                if status in ("SATISFIABLE", "OPTIMUM FOUND"):
                    (category, status, verified, wrong, incomplete,
                     note) = verify_solver_answer(
                        bin_path,
                        inst_path,
                        status,
                        best_obj,
                        v_tokens,
                        checker,
                        child_env,
                        memlimit_mb,
                    )
                del v_tokens
            err = stream_tail(stderr)
    wall = time.monotonic() - start

    if status is None:
        status = "ERROR"
        note = (err or "").strip().splitlines()[-1] if err else "no s-line"
        return Result(str(inst_path), category, status, best_obj, wall, rc,
                      None, False, note=note[:200], memlimit_mb=memlimit_mb,
                      nbcore=nbcore, timeout_sec=timeout_s,
                      resource_envelope=resource_envelope,
                      memout=guard.breached, timed_out=timed_out)

    return Result(str(inst_path), category, status, best_obj, wall, rc,
                  verified, wrong, incomplete_model=incomplete, note=note,
                  memlimit_mb=memlimit_mb, nbcore=nbcore,
                  timeout_sec=timeout_s, resource_envelope=resource_envelope,
                  memout=guard.breached, timed_out=timed_out)


def check_solution_via_ay(bin_path, inst_path, v_tokens, env, memlimit_mb):
    """Run the optional AY checker under the same exact process envelope."""
    with tempfile.TemporaryFile(mode="w+t", encoding="utf-8") as solution:
        solution.write(" ".join(v_tokens))
        solution.seek(0)
        with tempfile.TemporaryFile(mode="w+t", encoding="utf-8",
                                    errors="replace") as stdout:
            with tempfile.TemporaryFile(mode="w+t", encoding="utf-8",
                                        errors="replace") as stderr:
                try:
                    proc = subprocess.Popen(
                        [bin_path, "pb", "verify", str(inst_path),
                         "--solution", "-"],
                        stdin=solution,
                        stdout=stdout,
                        stderr=stderr,
                        text=True,
                        start_new_session=True,
                        env=env,
                    )
                except OSError as exc:
                    return False, None, f"ay verify spawn failed: {exc}"
                guard = rss_watchdog(
                    proc,
                    memlimit_mb,
                    label="pbcomp_harness.py[verify]",
                    grace_mb=0,
                )
                timed_out = False
                try:
                    try:
                        returncode = proc.wait(timeout=120)
                    except subprocess.TimeoutExpired:
                        timed_out = True
                        kill_process_group(proc)
                        returncode = proc.wait()
                finally:
                    kill_process_group(proc)
                    if proc.poll() is None:
                        proc.wait()
                    guard.stop()
                if guard.breached:
                    return False, None, "ay verify exceeded memory envelope"
                if timed_out:
                    return False, None, "ay verify timed out"
                stdout.flush()
                stdout.seek(0)
                objective = None
                message = ""
                for line in stdout:
                    message = (message + line)[-200:]
                    match = re.search(r"objective[=:]\s*(-?\d+)", line)
                    if match:
                        objective = int(match.group(1))
                if returncode == 0:
                    return True, objective, ""
                return False, None, message.strip() or stream_tail(stderr) or \
                    "ay verify rejected"


# ----------------------------------------------------------------------------
# Baseline diff
# ----------------------------------------------------------------------------

def load_baseline(path: Path) -> dict:
    out = {}
    if not path or not path.exists():
        return out
    for line in path.read_text().splitlines():
        if line.startswith("CATEGORY") or not line.strip():
            continue
        f = line.split("|")
        if len(f) < 3:
            continue
        out[Path(f[1]).name] = {"category": f[0], "result": f[2]}
    return out


_SOLVED = {"SATISFIABLE", "UNSATISFIABLE", "OPTIMUM FOUND"}


def diff_baseline(results, baseline):
    regressions, improvements, conflicts = [], [], []
    for r in results:
        name = Path(r.instance).name
        b = baseline.get(name)
        if not b:
            continue
        was = b["result"]
        now = r.status
        was_solved = was in _SOLVED
        now_solved = now in _SOLVED
        # soundness conflict: SAT vs UNSAT disagreement
        if {was, now} == {"SATISFIABLE", "UNSATISFIABLE"} or \
           ("UNSAT" in was and now in ("SATISFIABLE", "OPTIMUM FOUND")) or \
           ("SAT" == was and now == "UNSATISFIABLE"):
            conflicts.append((name, was, now))
        if was_solved and not now_solved:
            regressions.append((name, was, now))
        elif not was_solved and now_solved:
            improvements.append((name, was, now))
    return regressions, improvements, conflicts


# ----------------------------------------------------------------------------
# Commands
# ----------------------------------------------------------------------------

def cmd_run(args):
    if args.jobs <= 0 or args.timeout <= 0 or args.limit < 0:
        print("jobs/timeout must be positive and limit nonnegative",
              file=sys.stderr)
        return 2
    bin_path = args.bin
    inst_dir = Path(args.instances)
    instances = sorted(
        [p for p in inst_dir.rglob("*") if p.suffix in (".opb", ".wbo")]
    )
    if args.limit:
        instances = instances[: args.limit]
    if not instances:
        print(f"no .opb/.wbo instances under {inst_dir}", file=sys.stderr)
        return 1
    # OOM guard (scripts/_oom_guard.py; 2026-06-19 / 2026-07-11 watchdog
    # panics): refuse to sweep concurrently with a cargo build (that exact
    # combination caused both panics; a warning was not enough), cap jobs to a
    # safe RAM budget, and give each child an enforced per-child envelope.
    try:
        warn_concurrent_build()
        requested_jobs = args.jobs
        plan = plan_solver_resources(args.jobs, label="pbcomp_harness.py")
    except RuntimeError as exc:
        if "REFUSING" not in str(exc):
            print(f"resource planning failed: {exc}", file=sys.stderr)
        return 2
    if plan.memlimit_mb <= 0 or plan.nbcore <= 0:
        print("resource planner returned an unenforceable envelope",
              file=sys.stderr)
        return 2
    if not hasattr(os, "killpg"):
        print("exact process-group RSS enforcement requires POSIX",
              file=sys.stderr)
        return 2
    args.jobs = plan.jobs
    env = child_solver_env(args.jobs, plan.nbcore,
                           memlimit_mb=plan.memlimit_mb)
    nbcore_desc = env["NBCORE"]
    memlimit_desc = env["MEMLIMIT"]
    resource_envelope = make_resource_envelope(
        args, instances, requested_jobs, plan,
    )
    if not resource_envelope["executable"].get("sha256"):
        print("solver executable unavailable: " +
              resource_envelope["executable"]["path"], file=sys.stderr)
        return 2
    # Envelope honesty: the MEMLIMIT env is enforced only by ay-pb-lineage
    # binaries; the default `ay pb solve` ignores it, so the rss watchdog in
    # run_one is what actually enforces the envelope for every child.
    print(f"running {len(instances)} instances, timeout={args.timeout}s, "
          f"requested_jobs={requested_jobs}, jobs={args.jobs}, "
          f"checker={args.checker}, NBCORE={nbcore_desc}, "
          f"MEMLIMIT(env)={memlimit_desc}, "
          f"rss-watchdog={plan.memlimit_mb or 'off'} MiB/child",
          file=sys.stderr)

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    Path(str(out_path) + ".resource-envelope.json").write_text(
        json.dumps(resource_envelope, indent=2) + "\n"
    )
    results = []
    done = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {
            ex.submit(run_one, bin_path, p, args.timeout, args.checker,
                      env=env, memlimit_mb=plan.memlimit_mb,
                      nbcore=plan.nbcore,
                      resource_envelope=resource_envelope): p
            for p in instances
        }
        with out_path.open("w") as fh:
            for fut in concurrent.futures.as_completed(futs):
                r = fut.result()
                results.append(r)
                fh.write(json.dumps(dataclasses.asdict(r)) + "\n")
                fh.flush()
                done += 1
                flag = ""
                if r.wrong_answer:
                    flag = "  <<< WRONG ANSWER"
                print(f"[{done}/{len(instances)}] {r.status:16} "
                      f"{r.wall_s:7.2f}s  {Path(r.instance).name}{flag}",
                      file=sys.stderr)

    baseline = load_baseline(Path(args.baseline)) if args.baseline else {}
    sound = report(results, baseline, args.timeout)
    print(f"\nwrote {out_path}", file=sys.stderr)
    return 0 if sound else 3


def cmd_score(args):
    results = []
    try:
        lines = Path(args.out).read_text().splitlines()
    except OSError as exc:
        print(f"REFUSING performance score: cannot read results: {exc}",
              file=sys.stderr)
        return 2
    for line in lines:
        if line.strip():
            try:
                d = json.loads(line)
                results.append(Result(**d))
            except (json.JSONDecodeError, TypeError) as exc:
                print(f"REFUSING performance score: malformed record: {exc}",
                      file=sys.stderr)
                return 2
    envelope, issue = validate_result_envelopes(results)
    if issue:
        print(f"REFUSING performance score: {issue}", file=sys.stderr)
        return 2
    if args.timeout is not None and args.timeout != envelope["timeout_sec"]:
        print("REFUSING performance score: --timeout disagrees with the "
              f"recorded envelope ({args.timeout} vs "
              f"{envelope['timeout_sec']})", file=sys.stderr)
        return 2
    baseline = load_baseline(Path(args.baseline)) if args.baseline else {}
    sound = report(results, baseline, envelope["timeout_sec"])
    return 0 if sound else 3


def report(results, baseline, timeout_s):
    cats = {}
    wrong = []
    incomplete = []
    for r in results:
        c = cats.setdefault(r.category, [])
        c.append(r)
        if r.wrong_answer:
            wrong.append(r)
        if getattr(r, "incomplete_model", False):
            incomplete.append(r)

    print("\n" + "=" * 72)
    print("PB-COMP HARNESS REPORT")
    print("=" * 72)
    total_solved = total = 0
    par2_sum = 0.0
    for cat in sorted(cats):
        rs = cats[cat]
        solved = [r for r in rs if r.status in _SOLVED and not r.wrong_answer]
        opt = [r for r in rs if r.status == "OPTIMUM FOUND" and not r.wrong_answer]
        sat = [r for r in rs if r.status == "SATISFIABLE" and not r.wrong_answer]
        unsat = [r for r in rs if r.status == "UNSATISFIABLE" and not r.wrong_answer]
        to = [r for r in rs if r.status == "TIMEOUT"]
        mo = [r for r in rs if r.status == "MEMOUT"]
        uns = [r for r in rs if r.status == "UNSUPPORTED"]
        err = [r for r in rs if r.status == "ERROR"]
        wr = [r for r in rs if r.wrong_answer]
        total_solved += len(solved)
        total += len(rs)
        # PAR-2: solved -> wall, else 2*timeout
        for r in rs:
            par2_sum += r.wall_s if (r.status in _SOLVED and not r.wrong_answer) else 2 * timeout_s
        print(f"\n{cat}:  {len(solved)}/{len(rs)} solved")
        print(f"    OPTIMUM {len(opt)}  SAT {len(sat)}  UNSAT {len(unsat)}  "
              f"TIMEOUT {len(to)}  MEMOUT {len(mo)}  UNSUPPORTED {len(uns)}  "
              f"ERROR {len(err)}  WRONG {len(wr)}")

    print("\n" + "-" * 72)
    print(f"OVERALL: {total_solved}/{total} solved "
          f"({100*total_solved/max(total,1):.1f}%)   PAR-2 = {par2_sum:.0f}")
    # Measurement-envelope record: results taken under different per-child
    # memory envelopes are not comparable (a TIMEOUT under a tight envelope
    # can be a memout artifact). 0 = no envelope (pre-guard runs).
    envelopes = {canonical_envelope(r.resource_envelope) for r in results}
    if len(envelopes) == 1 and next(iter(envelopes)) is not None:
        envelope = results[0].resource_envelope
        print("resource envelope: "
              f"jobs={envelope['jobs']} "
              f"MEMLIMIT={envelope['memlimit_mb_per_child']}MiB/child "
              f"NBCORE={envelope['nbcore_per_child']} "
              f"timeout={envelope['timeout_sec']}s grace=0MiB")
    else:
        print("*** PERFORMANCE RESULTS ARE NOT COMPARABLE: missing or mixed "
              "resource envelopes ***")
    if wrong:
        print(f"\n*** {len(wrong)} WRONG ANSWERS (each = category DQ) ***")
        for r in wrong:
            print(f"    {r.status:16} {Path(r.instance).name}: {r.note}")
    else:
        print("\nNo wrong answers detected. (soundness OK on this set)")
    if incomplete:
        print(f"\n*** {len(incomplete)} INCOMPLETE MODELS (v-line missing vars = DQ risk) ***")
        for r in incomplete[:20]:
            print(f"    {Path(r.instance).name}: {r.note}")

    baseline_conflicts = []
    if baseline:
        _reg, _imp, conf = diff_baseline(results, baseline)
        baseline_conflicts = conf
        print("\n" + "-" * 72)
        print("VS BASELINE: performance comparison REFUSED (legacy baseline "
              "CSV has no enforced resource envelope)")
        print(f"    soundness conflicts (resource-independent): {len(conf)}")
        for name, was, now in conf:
            print(f"    CONFLICT {name}: baseline={was} now={now}")
    return not wrong and not baseline_conflicts


def main():
    ap = argparse.ArgumentParser(description="PB-COMP benchmark harness")
    sub = ap.add_subparsers(dest="cmd", required=True)

    r = sub.add_parser("run")
    r.add_argument("--bin", default="target/release/ay")
    r.add_argument("--instances", required=True)
    r.add_argument("--timeout", type=float, default=30.0)
    r.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 4) // 2))
    r.add_argument("--checker", choices=["python", "ay"], default="python")
    r.add_argument("--baseline", default="")
    r.add_argument("--limit", type=int, default=0)
    r.add_argument("--out", default="evals/results/pbcomp/run.jsonl")
    r.set_defaults(func=cmd_run)

    s = sub.add_parser("score")
    s.add_argument("--out", required=True)
    s.add_argument("--baseline", default="")
    s.add_argument("--timeout", type=float, default=None,
                   help="optional assertion; must equal the recorded timeout")
    s.set_defaults(func=cmd_score)

    args = ap.parse_args()
    sys.exit(args.func(args))


if __name__ == "__main__":
    main()
