#!/usr/bin/env python3
# ay-script: ay-gurobi-w1-latency
"""Repeated, exact-checked AY/Gurobi process-wall closure for the W1 losses.

This is a deliberately narrow companion to :mod:`ay_gurobi_closure`.  The
general closure corpus answers solver coverage; this driver resolves the six
small ``sat_relu`` captures where both solvers reach the same expected verdict
but Gurobi historically had the lower process wall.  Three are feasible and
three are infeasible.  The measured unit is a fresh process, including model
parsing and route selection.

The driver is intentionally strict:

* one serial, RSS-watchdog-enforced ``_oom_guard`` plan for the whole run;
* a frozen copy of the production ``ay-milp`` binary;
* every ``AY_*``/``NY_*`` solver override scrubbed from both children;
* one thread, seed zero, deterministic AY, and zero Gurobi MIP gaps;
* the same byte-identical MPS input, whose zero objective is checked up front;
* rational AY witnesses checked literally, while rounded Gurobi ``.sol``
  points may exactly repair only continuous values with every integral value
  fixed, using the frozen production binary on feasible captures;
* every bounded UNSAT result backed by an independently VERIFIED
  ``sat-relu-rup`` infeasibility artifact, and every SAT result backed by
  VERIFIED primal and dual claims;
* every AY solve traced through exactly one conclusive bounded SAT/ReLU pass,
  with any route decline or ordinary-CDCL fallback rejected;
* an AB/BA solver order for each case and reversed/rotated corpus traversal;
* raw stdout/stderr, input/binary hashes, dirty-tree identity, host and resource
  envelope persisted beside the summary.

Exit status is 0 only if every common-capability observation is valid, AY is no
slower than Gurobi in every paired observation, and AY's separate certified
functionality gate passes.  It is 1 for a valid Gurobi speed advantage, 2 for
incomplete evidence, and 3 for invalid or contradictory evidence.
"""

from __future__ import annotations

import argparse
import collections
import enum
import gzip
import json
import math
import os
import platform
import random
import re
import statistics
import sys
import traceback
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
CASE_LIST_PATH = SCRIPT_DIR / "data" / "ay_gurobi_w1_latency_6.txt"
FULL_CENSUS_PATH = SCRIPT_DIR / "data" / "ay_gurobi_w1_census_46.txt"
FULL_CENSUS_SCHEMA = "ay-w1-46-h2h-v1"
FULL_CENSUS_COUNT = 46
FULL_CENSUS_SOURCE_SHA256 = (
    "cffbb070812b59607f40afd5a216a07e255fde5e5c3f3ba186e4fe6656fc72f7"
)
FULL_CENSUS_MANIFEST_SHA256 = (
    "21e2865ddbf49648511175a361aa5b84b8b0baaf9f4f0b3e045dcd1a4a1126d9"
)
DEFAULT_AY_BIN = REPO_ROOT / "target" / "release" / "ay-milp"
SCHEMA = "ay-gurobi-w1-latency-v2"
SOLVER_SEED = 0
SCHEDULE_SEED = 20260801
SAT_STATUSES = frozenset(("FEASIBLE", "OPTIMAL"))
EXPECTED_STATUSES = frozenset(("OPTIMAL", "INFEASIBLE"))
MAX_GUROBI_POINT_REPAIR_SEC = 10.0
SAT_RELU_TRACE_PREFIX = "AY_MILP_TRACE sat-relu-proof:"
SAT_RELU_FALLBACK_TRACE = f"{SAT_RELU_TRACE_PREFIX} fallback=ordinary-cdcl"
SAT_RELU_ATTEMPT_TRACE = re.compile(
    rf"^{re.escape(SAT_RELU_TRACE_PREFIX)} vars=(\d+) clauses=(\d+) "
    r"outcome=(SAT|UNSAT|DECLINE) reason=(.+?) wall=(\d+(?:\.\d+)?)s$"
)
AYC_EVIDENCE_LINE = re.compile(
    r"^evidence (primal|dual|infeasible) (SUCCINCT|REPLAY|NONE)(?: ([^ ]+))?$"
)
AYC_VERDICT_BLOCK_TOKENS = frozenset(
    (
        "witness",
        "farkas",
        "optcert",
        "tree",
        "sat-relu-rup",
        "parity-gf2",
        "network-design-infeasibility",
        "network-design-optimality",
        "single-machine-scheduling-optimality",
        "single-row-dp",
        "multi-row-bdd",
        "open-domain-dp",
        "open-domain-bdd",
        "open-domain-hybrid-pb-lp",
        "open-domain-hybrid-integer-lift",
        "hybrid-pb-lp",
        "hybrid-integer-lift",
        "replay",
    )
)


class PointEvidenceMode(str, enum.Enum):
    """How the exact checker must interpret a solver's point artifact."""

    AY_RATIONAL_LITERAL = "ay-rational-literal-exact"
    GUROBI_DECIMAL_REPAIR = "gurobi-decimal-continuous-repair"


sys.path.insert(0, str(SCRIPT_DIR))
import ay_gurobi_closure as closure  # noqa: E402
from _oom_guard import (  # noqa: E402
    physical_core_count,
    physical_ram_mb,
    plan_solver_resources,
    warn_concurrent_build,
)


def parse_sat_relu_route_trace_text(text: str) -> dict[str, Any]:
    """Parse every SAT/ReLU proof-route marker from complete solver stderr.

    Unknown lines are ignored, but any malformed line carrying the exact route
    prefix is retained and makes the evidence fail closed during evaluation.
    This prevents a changed trace format from silently looking like a clean
    route selection.
    """

    attempts: list[dict[str, Any]] = []
    malformed: list[dict[str, Any]] = []
    fallback_lines: list[int] = []
    for line_number, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if not line.startswith(SAT_RELU_TRACE_PREFIX):
            continue
        if line == SAT_RELU_FALLBACK_TRACE:
            fallback_lines.append(line_number)
            continue
        matched = SAT_RELU_ATTEMPT_TRACE.fullmatch(line)
        if matched is None:
            malformed.append({"line_number": line_number, "text": line})
            continue
        wall = float(matched.group(5))
        if not math.isfinite(wall):
            malformed.append({"line_number": line_number, "text": line})
            continue
        attempts.append(
            {
                "line_number": line_number,
                "variables": int(matched.group(1)),
                "clauses": int(matched.group(2)),
                "outcome": matched.group(3),
                "reason": matched.group(4),
                "wall_sec": wall,
            }
        )
    return {
        "attempts": attempts,
        "fallback_count": len(fallback_lines),
        "fallback_lines": fallback_lines,
        "malformed": malformed,
        "read_error": None,
    }


def read_sat_relu_route_trace(
    process: dict[str, Any], artifact_root: Path
) -> dict[str, Any]:
    """Read and parse the persisted, complete stderr artifact for one AY run."""

    stderr = process.get("stderr")
    if not isinstance(stderr, dict) or stderr.get("exists") is not True:
        return {
            "attempts": [],
            "fallback_count": 0,
            "fallback_lines": [],
            "malformed": [],
            "read_error": "solver process has no persisted stderr artifact",
        }
    try:
        path = (artifact_root / stderr["path"]).resolve(strict=True)
        root = artifact_root.resolve(strict=True)
        path.relative_to(root)
        data = path.read_bytes()
        if len(data) != stderr.get("size_bytes"):
            raise ValueError("stderr artifact size changed before trace parsing")
        if closure.sha256_bytes(data) != stderr.get("sha256"):
            raise ValueError("stderr artifact digest changed before trace parsing")
        parsed = parse_sat_relu_route_trace_text(data.decode("utf-8", errors="strict"))
    except (KeyError, OSError, UnicodeError, ValueError) as error:
        return {
            "attempts": [],
            "fallback_count": 0,
            "fallback_lines": [],
            "malformed": [],
            "read_error": f"{type(error).__name__}: {error}",
        }
    parsed["stderr"] = stderr
    return parsed


def traced_ay_environment(
    env: dict[str, str], env_posture: dict[str, Any]
) -> tuple[dict[str, str], dict[str, Any]]:
    """Enable route telemetry only after the shared solver-env scrub."""

    traced = dict(env)
    traced["AY_MILP_TRACE"] = "1"
    posture = dict(env_posture)
    posture["enabled_solver_environment"] = {"AY_MILP_TRACE": "1"}
    posture["environment_sha256"] = closure.sha256_text(
        "".join(f"{key}={traced[key]}\0" for key in sorted(traced))
    )
    return traced, posture


def load_case_expectations(path: Path = CASE_LIST_PATH) -> dict[str, str]:
    """Load unique MPS stems and frozen expected verdicts."""

    cases: dict[str, str] = {}
    for line_number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split()
        if len(fields) != 2 or fields[1] not in EXPECTED_STATUSES:
            raise ValueError(
                f"{path}:{line_number}: expected '<MPS stem> OPTIMAL|INFEASIBLE'"
            )
        name, expected = fields
        if name in cases:
            raise ValueError(f"duplicate W1 latency case: {name}")
        cases[name] = expected
    if path == CASE_LIST_PATH and len(cases) != 6:
        raise ValueError(f"frozen W1 latency list has {len(cases)} cases, expected 6")
    return cases


def load_case_names(path: Path = CASE_LIST_PATH) -> list[str]:
    """Compatibility helper returning the ordered frozen MPS stems."""

    names = list(load_case_expectations(path))
    duplicates = sorted(
        name for name, count in collections.Counter(names).items() if count > 1
    )
    if duplicates:
        raise ValueError(f"duplicate W1 latency cases: {', '.join(duplicates)}")
    return names


def classify_case_set(
    path: Path,
    expectations: dict[str, str],
    *,
    full_census_path: Path = FULL_CENSUS_PATH,
    full_census_schema: str = FULL_CENSUS_SCHEMA,
    full_census_count: int = FULL_CENSUS_COUNT,
    full_census_source_sha256: str = FULL_CENSUS_SOURCE_SHA256,
    full_census_manifest_sha256: str = FULL_CENSUS_MANIFEST_SHA256,
) -> dict[str, Any]:
    """Name the selected corpus without letting custom input claim census status."""

    resolved = path.resolve(strict=True)
    if resolved != full_census_path.resolve():
        return {
            "kind": "focused-w1-losses" if resolved == CASE_LIST_PATH.resolve() else "custom",
            "full_census": False,
        }

    data = resolved.read_bytes()
    digest = closure.sha256_bytes(data)
    text = data.decode("utf-8", errors="strict")
    comments = [line.strip() for line in text.splitlines() if line.startswith("#")]
    schema_line = f"# {full_census_schema}"
    source_line = f"# Source SHA-256: {full_census_source_sha256}"
    problems: list[str] = []
    if not comments or comments[0] != schema_line:
        problems.append(f"schema is not {full_census_schema}")
    if comments.count(source_line) != 1:
        problems.append("source SHA-256 metadata is missing or duplicated")
    if len(expectations) != full_census_count:
        problems.append(
            f"case count is {len(expectations)}, expected {full_census_count}"
        )
    if digest != full_census_manifest_sha256:
        problems.append(
            f"manifest SHA-256 is {digest}, expected {full_census_manifest_sha256}"
        )
    if problems:
        raise ValueError("invalid frozen W1 full-census manifest: " + "; ".join(problems))
    return {
        "kind": "full-w1-census",
        "full_census": True,
        "schema": full_census_schema,
        "count": full_census_count,
        "source_sha256": full_census_source_sha256,
        "manifest_sha256": full_census_manifest_sha256,
    }


def open_mps_text(path: Path):
    """Open plain or gzip MPS text without changing the measured input."""

    opener = gzip.open if path.name.endswith(".gz") else open
    return opener(path, "rt", encoding="utf-8", errors="strict")


def objective_nonzeros(path: Path) -> int:
    """Return the exact count of nonzero MPS objective coefficients.

    The W1 comparison is feasibility-only.  Checking the objective from the
    shared bytes prevents a renamed optimization instance from silently
    entering this specialized latency gate.
    """

    section = None
    objective_row = None
    coefficients: dict[str, Fraction] = collections.defaultdict(Fraction)
    with open_mps_text(path) as handle:
        for line_number, raw in enumerate(handle, 1):
            if not raw.strip() or raw.startswith("*"):
                continue
            fields = raw.split()
            if not raw.startswith((" ", "\t")):
                section = fields[0].upper()
                if section == "ENDATA":
                    break
                continue
            if section == "ROWS":
                if len(fields) < 2:
                    raise ValueError(f"{path}:{line_number}: malformed ROWS entry")
                if fields[0].upper() == "N" and objective_row is None:
                    objective_row = fields[1]
            elif section == "COLUMNS":
                if any(field.upper() == "'MARKER'" for field in fields):
                    continue
                if len(fields) < 3 or len(fields) % 2 == 0:
                    raise ValueError(f"{path}:{line_number}: malformed COLUMNS entry")
                column = fields[0]
                for index in range(1, len(fields), 2):
                    if fields[index] == objective_row:
                        try:
                            coefficients[column] += Fraction(fields[index + 1])
                        except (ValueError, ZeroDivisionError) as error:
                            raise ValueError(
                                f"{path}:{line_number}: invalid objective number "
                                f"{fields[index + 1]!r}"
                            ) from error
    if objective_row is None:
        raise ValueError(f"{path}: no objective N row")
    return sum(value != 0 for value in coefficients.values())


def discover_models(mps_dir: Path, names: list[str]) -> list[dict[str, Any]]:
    """Resolve exactly one immutable MPS file for every selected stem."""

    records = []
    for name in names:
        candidates = [
            candidate
            for candidate in (mps_dir / f"{name}.mps", mps_dir / f"{name}.mps.gz")
            if candidate.is_file()
        ]
        if len(candidates) != 1:
            raise ValueError(
                f"{name}: expected exactly one .mps or .mps.gz in {mps_dir}, "
                f"found {len(candidates)}"
            )
        path = candidates[0].resolve(strict=True)
        nonzeros = objective_nonzeros(path)
        if nonzeros:
            raise ValueError(f"{name}: W1 latency gate requires objective=0, found {nonzeros}")
        identity = closure.file_identity(path)
        identity.update(
            {
                "name": name,
                "objective_nonzeros": nonzeros,
                "sense": closure.mps_sense(path),
            }
        )
        records.append(identity)
    return records


def build_ay_command(
    ay_binary: Path,
    model: Path,
    timeout: float,
    witness: Path,
    certificate: Path,
    memory_budget_bytes: int,
    require: str = "witness",
) -> list[str]:
    """Production AY command whose process wall is the measured quantity."""

    if (
        isinstance(memory_budget_bytes, bool)
        or not isinstance(memory_budget_bytes, int)
        or memory_budget_bytes <= 0
    ):
        raise ValueError("AY solve needs a positive integer logical memory budget")
    return [
        str(ay_binary),
        "solve",
        str(model),
        "--time-limit",
        str(timeout),
        "--threads",
        "1",
        "--seed",
        str(SOLVER_SEED),
        "--deterministic",
        "--memory-budget",
        str(memory_budget_bytes),
        "--require",
        require,
        "--emit-cert",
        str(certificate),
        "--emit-witness",
        str(witness),
        "--witness-format",
        "rational",
        "--format",
        "json",
    ]


def run_ay(
    ay_binary: Path,
    model: Path,
    timeout: float,
    hard_timeout: float,
    plan: Any,
    env: dict[str, str],
    env_posture: dict[str, Any],
    run_dir: Path,
    artifact_root: Path,
    require: str = "witness",
) -> dict[str, Any]:
    witness = run_dir / "result.sol"
    certificate = run_dir / "result.ayc"
    memory_budget_bytes = plan.memlimit_mb * 1024 * 1024
    command = build_ay_command(
        ay_binary,
        model,
        timeout,
        witness,
        certificate,
        memory_budget_bytes,
        require=require,
    )
    ay_env, ay_env_posture = traced_ay_environment(env, env_posture)
    process = closure.run_guarded_capture(
        command,
        memlimit_mb=plan.memlimit_mb,
        timeout_sec=hard_timeout,
        label="ay_gurobi_w1_latency.py[ay]",
        env=ay_env,
        env_posture=ay_env_posture,
        artifact_dir=run_dir,
        artifact_root=artifact_root,
    )
    verdict, parse_error = closure.parse_process_json(process, artifact_root)
    return {
        "process": process,
        "verdict": verdict,
        "parse_error": parse_error,
        "sat_relu_route_trace": read_sat_relu_route_trace(process, artifact_root),
        "witness": closure.artifact_identity(witness, artifact_root),
        "certificate": closure.artifact_identity(certificate, artifact_root),
        "memory_budget_bytes": memory_budget_bytes,
        "require": require,
    }


def build_point_check_command(
    ay_binary: Path,
    model: Path,
    point: Path,
    evidence_mode: PointEvidenceMode,
    *,
    repair_time_limit: float | None = None,
    memory_budget_bytes: int | None = None,
) -> list[str]:
    """Build a source-aware exact point-check command.

    AY emits rational values, so accepting them means checking those literal
    values.  Gurobi emits rounded decimal values; its mode may reconstruct only
    the continuous completion while holding every supplied integral value
    fixed.  Requiring the repair resources here prevents an unbounded nested
    solve from being introduced accidentally.
    """

    command = [
        str(ay_binary),
        "check-point",
        "--model",
        str(model),
        "--point",
        str(point),
    ]
    if evidence_mode is PointEvidenceMode.AY_RATIONAL_LITERAL:
        if repair_time_limit is not None or memory_budget_bytes is not None:
            raise ValueError("literal AY point checks cannot request continuous repair")
        return command
    if evidence_mode is not PointEvidenceMode.GUROBI_DECIMAL_REPAIR:
        raise ValueError(f"unsupported point evidence mode: {evidence_mode!r}")
    if (
        repair_time_limit is None
        or not math.isfinite(repair_time_limit)
        or repair_time_limit <= 0
    ):
        raise ValueError("Gurobi point repair needs a positive finite time limit")
    if (
        memory_budget_bytes is None
        or isinstance(memory_budget_bytes, bool)
        or not isinstance(memory_budget_bytes, int)
        or memory_budget_bytes <= 0
    ):
        raise ValueError("Gurobi point repair needs a positive integer memory budget")
    return [
        *command,
        "--repair-continuous",
        "--repair-time-limit",
        str(repair_time_limit),
        "--memory-budget",
        str(memory_budget_bytes),
    ]


def check_point(
    ay_binary: Path,
    model: Path,
    point_identity: dict[str, Any],
    evidence_mode: PointEvidenceMode,
    plan: Any,
    timeout: float,
    env: dict[str, str],
    env_posture: dict[str, Any],
    run_dir: Path,
    artifact_root: Path,
) -> dict[str, Any]:
    point = artifact_root / point_identity["path"]
    if not point.is_file():
        skipped = closure.skipped_checker("solver did not emit a point")
        skipped["evidence_mode"] = evidence_mode.value
        return skipped
    repair_options: dict[str, float | int] = {}
    if evidence_mode is PointEvidenceMode.GUROBI_DECIMAL_REPAIR:
        repair_options = {
            "repair_time_limit": min(timeout, MAX_GUROBI_POINT_REPAIR_SEC),
            "memory_budget_bytes": plan.memlimit_mb * 1024 * 1024,
        }
    checked = closure.run_checker(
        build_point_check_command(
            ay_binary,
            model,
            point,
            evidence_mode,
            **repair_options,
        ),
        parser=closure.parse_point_output,
        plan=plan,
        timeout=timeout,
        env=env,
        env_posture=env_posture,
        artifact_dir=run_dir,
        artifact_root=artifact_root,
    )
    checked["evidence_mode"] = evidence_mode.value
    return checked


def check_certificate(
    ay_binary: Path,
    model: Path,
    certificate_identity: dict[str, Any],
    plan: Any,
    timeout: float,
    env: dict[str, str],
    env_posture: dict[str, Any],
    run_dir: Path,
    artifact_root: Path,
) -> dict[str, Any]:
    certificate = artifact_root / certificate_identity["path"]
    if not certificate.is_file():
        return closure.skipped_checker("AY did not emit a certificate")
    return closure.run_checker(
        [str(ay_binary), "verify", "--model", str(model), "--cert", str(certificate)],
        parser=closure.parse_verify_output,
        plan=plan,
        timeout=timeout,
        env=env,
        env_posture=env_posture,
        artifact_dir=run_dir,
        artifact_root=artifact_root,
    )


def inspect_certificate_artifact(
    certificate_identity: dict[str, Any], artifact_root: Path
) -> dict[str, Any]:
    """Read one immutable AYC and census its verdict-bearing source tokens.

    The certificate checker establishes semantics.  This independent census
    establishes route ownership: a different verified proof mechanism must not
    be credited to the bounded SAT/ReLU route.  The persisted identity is
    rechecked before any source or block token is trusted.
    """

    profile: dict[str, Any] = {
        "read_error": None,
        "evidence": [],
        "malformed_evidence": [],
        "block_counts": {token: 0 for token in sorted(AYC_VERDICT_BLOCK_TOKENS)},
        "witness_block_count": 0,
        "optcert_block_count": 0,
        "sat_relu_rup_block_count": 0,
        "sat_relu_replay_block_count": 0,
    }
    try:
        if (
            not isinstance(certificate_identity, dict)
            or certificate_identity.get("exists") is not True
        ):
            raise ValueError("AY did not persist a certificate artifact")
        relative = certificate_identity.get("path")
        if not isinstance(relative, str):
            raise ValueError("certificate artifact has no relative path")
        root = artifact_root.resolve(strict=True)
        certificate = (root / relative).resolve(strict=True)
        certificate.relative_to(root)
        data = certificate.read_bytes()
        if len(data) != certificate_identity.get("size_bytes"):
            raise ValueError("certificate artifact size changed before source inspection")
        if closure.sha256_bytes(data) != certificate_identity.get("sha256"):
            raise ValueError("certificate artifact digest changed before source inspection")
        text = data.decode("utf-8", errors="strict")
    except (KeyError, OSError, UnicodeError, ValueError) as error:
        profile["read_error"] = f"{type(error).__name__}: {error}"
        return profile

    for line_number, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if line.startswith("evidence "):
            matched = AYC_EVIDENCE_LINE.fullmatch(line)
            if matched is None:
                profile["malformed_evidence"].append(
                    {"line_number": line_number, "text": line}
                )
            else:
                profile["evidence"].append(
                    {
                        "line_number": line_number,
                        "claim": matched.group(1),
                        "kind": matched.group(2),
                        "source": matched.group(3),
                    }
                )
        token = line.split(maxsplit=1)[0] if line else ""
        if token in AYC_VERDICT_BLOCK_TOKENS:
            profile["block_counts"][token] += 1
    profile["witness_block_count"] = profile["block_counts"]["witness"]
    profile["optcert_block_count"] = profile["block_counts"]["optcert"]
    profile["sat_relu_rup_block_count"] = profile["block_counts"]["sat-relu-rup"]
    profile["sat_relu_replay_block_count"] = profile["block_counts"]["replay"]
    profile["identity"] = certificate_identity
    return profile


def evidence_source_count(
    profile: dict[str, Any], claim: str, kind: str, source: str
) -> int:
    evidence = profile.get("evidence")
    if not isinstance(evidence, list):
        return 0
    return sum(
        isinstance(record, dict)
        and record.get("claim") == claim
        and record.get("kind") == kind
        and record.get("source") == source
        for record in evidence
    )


def certificate_artifact_shape_is_exact(
    profile: dict[str, Any],
    expected_evidence: tuple[tuple[str, str, str], ...],
    expected_blocks: dict[str, int],
) -> bool:
    """Require the complete evidence-record and verdict-block multisets."""

    evidence = profile.get("evidence")
    block_counts = profile.get("block_counts")
    if not isinstance(evidence, list) or not isinstance(block_counts, dict):
        return False
    observed_evidence: collections.Counter[tuple[str, str, str | None]] = (
        collections.Counter()
    )
    for record in evidence:
        if not isinstance(record, dict):
            return False
        observed_evidence[
            (record.get("claim"), record.get("kind"), record.get("source"))
        ] += 1
    observed_blocks: dict[str, int] = {}
    for token, count in block_counts.items():
        if (
            token not in AYC_VERDICT_BLOCK_TOKENS
            or isinstance(count, bool)
            or not isinstance(count, int)
            or count < 0
        ):
            return False
        if count:
            observed_blocks[token] = count
    return (
        observed_evidence == collections.Counter(expected_evidence)
        and observed_blocks == expected_blocks
    )


def certificate_replay_present(profile: dict[str, Any]) -> bool:
    block_counts = profile.get("block_counts")
    replay_blocks = block_counts.get("replay", 0) if isinstance(block_counts, dict) else 0
    return (
        evidence_source_count(
            profile, "infeasible", "REPLAY", "sat-relu-cnf-unsat"
        )
        > 0
        or replay_blocks != 0
    )


def sat_relu_replay_marker(
    certificate_identity: dict[str, Any], artifact_root: Path
) -> bool:
    """Recognize either half of the forbidden replay-only SAT/ReLU evidence."""

    profile = inspect_certificate_artifact(certificate_identity, artifact_root)
    return certificate_replay_present(profile)


def certificate_checker_consistent(check: dict[str, Any]) -> bool:
    parsed = check.get("parsed") or {}
    process = check.get("process")
    expected_exit = {
        "VERIFIED": 0,
        "UNVERIFIED": 10,
        "PARTIAL": 11,
        "REFUTED": 20,
        "MISMATCH": 30,
    }.get(parsed.get("status"))
    return (
        process is not None
        and expected_exit is not None
        and process.get("launch_error") is None
        and not process.get("timed_out")
        and not process.get("memout")
        and not process.get("cancelled")
        and not process.get("stdout_truncated")
        and not process.get("stderr_truncated")
        and process.get("returncode") == expected_exit
    )


def evaluate_sat_relu_route_trace(
    result: dict[str, Any], expected_status: str
) -> dict[str, Any]:
    """Require exactly one conclusive bounded route attempt and no fallback."""

    issues: list[str] = []
    expected_outcome = "SAT" if expected_status == "OPTIMAL" else "UNSAT"
    trace = result.get("sat_relu_route_trace")
    if not isinstance(trace, dict):
        trace = {}
        issues.append("AY SAT/ReLU route trace is missing")

    read_error = trace.get("read_error")
    if read_error:
        issues.append(f"AY SAT/ReLU route trace could not be read: {read_error}")

    attempts = trace.get("attempts", [])
    if not isinstance(attempts, list):
        attempts = []
        issues.append("AY SAT/ReLU route trace attempts are malformed")
    outcomes = [
        attempt.get("outcome")
        for attempt in attempts
        if isinstance(attempt, dict)
    ]
    if len(outcomes) != len(attempts) or any(
        outcome not in ("SAT", "UNSAT", "DECLINE") for outcome in outcomes
    ):
        issues.append("AY SAT/ReLU route trace contains an invalid outcome")

    malformed = trace.get("malformed", [])
    if not isinstance(malformed, list):
        malformed = []
        issues.append("AY SAT/ReLU malformed-trace census is invalid")
    if malformed:
        issues.append(
            f"AY emitted {len(malformed)} malformed SAT/ReLU route trace line(s)"
        )

    fallback_count = trace.get("fallback_count", 0)
    if (
        isinstance(fallback_count, bool)
        or not isinstance(fallback_count, int)
        or fallback_count < 0
    ):
        fallback_count = 0
        issues.append("AY SAT/ReLU fallback census is invalid")
    if fallback_count:
        issues.append(
            f"AY SAT/ReLU route used ordinary-CDCL fallback {fallback_count} time(s)"
        )

    decline_count = sum(outcome == "DECLINE" for outcome in outcomes)
    if decline_count:
        issues.append(f"AY SAT/ReLU bounded route declined {decline_count} time(s)")
    if len(attempts) != 1:
        issues.append(
            "AY SAT/ReLU route must emit exactly one bounded attempt; "
            f"observed {len(attempts)}"
        )
    elif outcomes and outcomes[0] != expected_outcome:
        issues.append(
            f"AY SAT/ReLU route outcome {outcomes[0]} does not match "
            f"expected {expected_outcome}"
        )

    return {
        "accepted": not issues,
        "expected_outcome": expected_outcome,
        "attempt_count": len(attempts),
        "outcomes": outcomes,
        "decline_count": decline_count,
        "fallback_count": fallback_count,
        "malformed_count": len(malformed),
        "read_error": read_error,
        "issues": issues,
    }


def evaluate_expected(
    solver: str,
    result: dict[str, Any],
    expected_status: str,
    *,
    require_verified_infeasible: bool = False,
) -> dict[str, Any]:
    """Validate one result against the frozen mixed SAT/UNSAT W1 reference."""

    invalid: list[str] = []
    wrong: list[str] = []
    process = result["process"]
    if not closure.process_is_clean(process):
        invalid.append("solver process did not exit cleanly inside its envelope")
    if result.get("parse_error"):
        invalid.append(f"unparseable solver result: {result['parse_error']}")
    verdict = result.get("verdict") or {}
    status = verdict.get("status")
    if not isinstance(status, str):
        invalid.append("solver result has no status")
        status = "HARNESS_ERROR"
    if status == "CHILD_ERROR":
        invalid.append(
            f"Gurobi child failed at {verdict.get('stage')}: {verdict.get('error')}"
        )
    expected_sat = expected_status == "OPTIMAL"
    status_matches = status in SAT_STATUSES if expected_sat else status == "INFEASIBLE"
    if status in SAT_STATUSES | {"INFEASIBLE", "UNBOUNDED"} and not status_matches:
        wrong.append(f"{status} contradicts frozen W1 reference {expected_status}")

    sat_relu_route = None
    if solver == "ay":
        sat_relu_route = evaluate_sat_relu_route_trace(result, expected_status)
        invalid.extend(sat_relu_route["issues"])

    wall = closure.numeric(process.get("wall_sec"))
    if wall is None or wall < 0:
        invalid.append("solver process has no finite non-negative wall time")

    point_check = result.get("point_check") or {}
    point_process = point_check.get("process")
    point_parsed = point_check.get("parsed") or {}
    point_verified = (
        expected_sat
        and status in SAT_STATUSES
        and point_process is not None
        and closure.process_is_clean(point_process)
        and point_parsed.get("status") == "FEASIBLE"
    )
    if expected_sat and status in SAT_STATUSES and not point_verified:
        invalid.append("SAT result did not pass the exact rational point checker")

    reported_key = "value" if solver == "ay" else "objective"
    reported = closure.numeric(verdict.get(reported_key))
    checked = closure.numeric(point_parsed.get("objective"))
    if expected_sat and point_verified and (
        reported is None
        or checked is None
        or not closure.close_number(reported, checked)
        or not closure.close_number(checked, 0.0)
    ):
        invalid.append(
            f"zero-objective mismatch: reported={verdict.get(reported_key)!r}, "
            f"checked={point_parsed.get('objective')!r}"
        )

    certificate_status = None
    certificate_claims: dict[str, str] = {}
    certificate_artifact: dict[str, Any] = {}
    replay_marker = False
    evidence_mode = "gurobi-status-only" if not expected_sat else "exact-point"
    if solver == "ay":
        certificate_check = result.get("certificate_check") or {}
        parsed = certificate_check.get("parsed") or {}
        certificate_status = parsed.get("status")
        certificate_claims = parsed.get("claims") or {}
        raw_artifact = result.get("certificate_artifact")
        if isinstance(raw_artifact, dict):
            certificate_artifact = raw_artifact
        else:
            invalid.append("AY certificate artifact source census is missing")
        artifact_read_error = certificate_artifact.get("read_error")
        if artifact_read_error:
            invalid.append(
                "AY certificate artifact could not be inspected: "
                f"{artifact_read_error}"
            )
        malformed_evidence = certificate_artifact.get("malformed_evidence", [])
        if not isinstance(malformed_evidence, list):
            invalid.append("AY certificate artifact evidence census is malformed")
            malformed_evidence = []
        if malformed_evidence:
            invalid.append(
                "AY certificate artifact contains "
                f"{len(malformed_evidence)} malformed evidence record(s)"
            )
        replay_marker = certificate_replay_present(certificate_artifact)
        if not certificate_checker_consistent(certificate_check):
            invalid.append("AY certificate checker process/status is inconsistent")
        if certificate_status in ("REFUTED", "MISMATCH"):
            invalid.append(f"AY certificate checker returned {certificate_status}")
        verified_claims = set(
            certificate_claims.get("verified", "-").split(",")
        ) - {"", "-"}
        if expected_sat and status in SAT_STATUSES:
            missing = {"primal", "dual"} - verified_claims
            source_owned = certificate_artifact_shape_is_exact(
                certificate_artifact,
                (
                    ("primal", "SUCCINCT", "witness"),
                    ("dual", "SUCCINCT", "optcert"),
                ),
                {"witness": 1, "optcert": 1},
            )
            if not source_owned:
                invalid.append(
                    "AY SAT certificate does not contain exactly the witness+optcert "
                    "evidence records and typed blocks"
                )
            if replay_marker:
                invalid.append("AY SAT certificate contains forbidden replay evidence")
            if (
                certificate_status == "VERIFIED"
                and not missing
                and source_owned
                and not replay_marker
            ):
                evidence_mode = "verified-witness-optcert"
            else:
                invalid.append(
                    "AY SAT lacks a VERIFIED certificate with primal and dual claims"
                )
                evidence_mode = "missing-verified-witness-optcert"
        elif not expected_sat and status == "INFEASIBLE":
            source_owned = certificate_artifact_shape_is_exact(
                certificate_artifact,
                (("infeasible", "SUCCINCT", "sat-relu-rup"),),
                {"sat-relu-rup": 1},
            )
            if not source_owned:
                invalid.append(
                    "AY UNSAT certificate does not contain exactly the sat-relu-rup "
                    "evidence record and typed block"
                )
            if replay_marker:
                invalid.append(
                    "AY UNSAT certificate contains forbidden "
                    "sat-relu-cnf-unsat replay evidence"
                )
            if (
                certificate_status == "VERIFIED"
                and "infeasible" in verified_claims
                and source_owned
                and not replay_marker
            ):
                evidence_mode = "verified-sat-relu-rup"
            else:
                lane = "certified" if require_verified_infeasible else "common"
                invalid.append(f"{lane} lane lacks a VERIFIED infeasible claim")
                evidence_mode = "missing-verified-sat-relu-rup"

    if solver == "gurobi" and status not in ("CHILD_ERROR", "HARNESS_ERROR"):
        posture = verdict.get("posture") or {}
        expected = {
            "threads": 1,
            "seed": SOLVER_SEED,
            "mip_gap": 0.0,
            "mip_gap_abs": 0.0,
        }
        for key, value in expected.items():
            if posture.get(key) != value:
                invalid.append(
                    f"Gurobi posture {key}={posture.get(key)!r}, expected {value!r}"
                )

    return {
        "status": status,
        "expected_status": expected_status,
        "valid": not invalid,
        "correct": not wrong,
        "solved": (
            status_matches
            and (point_verified if expected_sat else True)
            and not invalid
            and not wrong
        ),
        "point_verified": point_verified,
        "checked_objective": point_parsed.get("objective"),
        "certificate_status": certificate_status,
        "certificate_claims": certificate_claims,
        "certificate_artifact": certificate_artifact,
        "sat_relu_replay_marker": replay_marker,
        "sat_relu_route": sat_relu_route,
        "evidence_mode": evidence_mode,
        "outer_wall_sec": wall,
        "solver_runtime_sec": closure.numeric(
            verdict.get("runtime" if solver == "ay" else "solver_runtime_sec")
        ),
        "invalid_issues": invalid,
        "wrong_issues": wrong,
    }


def compare_pair(ay: dict[str, Any], gurobi: dict[str, Any]) -> dict[str, Any]:
    """Classify one order-controlled process pair, without a noise loophole."""

    if not ay["valid"] or not ay["correct"] or not gurobi["valid"] or not gurobi["correct"]:
        return {"classification": "INCONCLUSIVE_INVALID", "ay_over_gurobi": None}
    if ay["solved"] and not gurobi["solved"]:
        return {"classification": "AY_ONLY", "ay_over_gurobi": None}
    if gurobi["solved"] and not ay["solved"]:
        return {"classification": "GUROBI_ONLY", "ay_over_gurobi": None}
    if not ay["solved"] and not gurobi["solved"]:
        return {"classification": "NEITHER", "ay_over_gurobi": None}
    ratio = ay["outer_wall_sec"] / gurobi["outer_wall_sec"]
    if ratio < 1.0:
        classification = "AY_FASTER"
    elif ratio > 1.0:
        classification = "GUROBI_FASTER"
    else:
        classification = "TIE"
    return {"classification": classification, "ay_over_gurobi": ratio}


def schedule_for_repetition(
    names: list[str], repetition: int, *, seed: int = SCHEDULE_SEED
) -> list[str]:
    """Deterministic rotated/reversed traversal independent of solver AB/BA."""

    if not names:
        return []
    shuffled = list(names)
    random.Random(seed).shuffle(shuffled)
    offset = repetition % len(shuffled)
    rotated = shuffled[offset:] + shuffled[:offset]
    return list(reversed(rotated)) if repetition % 2 else rotated


def solver_order(name: str, names: list[str], repetition: int) -> tuple[str, str]:
    """Give every case exactly balanced AY-first/Gurobi-first exposure."""

    # The case index prevents every process in a pass from sharing one solver
    # order while repetition parity gives exact AB/BA balance for even counts.
    return (
        ("ay", "gurobi")
        if (names.index(name) + repetition) % 2 == 0
        else ("gurobi", "ay")
    )


def run_pair_before_verification(
    order: tuple[str, str],
    capture: Callable[[str], dict[str, Any]],
    verify: Callable[[str, dict[str, Any]], dict[str, Any]],
) -> dict[str, dict[str, Any]]:
    """Finish both timed children before either checker can perturb the host.

    The checkers re-read the model and may warm file-system/page caches.  Their
    walls are excluded from the solver measurements, but running one between
    the two solvers still changes the second solver's environment.  Retain the
    requested AB/BA capture order, then verify both already-frozen results.
    """

    captured = [(solver, capture(solver)) for solver in order]
    return {
        solver: verify(solver, result) for solver, result in captured
    }


def sat_relu_route_census(
    evaluations: list[dict[str, Any]], expected_trials: int
) -> dict[str, Any]:
    """Aggregate the fail-closed bounded-route evidence for AY trials."""

    routes = [evaluation.get("sat_relu_route") for evaluation in evaluations]
    accepted = sum(
        isinstance(route, dict) and route.get("accepted") is True for route in routes
    )
    attempts = sum(
        route.get("attempt_count", 0)
        for route in routes
        if isinstance(route, dict)
        and isinstance(route.get("attempt_count", 0), int)
        and not isinstance(route.get("attempt_count", 0), bool)
    )
    declines = sum(
        route.get("decline_count", 0)
        for route in routes
        if isinstance(route, dict)
        and isinstance(route.get("decline_count", 0), int)
        and not isinstance(route.get("decline_count", 0), bool)
    )
    fallbacks = sum(
        route.get("fallback_count", 0)
        for route in routes
        if isinstance(route, dict)
        and isinstance(route.get("fallback_count", 0), int)
        and not isinstance(route.get("fallback_count", 0), bool)
    )
    malformed = sum(
        route.get("malformed_count", 0)
        for route in routes
        if isinstance(route, dict)
        and isinstance(route.get("malformed_count", 0), int)
        and not isinstance(route.get("malformed_count", 0), bool)
    )
    return {
        "expected_trials": expected_trials,
        "evaluated_trials": len(evaluations),
        "accepted_trials": accepted,
        "rejected_trials": len(evaluations) - accepted,
        "bounded_attempts": attempts,
        "declines": declines,
        "ordinary_cdcl_fallbacks": fallbacks,
        "malformed_trace_lines": malformed,
        "closed": (
            len(evaluations) == expected_trials
            and accepted == expected_trials
            and attempts == expected_trials
            and declines == 0
            and fallbacks == 0
            and malformed == 0
        ),
    }


def aggregate(
    rows: list[dict[str, Any]], names: list[str], repetitions: int
) -> dict[str, Any]:
    grouped: dict[str, list[dict[str, Any]]] = collections.defaultdict(list)
    for row in rows:
        grouped[row["name"]].append(row)
    cases = []
    for name in names:
        trials = grouped.get(name, [])
        counts = collections.Counter(row.get("repetition") for row in trials)
        complete = (
            len(trials) == repetitions
            and set(counts) == set(range(repetitions))
            and all(count == 1 for count in counts.values())
        )
        classifications = [
            row["comparison"]["classification"] for row in trials
        ]
        invalid = any(value == "INCONCLUSIVE_INVALID" for value in classifications)
        route_census = sat_relu_route_census(
            [row["ay_evaluation"] for row in trials], repetitions
        )
        gurobi_advantages = [
            row["repetition"]
            for row in trials
            if row["comparison"]["classification"]
            in ("GUROBI_ONLY", "GUROBI_FASTER")
        ]
        ay_walls = [
            row["ay_evaluation"]["outer_wall_sec"]
            for row in trials
            if row["ay_evaluation"]["solved"]
        ]
        gurobi_walls = [
            row["gurobi_evaluation"]["outer_wall_sec"]
            for row in trials
            if row["gurobi_evaluation"]["solved"]
        ]
        if not complete:
            classification = "INCOMPLETE"
        elif invalid or not route_census["closed"]:
            classification = "INCONCLUSIVE_INVALID"
        elif gurobi_advantages:
            classification = "GUROBI_OBSERVATION_ADVANTAGE"
        elif len(ay_walls) != repetitions or len(gurobi_walls) != repetitions:
            classification = "INCONCLUSIVE_UNSOLVED"
        else:
            classification = "AY_NO_SLOWER_ALL_OBSERVATIONS"
        ay_median = statistics.median(ay_walls) if ay_walls else None
        gurobi_median = statistics.median(gurobi_walls) if gurobi_walls else None
        cases.append(
            {
                "name": name,
                "expected_status": (
                    trials[0].get("expected_status") if trials else None
                ),
                "classification": classification,
                "trials": len(trials),
                "repetition_counts": dict(sorted(counts.items())),
                "gurobi_advantage_repetitions": gurobi_advantages,
                "paired_classifications": dict(sorted(collections.Counter(classifications).items())),
                "ay_sat_relu_route": route_census,
                "ay_median_outer_wall_sec": ay_median,
                "gurobi_median_outer_wall_sec": gurobi_median,
                "median_ay_over_gurobi": (
                    ay_median / gurobi_median
                    if ay_median is not None and gurobi_median not in (None, 0.0)
                    else None
                ),
            }
        )
    known_advantages = [
        case for case in cases if case["classification"] == "GUROBI_OBSERVATION_ADVANTAGE"
    ]
    inconclusive = [
        case
        for case in cases
        if case["classification"].startswith("INCOMPLETE")
        or case["classification"].startswith("INCONCLUSIVE")
    ]
    route_census = sat_relu_route_census(
        [row["ay_evaluation"] for row in rows], len(names) * repetitions
    )
    return {
        "expected_pairs": len(names) * repetitions,
        "completed_pairs": len(rows),
        "classification_counts": dict(
            sorted(collections.Counter(case["classification"] for case in cases).items())
        ),
        "paired_observation_counts": dict(
            sorted(
                collections.Counter(
                    row["comparison"]["classification"] for row in rows
                ).items()
            )
        ),
        "known_gurobi_advantages": known_advantages,
        "inconclusive_cases": inconclusive,
        "ay_sat_relu_route": route_census,
        "dominance_closed": (
            len(rows) == len(names) * repetitions
            and not known_advantages
            and not inconclusive
            and route_census["closed"]
        ),
        "cases": cases,
    }


def aggregate_certified(
    rows: list[dict[str, Any]], names: list[str], repetitions: int
) -> dict[str, Any]:
    grouped: dict[str, list[dict[str, Any]]] = collections.defaultdict(list)
    for row in rows:
        grouped[row["name"]].append(row)
    cases = []
    for name in names:
        trials = grouped.get(name, [])
        counts = collections.Counter(row.get("repetition") for row in trials)
        complete = (
            len(trials) == repetitions
            and set(counts) == set(range(repetitions))
            and all(count == 1 for count in counts.values())
        )
        accepted = [
            row
            for row in trials
            if row["evaluation"]["solved"]
            and row["evaluation"]["evidence_mode"] == "verified-sat-relu-rup"
        ]
        walls = [row["evaluation"]["outer_wall_sec"] for row in accepted]
        route_census = sat_relu_route_census(
            [row["evaluation"] for row in trials], repetitions
        )
        if not complete:
            classification = "INCOMPLETE"
        elif len(accepted) != repetitions or not route_census["closed"]:
            classification = "CERTIFIED_FUNCTIONALITY_FAILED"
        else:
            classification = "VERIFIED_INFEASIBLE"
        cases.append(
            {
                "name": name,
                "classification": classification,
                "trials": len(trials),
                "repetition_counts": dict(sorted(counts.items())),
                "verified_trials": len(accepted),
                "ay_sat_relu_route": route_census,
                "median_outer_wall_sec": statistics.median(walls) if walls else None,
                "min_outer_wall_sec": min(walls) if walls else None,
                "max_outer_wall_sec": max(walls) if walls else None,
            }
        )
    failed = [case for case in cases if case["classification"] != "VERIFIED_INFEASIBLE"]
    route_census = sat_relu_route_census(
        [row["evaluation"] for row in rows], len(names) * repetitions
    )
    return {
        "expected_trials": len(names) * repetitions,
        "completed_trials": len(rows),
        "functionality_closed": (
            len(rows) == len(names) * repetitions
            and not failed
            and route_census["closed"]
        ),
        "failed_cases": failed,
        "ay_sat_relu_route": route_census,
        "cases": cases,
    }


def default_output_path() -> Path:
    stamp = closure.utc_now().replace(":", "").replace("-", "").replace(".", "")
    return REPO_ROOT / "evals" / "results" / "ay-gurobi-w1-latency" / f"{stamp}.json"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--mps-dir", type=Path, required=True)
    parser.add_argument("--cases", type=Path, default=CASE_LIST_PATH)
    parser.add_argument("--ay-bin", type=Path, default=DEFAULT_AY_BIN)
    parser.add_argument("--gurobi-python", default=sys.executable)
    parser.add_argument("--timeout", type=float, default=5.0)
    parser.add_argument("--hard-timeout-grace", type=float, default=10.0)
    parser.add_argument("--checker-timeout", type=float, default=30.0)
    parser.add_argument("--repetitions", type=int, default=16)
    parser.add_argument("--certified-repetitions", type=int, default=3)
    parser.add_argument("--out", type=Path, default=None)
    return parser


def validate_args(args: argparse.Namespace, parser: argparse.ArgumentParser) -> None:
    for name in ("timeout", "hard_timeout_grace", "checker_timeout"):
        value = getattr(args, name)
        if not math.isfinite(value) or value <= 0:
            parser.error(f"--{name.replace('_', '-')} must be finite and positive")
    if args.repetitions < 2 or args.repetitions % 2:
        parser.error("--repetitions must be a positive even number (AB/BA balance)")
    if args.certified_repetitions <= 0:
        parser.error("--certified-repetitions must be positive")


def exit_code(summary: dict[str, Any], certified: dict[str, Any]) -> int:
    if not certified["functionality_closed"]:
        return 3 if certified["completed_trials"] == certified["expected_trials"] else 2
    if summary["inconclusive_cases"]:
        invalid = any(
            case["classification"] == "INCONCLUSIVE_INVALID"
            for case in summary["inconclusive_cases"]
        )
        return 3 if invalid else 2
    if summary["known_gurobi_advantages"]:
        return 1
    return 0 if summary["dominance_closed"] else 2


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    validate_args(args, parser)

    case_list = args.cases.expanduser().resolve(strict=True)
    expectations = load_case_expectations(case_list)
    case_set = classify_case_set(case_list, expectations)
    names = list(expectations)
    mps_dir = args.mps_dir.expanduser().resolve(strict=True)
    models = discover_models(mps_dir, names)
    for model in models:
        model["expected_status"] = expectations[model["name"]]
    by_name = {model["name"]: model for model in models}
    ay_source = args.ay_bin.expanduser().resolve(strict=True)
    gurobi_python = closure.resolve_executable(args.gurobi_python)
    output = (args.out or default_output_path()).expanduser().resolve()
    artifacts = output.with_name(f"{output.stem}.artifacts")
    if output.exists() or artifacts.exists():
        parser.error(f"refusing to overwrite existing output/artifacts: {output}, {artifacts}")
    output.parent.mkdir(parents=True, exist_ok=True)

    warn_concurrent_build()
    plan = plan_solver_resources(1, cores=1, label="ay_gurobi_w1_latency.py")
    if plan.jobs != 1 or plan.nbcore != 1:
        raise RuntimeError(f"W1 serial single-core plan is not serial: {plan}")
    git = closure.git_provenance(REPO_ROOT)
    artifacts.mkdir(parents=True)
    frozen_ay = artifacts / "bin" / "ay-milp"
    ay_identity = closure.freeze_binary(ay_source, frozen_ay)
    ay_binary = Path(ay_identity["frozen"]["path"])
    env, env_posture = closure.controlled_environment()

    document: dict[str, Any] = {
        "schema": SCHEMA,
        "state": "running",
        "started_at": closure.utc_now(),
        "finished_at": None,
        "selection": {
            "cases": names,
            "count": len(names),
            "repetitions": args.repetitions,
            "certified_repetitions": args.certified_repetitions,
            "expected_statuses": expectations,
            "case_list": closure.file_identity(case_list),
            "case_set": case_set,
        },
        "posture": {
            "serial": True,
            "threads": 1,
            "seed": SOLVER_SEED,
            "time_limit_sec": args.timeout,
            "outer_hard_timeout_sec": args.timeout + args.hard_timeout_grace,
            "checker_timeout_sec": args.checker_timeout,
            "ay_deterministic": True,
            "ay_require": "witness",
            "ay_logical_memory_budget_bytes": plan.memlimit_mb * 1024 * 1024,
            "ay_certificate_emission": True,
            "ay_witness_format": "rational",
            "ay_sat_relu_trace": (
                "AY_MILP_TRACE=1 injected only into AY solve children after the "
                "controlled environment scrub"
            ),
            "gurobi_mip_gap": 0.0,
            "gurobi_mip_gap_abs": 0.0,
            "measured_unit": "fresh solver process wall including parse/route/output",
            "pair_timing_isolation": (
                "both timed solver children finish before either exact point or "
                "certificate checker starts"
            ),
            "point_checker": (
                "frozen production ay-milp check-point; literal exact AY rational "
                "points and exact Gurobi continuous completion with integral values fixed"
            ),
            "ay_point_evidence_mode": PointEvidenceMode.AY_RATIONAL_LITERAL.value,
            "gurobi_point_evidence_mode": PointEvidenceMode.GUROBI_DECIMAL_REPAIR.value,
            "gurobi_point_repair_time_limit_sec": min(
                args.checker_timeout, MAX_GUROBI_POINT_REPAIR_SEC
            ),
            "gurobi_point_repair_memory_budget_bytes": plan.memlimit_mb * 1024 * 1024,
            "common_unsat_evidence": (
                "Gurobi status-only versus AY default production; every conclusive "
                "bounded AY UNSAT must carry a checker-VERIFIED sat-relu-rup claim"
            ),
            "ay_sat_evidence": (
                "exact point plus checker-consistent VERIFIED primal and dual claims"
            ),
            "solver_order": "per-case AB/BA balanced; corpus rotated and reversed",
            "acceptance": (
                "no valid paired observation in which Gurobi is faster or alone; "
                "every AY solve has exactly one conclusive bounded SAT/ReLU attempt, "
                "zero declines, and zero ordinary-CDCL fallbacks"
            ),
            "environment": env_posture,
        },
        "resource_envelope": {
            "requested_jobs": 1,
            "jobs": plan.jobs,
            "memlimit_mb_per_child": plan.memlimit_mb,
            "nbcore_per_child": plan.nbcore,
            "headroom_mb": plan.headroom_mb,
            "memory_enforcement": "scripts/_oom_guard.py process-group RSS watchdog",
            "ay_solve_logical_memory_budget_bytes": plan.memlimit_mb * 1024 * 1024,
            "lease": "one process-scoped host lease for the complete campaign",
        },
        "schedule": {
            "seed": SCHEDULE_SEED,
            "even_repetitions_required": True,
            "orders": [
                {
                    "repetition": repetition,
                    "cases": schedule_for_repetition(names, repetition),
                    "solver_orders": {
                        name: list(solver_order(name, names, repetition)) for name in names
                    },
                }
                for repetition in range(args.repetitions)
            ],
        },
        "provenance": {
            "harness": closure.file_identity(Path(__file__)),
            "authoritative_runner": closure.file_identity(SCRIPT_DIR / "ay_gurobi_closure.py"),
            "oom_guard": closure.file_identity(SCRIPT_DIR / "_oom_guard.py"),
            "gurobi_child_sha256": closure.sha256_text(closure.GUROBI_CHILD),
            "ay_binary": ay_identity,
            "gurobi_python": closure.file_identity(gurobi_python),
            "git": git,
            "host": {
                "node": platform.node(),
                "platform": platform.platform(),
                "machine": platform.machine(),
                "processor": platform.processor(),
                "python": sys.version,
                "physical_ram_mb": physical_ram_mb(),
                "effective_physical_cores": physical_core_count(),
            },
            "invocation": [
                str(Path(__file__).resolve()),
                *(argv if argv is not None else sys.argv[1:]),
            ],
            "license_environment_values_recorded": False,
        },
        "instances": models,
        "gurobi_probe": None,
        "warmups": [],
        "rows": [],
        "summary": aggregate([], names, args.repetitions),
        "certified_functionality": {
            "posture": {
                "solver": "AY only; no equivalence claim against uncertified Gurobi",
                "require": "full",
                "repetitions": args.certified_repetitions,
                "acceptance": (
                    "every INFEASIBLE capture has a checker-VERIFIED infeasible "
                    "claim and exactly one conclusive bounded SAT/ReLU attempt, "
                    "with zero declines/fallbacks"
                ),
                "latency_reported_separately": True,
            },
            "rows": [],
            "summary": aggregate_certified(
                [],
                [name for name in names if expectations[name] == "INFEASIBLE"],
                args.certified_repetitions,
            ),
        },
    }
    closure.atomic_write_json(output, document)

    probe_process = closure.run_guarded_capture(
        closure.build_gurobi_probe_command(gurobi_python),
        memlimit_mb=plan.memlimit_mb,
        timeout_sec=args.checker_timeout,
        label="ay_gurobi_w1_latency.py[gurobi-probe]",
        env=env,
        env_posture=env_posture,
        artifact_dir=artifacts / "gurobi-probe",
        artifact_root=artifacts,
    )
    probe, probe_error = closure.parse_process_json(probe_process, artifacts)
    document["gurobi_probe"] = {
        "process": probe_process,
        "result": probe,
        "parse_error": probe_error,
    }
    if (
        not closure.process_is_clean(probe_process)
        or probe_error is not None
        or not probe
        or probe.get("status") != "PROBE_OK"
    ):
        document["state"] = "incomplete"
        document["finished_at"] = closure.utc_now()
        document["failure"] = "Gurobi import/license probe failed"
        closure.atomic_write_json(output, document)
        return 2
    closure.atomic_write_json(output, document)

    hard_timeout = args.timeout + args.hard_timeout_grace

    def capture_solver(
        solver: str, model: Path, directory: Path, *, require: str = "witness"
    ) -> dict[str, Any]:
        if solver == "ay":
            return run_ay(
                ay_binary, model, args.timeout, hard_timeout, plan, env,
                env_posture, directory / "ay", artifacts, require=require,
            )
        return closure.run_gurobi(
            gurobi_python, model, args.timeout, SOLVER_SEED, hard_timeout,
            plan, env, env_posture, directory, artifacts,
        )

    def verify_solver(
        solver: str, model: Path, directory: Path, result: dict[str, Any]
    ) -> dict[str, Any]:
        if solver == "ay":
            result["point_check"] = check_point(
                ay_binary, model, result["witness"],
                PointEvidenceMode.AY_RATIONAL_LITERAL, plan, args.checker_timeout,
                env, env_posture, directory / "ay-point-check", artifacts,
            )
            result["certificate_check"] = check_certificate(
                ay_binary, model, result["certificate"], plan, args.checker_timeout,
                env, env_posture, directory / "ay-certificate-check", artifacts,
            )
            result["certificate_artifact"] = inspect_certificate_artifact(
                result["certificate"], artifacts
            )
            result["sat_relu_replay_marker"] = certificate_replay_present(
                result["certificate_artifact"]
            )
            return result
        result["point_check"] = check_point(
            ay_binary, model, result["solution"],
            PointEvidenceMode.GUROBI_DECIMAL_REPAIR, plan, args.checker_timeout,
            env, env_posture, directory / "gurobi-point-check", artifacts,
        )
        return result

    def run_solver(
        solver: str, model: Path, directory: Path, *, require: str = "witness"
    ) -> dict[str, Any]:
        return verify_solver(
            solver,
            model,
            directory,
            capture_solver(solver, model, directory, require=require),
        )

    # Warm each executable and the common input/checker path once.  Warmups are
    # evidence-gated but excluded from every timing statistic.
    warm_name = min(names, key=lambda name: by_name[name]["size_bytes"])
    warm_model = Path(by_name[warm_name]["path"])
    for index, solver in enumerate(("ay", "gurobi")):
        result = run_solver(solver, warm_model, artifacts / f"warmup-{index}-{solver}")
        evaluation = evaluate_expected(solver, result, expectations[warm_name])
        document["warmups"].append(
            {"solver": solver, "name": warm_name, "result": result, "evaluation": evaluation}
        )
        closure.atomic_write_json(output, document)
        if not evaluation["valid"] or not evaluation["correct"] or not evaluation["solved"]:
            document["state"] = "invalid"
            document["finished_at"] = closure.utc_now()
            document["failure"] = (
                f"{solver} warmup did not produce a valid result for "
                f"{expectations[warm_name]}"
            )
            closure.atomic_write_json(output, document)
            return 3

    total = len(names) * args.repetitions
    completed = 0
    for repetition in range(args.repetitions):
        warn_concurrent_build()
        for name in schedule_for_repetition(names, repetition):
            model_record = by_name[name]
            model = Path(model_record["path"])
            if closure.file_identity(model)["sha256"] != model_record["sha256"]:
                raise RuntimeError(f"benchmark input changed during campaign: {model}")
            order = solver_order(name, names, repetition)
            case_dir = artifacts / f"r{repetition:02d}-{name}"
            print(
                f"[{completed + 1}/{total}] {name} r{repetition + 1}/{args.repetitions} "
                f"order={order[0]}->{order[1]}",
                flush=True,
            )
            results = run_pair_before_verification(
                order,
                lambda solver: capture_solver(solver, model, case_dir),
                lambda solver, result: verify_solver(solver, model, case_dir, result),
            )
            ay_evaluation = evaluate_expected("ay", results["ay"], expectations[name])
            gurobi_evaluation = evaluate_expected(
                "gurobi", results["gurobi"], expectations[name]
            )
            comparison = compare_pair(ay_evaluation, gurobi_evaluation)
            document["rows"].append(
                {
                    "name": name,
                    "repetition": repetition,
                    "expected_status": expectations[name],
                    "solver_order": list(order),
                    "model": model_record,
                    "ay": results["ay"],
                    "gurobi": results["gurobi"],
                    "ay_evaluation": ay_evaluation,
                    "gurobi_evaluation": gurobi_evaluation,
                    "comparison": comparison,
                }
            )
            document["summary"] = aggregate(document["rows"], names, args.repetitions)
            closure.atomic_write_json(output, document)
            completed += 1
            print(
                f"  AY={ay_evaluation['outer_wall_sec']}s "
                f"Gurobi={gurobi_evaluation['outer_wall_sec']}s "
                f"{comparison['classification']}",
                flush=True,
            )

    # Separate service posture: AY emits a full, independently checked UNSAT
    # artifact.  Its wall is reported, never substituted into or compared by
    # the common-capability speed gate above.
    certified_names = [name for name in names if expectations[name] == "INFEASIBLE"]
    certified_total = len(certified_names) * args.certified_repetitions
    certified_completed = 0
    for repetition in range(args.certified_repetitions):
        warn_concurrent_build()
        for name in schedule_for_repetition(certified_names, repetition):
            model_record = by_name[name]
            model = Path(model_record["path"])
            if closure.file_identity(model)["sha256"] != model_record["sha256"]:
                raise RuntimeError(f"benchmark input changed during certified lane: {model}")
            print(
                f"[certified {certified_completed + 1}/{certified_total}] {name} "
                f"r{repetition + 1}/{args.certified_repetitions}",
                flush=True,
            )
            result = run_solver(
                "ay",
                model,
                artifacts / f"certified-r{repetition:02d}-{name}",
                require="full",
            )
            evaluation = evaluate_expected(
                "ay",
                result,
                "INFEASIBLE",
                require_verified_infeasible=True,
            )
            document["certified_functionality"]["rows"].append(
                {
                    "name": name,
                    "repetition": repetition,
                    "expected_status": "INFEASIBLE",
                    "ay": result,
                    "evaluation": evaluation,
                }
            )
            document["certified_functionality"]["summary"] = aggregate_certified(
                document["certified_functionality"]["rows"],
                certified_names,
                args.certified_repetitions,
            )
            closure.atomic_write_json(output, document)
            certified_completed += 1
            print(
                f"  AY-full={evaluation['outer_wall_sec']}s "
                f"evidence={evaluation['evidence_mode']}",
                flush=True,
            )

    document["state"] = "complete"
    document["finished_at"] = closure.utc_now()
    document["summary"] = aggregate(document["rows"], names, args.repetitions)
    closure.atomic_write_json(output, document)
    summary = document["summary"]
    certified = document["certified_functionality"]["summary"]
    print(
        f"wrote {output}; closed={summary['dominance_closed']} "
        f"Gurobi-advantages={len(summary['known_gurobi_advantages'])} "
        f"inconclusive={len(summary['inconclusive_cases'])} "
        f"route-declines={summary['ay_sat_relu_route']['declines']} "
        f"route-fallbacks={summary['ay_sat_relu_route']['ordinary_cdcl_fallbacks']} "
        f"certified={certified['functionality_closed']}",
        flush=True,
    )
    return exit_code(summary, certified)


if __name__ == "__main__":
    try:
        status = main()
    except Exception:
        traceback.print_exc()
        status = 2
    raise SystemExit(status)
