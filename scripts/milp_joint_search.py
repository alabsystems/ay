#!/usr/bin/env python3
# ay-script: milp-joint-search
"""Preregistered joint MILP configuration search with a sealed holdout gate.

This harness answers the part that one-at-a-time ablations cannot: whether cuts,
cut retention, branching effort, and structural presolve choices must move
together to cross a local optimum.  Its default grid is the full 4 x 3 x 3 x 4
Cartesian product (144 configurations).  Training chooses exactly one winner.
Only after that choice is persisted may the harness run the frozen held-out
split.

The search metric is repeated node counts, not a claim that one node-capped run
is magically load-independent.  ``AY_MILP_MAX_NODES`` caps the tree at 20,000
nodes by default.  Every case/arm is run three times in an interleaved order;
status, solvedness, and nodes must agree exactly, and a traced partial/deadline-
truncated root pass makes the arm ineligible.  An unsolved run must reach the
node cap.  Every terminal answer is gated by the same exact point/certificate
and MIPLIB-reference checks as ``ay_gurobi_closure.py``.

The one training-selected arm then faces the held-out node screen and, only if
that passes, a separate four-repeat AB/BA production-wall gate with the node cap
and diagnostic trace removed.  Acceptance therefore means both a reproducible
node improvement and an isolated, order-balanced production-wall improvement.

Acceptance is deliberately stricter than an aggregate average:

* no baseline-solved case may become unsolved;
* no jointly solved case may use more nodes than baseline;
* at least one held-out case must gain a solve or use fewer nodes;
* production wall may lose neither solves nor median wall time on any held-out
  case, and must improve at least one by the preregistered 1%/1 ms margin;
* any wrong/reference-disagreeing arm is a soundness alarm, never a fast arm.

All solver/checker children are serial and live under one process-scoped
``_oom_guard`` plan and its process-group RSS watchdog.  The frozen binary,
input hashes, environment settings, resource envelope, raw outputs, and every
completed run are stored in append-only JSONL plus a sibling artifact tree.
Re-running with ``--resume`` skips complete keys and continues after interruption.

Examples::

    scripts/milp_joint_search.py describe
    scripts/milp_joint_search.py run --out evals/results/milp-joint/search.jsonl
    scripts/milp_joint_search.py run --resume --out evals/results/milp-joint/search.jsonl
    scripts/milp_joint_search.py analyze evals/results/milp-joint/search.jsonl

Exit codes for ``run`` are 0 accepted on holdout, 1 measured rejection/no
training winner, 2 incomplete or invalid campaign evidence, and 3 a soundness
alarm.  Importing this module never launches a solver.
"""

from __future__ import annotations

import argparse
import collections
import dataclasses
import datetime as dt
import hashlib
import itertools
import json
import math
import os
import platform
import re
import statistics
import sys
from pathlib import Path
from typing import Any, Iterable

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
TRAIN_LIST = SCRIPT_DIR / "data" / "milp_joint_search_train.txt"
HOLDOUT_LIST = SCRIPT_DIR / "data" / "milp_joint_search_holdout.txt"
DEFAULT_AY_BIN = REPO_ROOT / "target" / "release" / "ay-milp"
SCHEMA = "ay-milp-joint-search-v2"
BASELINE_ID = "baseline"
DEFAULT_NODE_CAP = 20_000
DEFAULT_SOLVER_LIMIT_SEC = 60.0
DEFAULT_CHECKER_LIMIT_SEC = 120.0
DEFAULT_HARD_GRACE_SEC = 120.0
NODE_REPETITIONS = 3
WALL_REPETITIONS = 4
WALL_STRICT_RELATIVE_GAIN = 0.01
WALL_STRICT_ABSOLUTE_GAIN_SEC = 0.001
NODE_METRIC = "node"
WALL_METRIC = "production-wall"

sys.path.insert(0, str(SCRIPT_DIR))
import ay_gurobi_closure as evidence  # noqa: E402
from _oom_guard import (  # noqa: E402
    physical_core_count,
    physical_ram_mb,
    plan_solver_resources,
    warn_concurrent_build,
)


@dataclasses.dataclass(frozen=True)
class CoordinateValue:
    name: str
    env: tuple[tuple[str, str], ...]

    def as_dict(self) -> dict[str, str]:
        return dict(self.env)


@dataclasses.dataclass(frozen=True)
class JointConfig:
    config_id: str
    coordinates: tuple[tuple[str, str], ...]
    env: tuple[tuple[str, str], ...]

    def env_dict(self) -> dict[str, str]:
        return dict(self.env)

    def coordinate_dict(self) -> dict[str, str]:
        return dict(self.coordinates)


# These are hypotheses for this campaign, not claimed historical winners.  The
# values are fixed here so a run cannot add an arm after seeing held-out data.
# Each coordinate owns disjoint environment variables, making every Cartesian
# product entry unambiguous and audit-friendly.
#
# Presolve deliberately uses structural switches, not PRESOLVE_SHARE.  The
# latter is a fraction of a wall-clock deadline inside bab.rs; calling its
# resulting tree-node delta deterministic would merely benchmark how much exact
# propagation happened to fit under current load.  These switches alter which
# established pass runs, while the three-repeat/trace gate below still refuses
# any root pipeline whose own deadline visibly truncates work.
COORDINATES: tuple[tuple[str, tuple[CoordinateValue, ...]], ...] = (
    (
        "cuts",
        (
            CoordinateValue("default", ()),
            CoordinateValue("gmi-1", (("AY_MILP_GMI_ROUNDS", "1"),)),
            CoordinateValue("gmi-5", (("AY_MILP_GMI_ROUNDS", "5"),)),
            CoordinateValue("gmi-10", (("AY_MILP_GMI_ROUNDS", "10"),)),
        ),
    ),
    (
        "cut-selection-budget",
        (
            CoordinateValue("default", ()),
            CoordinateValue(
                "top8-budget16",
                (
                    ("AY_MILP_ROOT_CUTS_PER_ROUND", "16"),
                    ("AY_MILP_CUT_TOPK", "8"),
                ),
            ),
            CoordinateValue(
                "top24-budget40",
                (
                    ("AY_MILP_ROOT_CUTS_PER_ROUND", "40"),
                    ("AY_MILP_CUT_TOPK", "24"),
                ),
            ),
        ),
    ),
    (
        "branching",
        (
            CoordinateValue("default", ()),
            CoordinateValue(
                "economy",
                (
                    ("AY_MILP_SB_REL", "2"),
                    ("AY_MILP_SB_CANDS", "8"),
                    ("AY_MILP_SB_TOTAL", "600"),
                ),
            ),
            CoordinateValue(
                "thorough",
                (
                    ("AY_MILP_SB_REL", "8"),
                    ("AY_MILP_SB_CANDS", "24"),
                    ("AY_MILP_SB_TOTAL", "6000"),
                ),
            ),
        ),
    ),
    (
        "structural-presolve",
        (
            CoordinateValue("default", ()),
            CoordinateValue(
                "exact-no-scout", (("AY_MILP_NO_PRESOLVE_SCOUT", "1"),)
            ),
            CoordinateValue("no-dualfix", (("AY_MILP_NO_DUALFIX", "1"),)),
            CoordinateValue("off", (("AY_MILP_NO_PRESOLVE", "1"),)),
        ),
    ),
)


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def canonical_hash(value: Any) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), allow_nan=False
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def build_grid(
    coordinates: tuple[tuple[str, tuple[CoordinateValue, ...]], ...] = COORDINATES,
) -> list[JointConfig]:
    if len(coordinates) < 4:
        raise ValueError("joint search requires at least four coordinates")
    coordinate_names = [name for name, _ in coordinates]
    if len(set(coordinate_names)) != len(coordinate_names):
        raise ValueError("duplicate coordinate name")
    grid: list[JointConfig] = []
    for choices in itertools.product(*(values for _, values in coordinates)):
        pairs = tuple(
            (coordinate_name, value.name)
            for (coordinate_name, _), value in zip(coordinates, choices)
        )
        env: dict[str, str] = {}
        for value in choices:
            for key, setting in value.env:
                if key in env:
                    raise ValueError(f"coordinates overlap on {key}")
                env[key] = setting
        config_id = "__".join(f"{name}={value}" for name, value in pairs)
        grid.append(JointConfig(config_id, pairs, tuple(sorted(env.items()))))
    ids = [config.config_id for config in grid]
    if len(ids) != len(set(ids)):
        raise ValueError("configuration ids are not unique")
    return grid


GRID = build_grid()
GRID_BY_ID = {config.config_id: config for config in GRID}
DEFAULT_GRID_CONFIG = next(
    config
    for config in GRID
    if all(value == "default" for _, value in config.coordinates)
)


def serialized_grid() -> list[dict[str, Any]]:
    return [
        {
            "config_id": config.config_id,
            "coordinates": config.coordinate_dict(),
            "environment": config.env_dict(),
        }
        for config in GRID
    ]


GRID_SHA256 = canonical_hash(serialized_grid())


def load_name_list(path: Path) -> list[str]:
    names = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line and not line.startswith("#"):
            names.append(line)
    duplicates = sorted(
        name for name, count in collections.Counter(names).items() if count > 1
    )
    if duplicates:
        raise ValueError(f"duplicate names in {path}: {', '.join(duplicates)}")
    if not names:
        raise ValueError(f"empty split list: {path}")
    return names


def load_splits(train_path: Path, holdout_path: Path) -> tuple[list[str], list[str]]:
    train = load_name_list(train_path)
    holdout = load_name_list(holdout_path)
    overlap = sorted(set(train) & set(holdout))
    if overlap:
        raise ValueError(f"training/holdout overlap: {', '.join(overlap)}")
    return train, holdout


def configured_environment(
    source: dict[str, str],
    config_env: dict[str, str],
    node_cap: int | None,
    metric: str = NODE_METRIC,
) -> tuple[dict[str, str], dict[str, Any]]:
    if metric not in (NODE_METRIC, WALL_METRIC):
        raise ValueError(f"unknown measurement metric {metric!r}")
    if metric == NODE_METRIC and node_cap is None:
        raise ValueError("node screening requires a node cap")
    if metric == WALL_METRIC and node_cap is not None:
        raise ValueError("production-wall measurement must not set a node cap")
    env, posture = evidence.controlled_environment(source)
    # The shared closure posture scrubs every AY_ / NY_ lane control.  Retain
    # the historical category in this report so tuning evidence still says
    # which non-MILP AY names were neutralized before the explicit arm was set.
    removed_by_base = posture.get("removed_solver_environment", {})
    removed_other_ay = sorted(
        {
            key
            for key in removed_by_base
            if key.startswith("AY_") and not key.startswith("AY_MILP_")
        }
        | {key for key in env if key.startswith("AY_")}
    )
    for key in list(env):
        if key.startswith("AY_"):
            env.pop(key)
    settings = dict(config_env)
    if metric == NODE_METRIC:
        settings["AY_MILP_MAX_NODES"] = str(node_cap)
        # Diagnostic only.  Its raw stderr is parsed below to reject a root
        # pipeline whose wall deadline changed the model handed to the tree.
        settings["AY_MILP_TRACE"] = "1"
    env.update(settings)
    posture = dict(posture)
    posture["base_environment_sha256_before_legacy_scrub"] = posture.pop(
        "environment_sha256"
    )
    posture["removed_non_milp_ay_environment_names"] = removed_other_ay
    posture["configured_ay_milp_environment"] = dict(sorted(settings.items()))
    posture["measurement_metric"] = metric
    posture["configured_environment_sha256"] = evidence.sha256_text(
        "".join(f"{key}={env[key]}\0" for key in sorted(env))
    )
    return env, posture


def campaign_environment_protocol(
    source: dict[str, str], node_cap: int
) -> dict[str, Any]:
    """Freeze the effective environment for every arm, without secret values.

    All ``AY_``/``NY_`` inputs are scrubbed before these hashes are computed, so
    changing a caller-side tuning knob cannot poison or strand a resumed run.
    Everything that remains can affect the same frozen binary, however, and a
    campaign resumed under a different remainder is not comparable evidence.
    """

    configured_hashes: dict[str, dict[str, str]] = {
        NODE_METRIC: {},
        WALL_METRIC: {},
    }
    baseline_env, baseline_posture = configured_environment(
        source, {}, node_cap, NODE_METRIC
    )
    del baseline_env
    configured_hashes[NODE_METRIC][BASELINE_ID] = baseline_posture[
        "configured_environment_sha256"
    ]
    _, wall_baseline_posture = configured_environment(
        source, {}, None, WALL_METRIC
    )
    configured_hashes[WALL_METRIC][BASELINE_ID] = wall_baseline_posture[
        "configured_environment_sha256"
    ]
    for config in GRID:
        _, posture = configured_environment(
            source, config.env_dict(), node_cap, NODE_METRIC
        )
        configured_hashes[NODE_METRIC][config.config_id] = posture[
            "configured_environment_sha256"
        ]
        _, wall_posture = configured_environment(
            source, config.env_dict(), None, WALL_METRIC
        )
        configured_hashes[WALL_METRIC][config.config_id] = wall_posture[
            "configured_environment_sha256"
        ]
    return {
        "scrubbed_solver_environment_prefixes": list(
            evidence.SOLVER_ENV_PREFIXES
        ),
        "scrubbed_solver_resource_environment_names": sorted(
            evidence.SOLVER_RESOURCE_ENV_NAMES
        ),
        "thread_limits": dict(evidence.THREAD_ENV),
        "base_environment_sha256": baseline_posture[
            "base_environment_sha256_before_legacy_scrub"
        ],
        "configured_environment_sha256_by_metric_and_config": configured_hashes,
    }


def host_record() -> dict[str, Any]:
    """Host identity that must stay fixed across repeated-node resumes."""

    return {
        "node": platform.node(),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "processor": platform.processor(),
        "python": sys.version,
        "physical_ram_mb": physical_ram_mb(),
        "effective_physical_cores": physical_core_count(),
    }


def parse_nodes(value: Any) -> tuple[int | None, str | None]:
    if isinstance(value, bool):
        return None, "node count is boolean"
    if isinstance(value, int):
        return (value, None) if value >= 0 else (None, "negative node count")
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        number = int(value)
        return (number, None) if number >= 0 else (None, "negative node count")
    return None, f"missing or non-integral node count {value!r}"


TRACE_DEADLINE_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "presolve-deadline",
        re.compile(r"AY_MILP_TRACE presolve:.*(?:EXPIRED|skipped \(deadline\))"),
    ),
    (
        "root-worker-preparation-deadline",
        re.compile(r"reason=(?:preparation-)?deadline\b"),
    ),
    (
        "root-cut-lp-stopped",
        re.compile(r"AY_MILP_TRACE cut loop: round \d+ LP Stopped; stopping"),
    ),
    (
        "root-repair-deadline",
        re.compile(r"AY_MILP_TRACE .*construction hit the deadline"),
    ),
    ("root-probe-deadline", re.compile(r"\bprobe-deadline\b")),
)


def inspect_node_trace(result: dict[str, Any], artifact_root: Path) -> dict[str, Any]:
    process = result.get("process") or {}
    stderr_identity = process.get("stderr") or {}
    relative = stderr_identity.get("path")
    if not isinstance(relative, str):
        return {
            "inspected": False,
            "issues": ["solver stderr artifact is missing from node screen"],
            "matches": [],
        }
    stderr_path = (artifact_root / relative).resolve()
    try:
        stderr_path.relative_to(artifact_root.resolve())
    except ValueError:
        return {
            "inspected": False,
            "issues": ["solver stderr artifact escaped the campaign directory"],
            "matches": [],
        }
    try:
        text = stderr_path.read_text(encoding="utf-8")
    except OSError as error:
        return {
            "inspected": False,
            "issues": [f"cannot inspect solver trace: {type(error).__name__}: {error}"],
            "matches": [],
        }
    matches = []
    for label, pattern in TRACE_DEADLINE_PATTERNS:
        matching_lines = [
            line.strip() for line in text.splitlines() if pattern.search(line)
        ]
        if matching_lines:
            matches.append({"kind": label, "lines": matching_lines[:16]})
    issues = [
        f"root work was deadline-truncated ({match['kind']})" for match in matches
    ]
    return {"inspected": True, "issues": issues, "matches": matches}


def evaluate_node_run(
    result: dict[str, Any],
    reference: dict[str, Any],
    sense: str,
    node_cap: int,
    trace: dict[str, Any] | None = None,
) -> dict[str, Any]:
    checked = evidence.evaluate_solver(
        "ay", result, reference, sense, evidence.REFERENCE_RELATIVE_TOLERANCE
    )
    verdict = result.get("verdict") or {}
    nodes, node_error = parse_nodes(verdict.get("nodes"))
    node_issues = []
    if node_error:
        node_issues.append(node_error)
    elif nodes is not None and nodes > node_cap + 1:
        node_issues.append(
            f"node count {nodes} exceeded cap {node_cap} by more than stop-check overshoot"
        )
    node_cap_reached = nodes is not None and nodes >= node_cap
    if not checked["solved"] and not node_cap_reached:
        node_issues.append(
            "unsolved run stopped before the fixed node cap; wall/root work contaminated score"
        )
    if trace is None:
        node_issues.append("node screen has no root-work trace inspection")
    else:
        node_issues.extend(trace.get("issues") or [])
    eligible = (
        not checked["invalid_issues"]
        and not checked["wrong_issues"]
        and not node_issues
    )
    return {
        **checked,
        "nodes": nodes,
        "node_cap": node_cap,
        "node_cap_reached": node_cap_reached,
        "node_gate_issues": node_issues,
        "score_eligible": eligible,
        "root_trace": trace,
    }


def evaluate_wall_run(
    result: dict[str, Any], reference: dict[str, Any], sense: str
) -> dict[str, Any]:
    checked = evidence.evaluate_solver(
        "ay", result, reference, sense, evidence.REFERENCE_RELATIVE_TOLERANCE
    )
    eligible = not checked["invalid_issues"] and not checked["wrong_issues"]
    return {**checked, "score_eligible": eligible}


def run_key(
    split: str,
    name: str,
    config_id: str,
    repetition: int = 0,
    metric: str = NODE_METRIC,
) -> str:
    if repetition < 0:
        raise ValueError("repetition must be non-negative")
    return f"{metric}|{split}|{name}|{config_id}|rep={repetition + 1}"


def safe_token(value: str, limit: int = 72) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9_.-]+", "-", value).strip("-") or "run"
    digest = hashlib.sha256(value.encode("utf-8")).hexdigest()[:10]
    return f"{cleaned[:limit]}-{digest}"


def next_attempt_dir(artifact_root: Path, key: str) -> Path:
    base = artifact_root / "runs" / safe_token(key)
    if not base.exists():
        return base
    index = 2
    while True:
        candidate = base.with_name(f"{base.name}-attempt{index}")
        if not candidate.exists():
            return candidate
        index += 1


def append_jsonl(path: Path, record: dict[str, Any], exclusive: bool = False) -> None:
    payload = json.dumps(record, sort_keys=True, allow_nan=False) + "\n"
    mode = "x" if exclusive else "a"
    with path.open(mode, encoding="utf-8") as handle:
        handle.write(payload)
        handle.flush()
        os.fsync(handle.fileno())


def load_jsonl(path: Path, *, repair_trailing: bool = False) -> list[dict[str, Any]]:
    records = []
    raw_bytes = path.read_bytes()
    lines = raw_bytes.splitlines(keepends=True)
    offset = 0
    for line_number, raw_line in enumerate(lines, 1):
        line_start = offset
        offset += len(raw_line)
        try:
            raw = raw_line.decode("utf-8")
        except UnicodeDecodeError as error:
            raw = ""
            decode_error: Exception | None = error
        else:
            decode_error = None
        try:
            if decode_error is not None:
                raise decode_error
            if not raw.strip():
                continue
            value = json.loads(raw)
            if not isinstance(value, dict):
                raise ValueError(f"non-object JSONL record at {path}:{line_number}")
            records.append(value)
        except (json.JSONDecodeError, UnicodeDecodeError) as error:
            is_partial_tail = line_number == len(lines) and not raw_bytes.endswith(b"\n")
            if not repair_trailing or not is_partial_tail:
                raise ValueError(
                    f"malformed JSONL at {path}:{line_number}; preserve/repair the partial line"
                ) from error
            with path.open("r+b") as handle:
                handle.truncate(line_start)
                handle.flush()
                os.fsync(handle.fileno())
            print(
                f"milp_joint_search.py: discarded incomplete trailing JSONL record "
                f"at line {line_number}",
                file=sys.stderr,
                flush=True,
            )
            break
    if not records or records[0].get("type") != "header":
        raise ValueError(f"{path} has no leading header record")
    return records


def index_records(records: Iterable[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    indexed = {}
    for record in records:
        if record.get("type") != "run":
            continue
        key = record.get("run_key")
        if not isinstance(key, str):
            raise ValueError("run record has no string run_key")
        if key in indexed:
            raise ValueError(f"duplicate completed run key: {key}")
        indexed[key] = record
    return indexed


def config_environment(config_id: str) -> dict[str, str]:
    if config_id == BASELINE_ID:
        return {}
    config = GRID_BY_ID.get(config_id)
    if config is None:
        raise ValueError(f"unknown configuration {config_id!r}")
    return config.env_dict()


def validate_artifact_identity(
    identity: dict[str, Any], artifact_root: Path, label: str
) -> Path:
    if not isinstance(identity, dict) or not isinstance(identity.get("path"), str):
        raise ValueError(f"{label} has no artifact identity")
    relative = Path(identity["path"])
    if relative.is_absolute():
        raise ValueError(f"{label} artifact path is absolute")
    root = artifact_root.resolve()
    path = (root / relative).resolve()
    try:
        path.relative_to(root)
    except ValueError as error:
        raise ValueError(f"{label} artifact escapes campaign directory") from error
    expected_exists = identity.get("exists")
    if not isinstance(expected_exists, bool):
        raise ValueError(f"{label} artifact has no boolean existence record")
    if not expected_exists:
        if path.exists():
            raise ValueError(f"{label} artifact appeared after the run")
        return path
    if not path.is_file() or path.is_symlink():
        raise ValueError(f"{label} artifact is missing, non-regular, or a symlink")
    stat = path.stat()
    if identity.get("size_bytes") != stat.st_size:
        raise ValueError(f"{label} artifact size changed")
    if identity.get("sha256") != evidence.sha256_file(path):
        raise ValueError(f"{label} artifact digest changed")
    return path


def validate_campaign_provenance(
    header: dict[str, Any], artifact_root: Path
) -> None:
    if header.get("schema") != SCHEMA:
        raise ValueError(f"campaign has unsupported schema {header.get('schema')!r}")
    if (header.get("grid") or {}).get("sha256") != GRID_SHA256:
        raise ValueError("campaign grid differs from this harness")
    provenance = header.get("provenance") or {}
    for label in (
        "harness",
        "evidence_harness",
        "oom_guard",
        "train_list",
        "holdout_list",
        "manifest",
        "solution_reference",
    ):
        identity = provenance.get(label)
        if not isinstance(identity, dict) or not isinstance(identity.get("path"), str):
            raise ValueError(f"campaign has no {label} provenance")
        path = Path(identity["path"])
        if not path.is_file() or evidence.sha256_file(path) != identity.get("sha256"):
            raise ValueError(f"campaign {label} provenance changed or is missing")
    for instance in header.get("instances") or []:
        path = Path(instance.get("path", ""))
        if not path.is_file() or evidence.sha256_file(path) != instance.get("sha256"):
            raise ValueError(
                f"campaign input {instance.get('name')!r} changed or is missing"
            )
    frozen = (provenance.get("ay_binary") or {}).get("frozen") or {}
    frozen_path = Path(frozen.get("path", ""))
    if not frozen_path.is_file() or frozen_path.is_symlink():
        raise ValueError("frozen AY binary is missing or a symlink")
    try:
        frozen_path.resolve().relative_to(artifact_root.resolve())
    except ValueError as error:
        raise ValueError("frozen AY binary escaped campaign artifacts") from error
    if (
        frozen_path.stat().st_size != frozen.get("size_bytes")
        or evidence.sha256_file(frozen_path) != frozen.get("sha256")
    ):
        raise ValueError("frozen AY binary changed")


def validate_result_artifacts(
    result: dict[str, Any], artifact_root: Path, run_label: str
) -> None:
    process = result.get("process")
    if not isinstance(process, dict):
        raise ValueError(f"{run_label} has no solver process")
    validate_artifact_identity(process.get("stdout"), artifact_root, f"{run_label} stdout")
    validate_artifact_identity(process.get("stderr"), artifact_root, f"{run_label} stderr")
    verdict, parse_error = evidence.parse_process_json(process, artifact_root)
    if result.get("verdict") != verdict or result.get("parse_error") != parse_error:
        raise ValueError(f"{run_label} parsed solver result disagrees with raw stdout")

    for artifact_name in ("certificate", "witness"):
        validate_artifact_identity(
            result.get(artifact_name), artifact_root, f"{run_label} {artifact_name}"
        )
    for checker_name, parser in (
        ("certificate_check", evidence.parse_verify_output),
        ("point_check", evidence.parse_point_output),
    ):
        checker = result.get(checker_name)
        if not isinstance(checker, dict):
            raise ValueError(f"{run_label} has malformed {checker_name}")
        checker_process = checker.get("process")
        if checker_process is None:
            if checker.get("parsed") is not None:
                raise ValueError(f"{run_label} skipped {checker_name} has parsed output")
            continue
        if not isinstance(checker_process, dict):
            raise ValueError(f"{run_label} has malformed {checker_name} process")
        stdout_path = validate_artifact_identity(
            checker_process.get("stdout"),
            artifact_root,
            f"{run_label} {checker_name} stdout",
        )
        validate_artifact_identity(
            checker_process.get("stderr"),
            artifact_root,
            f"{run_label} {checker_name} stderr",
        )
        parsed = parser(stdout_path.read_text(encoding="utf-8"))
        if checker.get("parsed") != parsed:
            raise ValueError(f"{run_label} {checker_name} disagrees with raw stdout")


def validate_run_semantics(
    records: Iterable[dict[str, Any]],
    header: dict[str, Any],
    artifact_root: Path,
) -> None:
    """Recompute stored scores and bind each run to the frozen campaign.

    Selection and final records must never be able to bless a hand-edited
    ``evaluation`` object, reference value, model digest, configuration, or
    effective environment.  Raw artifact hashes remain in each result; this
    check covers the structured facts that drive acceptance and resume.
    """

    instances = header.get("instances")
    if not isinstance(instances, list):
        raise ValueError("header has no frozen instance records")
    by_name: dict[str, dict[str, Any]] = {}
    for instance in instances:
        if not isinstance(instance, dict) or not isinstance(instance.get("name"), str):
            raise ValueError("header has a malformed instance record")
        name = instance["name"]
        if name in by_name:
            raise ValueError(f"header repeats instance {name!r}")
        if not isinstance(instance.get("reference"), dict):
            raise ValueError(f"header instance {name!r} has no frozen reference")
        if instance.get("sense") not in ("minimize", "maximize"):
            raise ValueError(f"header instance {name!r} has invalid objective sense")
        by_name[name] = instance

    node_cap = (header.get("posture") or {}).get("node_cap")
    if not isinstance(node_cap, int) or isinstance(node_cap, bool) or node_cap <= 0:
        raise ValueError("header has no valid fixed node cap")
    environment_protocol = header.get("environment_protocol") or {}
    base_environment_hash = environment_protocol.get("base_environment_sha256")
    configured_hashes = environment_protocol.get(
        "configured_environment_sha256_by_metric_and_config"
    )
    thread_limits = environment_protocol.get("thread_limits")
    if (
        not isinstance(base_environment_hash, str)
        or not isinstance(configured_hashes, dict)
        or not isinstance(thread_limits, dict)
    ):
        raise ValueError("header has no complete environment protocol")

    for record in records:
        if record.get("type") != "run":
            continue
        key = record.get("run_key")
        try:
            name = record["name"]
            config_id = record["config_id"]
            metric = record["metric"]
            repetition = record["repetition"]
            result = record["result"]
            stored_evaluation = record["evaluation"]
        except KeyError as error:
            raise ValueError(f"run {key!r} is missing {error.args[0]}") from error
        if record.get("schema") != SCHEMA:
            raise ValueError(f"run {key!r} has the wrong schema")
        if name not in by_name:
            raise ValueError(f"run {key!r} names an unfrozen instance")
        if metric not in (NODE_METRIC, WALL_METRIC):
            raise ValueError(f"run {key!r} has an unknown metric")
        repetition_count = (
            NODE_REPETITIONS if metric == NODE_METRIC else WALL_REPETITIONS
        )
        if (
            not isinstance(repetition, int)
            or isinstance(repetition, bool)
            or repetition not in range(repetition_count)
        ):
            raise ValueError(f"run {key!r} has an invalid repetition")
        instance = by_name[name]
        expected_config = config_environment(config_id)
        if record.get("configuration_environment") != dict(
            sorted(expected_config.items())
        ):
            raise ValueError(f"run {key!r} configuration environment was altered")
        if record.get("model_sha256") != instance.get("sha256"):
            raise ValueError(f"run {key!r} model digest disagrees with the header")
        if record.get("reference") != instance["reference"]:
            raise ValueError(f"run {key!r} reference disagrees with the header")
        validate_result_artifacts(result, artifact_root, f"run {key!r}")

        expected_settings = dict(expected_config)
        if metric == NODE_METRIC:
            expected_settings["AY_MILP_MAX_NODES"] = str(node_cap)
            expected_settings["AY_MILP_TRACE"] = "1"
        metric_hashes = configured_hashes.get(metric)
        if not isinstance(metric_hashes, dict):
            raise ValueError(f"header has no environment hashes for {metric!r}")
        expected_configured_hash = metric_hashes.get(config_id)
        if not isinstance(expected_configured_hash, str):
            raise ValueError(f"header has no environment hash for {config_id!r}")
        processes = [("solver", result.get("process"))]
        for checker_name in ("certificate_check", "point_check"):
            checker = result.get(checker_name) or {}
            if not isinstance(checker, dict):
                raise ValueError(f"run {key!r} has malformed {checker_name}")
            if checker.get("process") is not None:
                processes.append((checker_name, checker.get("process")))
        for process_name, process in processes:
            if not isinstance(process, dict):
                raise ValueError(f"run {key!r} has no {process_name} process record")
            posture = process.get("environment")
            if not isinstance(posture, dict):
                raise ValueError(
                    f"run {key!r} has no {process_name} environment record"
                )
            if posture.get("thread_limits") != thread_limits:
                raise ValueError(f"run {key!r} changed {process_name} thread limits")
            if (
                posture.get("base_environment_sha256_before_legacy_scrub")
                != base_environment_hash
            ):
                raise ValueError(f"run {key!r} changed the base environment")
            if posture.get("measurement_metric") != metric:
                raise ValueError(f"run {key!r} changed its measurement metric")
            if posture.get("configured_ay_milp_environment") != dict(
                sorted(expected_settings.items())
            ):
                raise ValueError(
                    f"run {key!r} changed {process_name} tuning settings"
                )
            if (
                posture.get("configured_environment_sha256")
                != expected_configured_hash
            ):
                raise ValueError(
                    f"run {key!r} changed the effective {process_name} environment"
                )

        try:
            computed_evaluation = (
                evaluate_node_run(
                    result,
                    instance["reference"],
                    instance["sense"],
                    node_cap,
                    inspect_node_trace(result, artifact_root),
                )
                if metric == NODE_METRIC
                else evaluate_wall_run(
                    result, instance["reference"], instance["sense"]
                )
            )
        except (KeyError, TypeError) as error:
            raise ValueError(f"run {key!r} has malformed solver evidence") from error
        if stored_evaluation != computed_evaluation:
            raise ValueError(f"run {key!r} evaluation disagrees with recomputation")


def training_node_schedule(train_names: list[str]) -> list[tuple[str, str, int]]:
    """Three corpus-wide passes; no arm receives adjacent self-repetitions."""

    configs = [BASELINE_ID, *(config.config_id for config in GRID)]
    schedule = []
    for repetition in range(NODE_REPETITIONS):
        if repetition == 0:
            config_order = configs
            name_order = train_names
        elif repetition == 1:
            config_order = list(reversed(configs))
            name_order = list(reversed(train_names))
        else:
            pivot = len(configs) // 2
            config_order = configs[pivot:] + configs[:pivot]
            name_order = train_names[1:] + train_names[:1]
        for config_id in config_order:
            for name in name_order:
                schedule.append((name, config_id, repetition))
    return schedule


def holdout_node_schedule(
    holdout_names: list[str], selected: str
) -> list[tuple[str, str, int]]:
    schedule = []
    for repetition in range(NODE_REPETITIONS):
        names = holdout_names if repetition != 1 else list(reversed(holdout_names))
        configs = (
            (BASELINE_ID, selected)
            if repetition % 2 == 0
            else (selected, BASELINE_ID)
        )
        for name in names:
            for config_id in configs:
                schedule.append((name, config_id, repetition))
    return schedule


def wall_holdout_schedule(
    holdout_names: list[str], selected: str
) -> list[tuple[str, str, int, str, int]]:
    """Four AB/BA passes: each arm occupies each order position twice."""

    schedule = []
    for repetition in range(WALL_REPETITIONS):
        baseline_first = repetition % 2 == 0
        order_name = "baseline-first" if baseline_first else "candidate-first"
        configs = (
            (BASELINE_ID, selected)
            if baseline_first
            else (selected, BASELINE_ID)
        )
        names = holdout_names if repetition < 2 else list(reversed(holdout_names))
        for name in names:
            for position, config_id in enumerate(configs):
                schedule.append((name, config_id, repetition, order_name, position))
    return schedule


def validate_record_protocol(
    records: list[dict[str, Any]], train_names: list[str], holdout_names: list[str]
) -> None:
    """Fail closed on unbalanced ordering or held-out exposure before sealing."""

    training_expected = training_node_schedule(train_names)
    training_seen: list[tuple[str, str, int]] = []
    holdout_node_seen: list[tuple[str, str, int]] = []
    wall_seen: list[tuple[str, str, int, str, int]] = []
    selection: dict[str, Any] | None = None
    wall_admission: dict[str, Any] | None = None
    final_seen = False
    seen_keys: set[str] = set()

    for index, record in enumerate(records):
        record_type = record.get("type")
        if record_type == "header":
            if index != 0:
                raise ValueError("header record appears after campaign start")
            continue
        if final_seen:
            raise ValueError("records appear after the final campaign record")
        if record_type == "selection":
            if selection is not None:
                raise ValueError("multiple selection records")
            if training_seen != training_expected:
                raise ValueError("selection was persisted before the repeated training grid")
            selection = record
            selected = record.get("selected_config_id")
            if selected is not None and selected not in GRID_BY_ID:
                raise ValueError(f"selection names unknown config {selected!r}")
            continue
        if record_type == "wall-admission":
            if wall_admission is not None:
                raise ValueError("multiple wall-admission records")
            if selection is None or not selection.get("selected_config_id"):
                raise ValueError("wall admission appears without a selected arm")
            selected = selection["selected_config_id"]
            if holdout_node_seen != holdout_node_schedule(holdout_names, selected):
                raise ValueError("wall admission precedes the repeated held-out node screen")
            wall_admission = record
            continue
        if record_type == "final":
            if selection is None:
                raise ValueError("final record precedes training selection")
            selected = selection.get("selected_config_id")
            if selected:
                if wall_admission is None:
                    raise ValueError("final record precedes held-out node admission")
                expected_wall = (
                    wall_holdout_schedule(holdout_names, selected)
                    if wall_admission.get("admitted")
                    else []
                )
                if wall_seen != expected_wall:
                    raise ValueError("final record precedes the production-wall gate")
            elif holdout_node_seen or wall_seen or wall_admission is not None:
                raise ValueError("unselected campaign contains held-out evidence")
            final_seen = True
            continue
        if record_type != "run":
            raise ValueError(f"unknown JSONL record type {record_type!r}")

        split = record.get("split")
        name = record.get("name")
        config_id = record.get("config_id")
        repetition = record.get("repetition")
        metric = record.get("metric")
        key = record.get("run_key")
        if not isinstance(repetition, int) or isinstance(repetition, bool):
            raise ValueError(f"run has invalid repetition: {key!r}")
        if key != run_key(
            str(split), str(name), str(config_id), repetition, str(metric)
        ):
            raise ValueError(f"run key disagrees with record fields: {key!r}")
        if key in seen_keys:
            raise ValueError(f"duplicate completed run key: {key}")
        seen_keys.add(key)

        if metric == NODE_METRIC and split == "train":
            if selection is not None:
                raise ValueError("training run appears after selection was sealed")
            training_seen.append((name, config_id, repetition))
            if training_seen != training_expected[: len(training_seen)]:
                raise ValueError(f"out-of-order training run {key}")
        elif metric == NODE_METRIC and split == "holdout":
            if selection is None or not selection.get("selected_config_id"):
                raise ValueError("held-out node run appears before training selection")
            if wall_admission is not None:
                raise ValueError("held-out node run appears after wall admission")
            selected = selection["selected_config_id"]
            holdout_node_seen.append((name, config_id, repetition))
            expected = holdout_node_schedule(holdout_names, selected)
            if holdout_node_seen != expected[: len(holdout_node_seen)]:
                raise ValueError(f"out-of-order held-out node run {key}")
        elif metric == WALL_METRIC and split == "holdout":
            if wall_admission is None or not wall_admission.get("admitted"):
                raise ValueError("production-wall run appears before node admission")
            selected = selection["selected_config_id"]
            wall_seen.append(
                (
                    name,
                    config_id,
                    repetition,
                    record.get("pair_order"),
                    record.get("order_position"),
                )
            )
            expected = wall_holdout_schedule(holdout_names, selected)
            if wall_seen != expected[: len(wall_seen)]:
                raise ValueError(f"out-of-order production-wall run {key}")
        else:
            raise ValueError(f"out-of-protocol run {key}")


def geometric_mean(values: list[float]) -> float | None:
    if not values:
        return None
    if any(value <= 0 or not math.isfinite(value) for value in values):
        raise ValueError("geometric mean requires finite positive values")
    return math.exp(sum(math.log(value) for value in values) / len(values))


def compare_to_baseline(
    names: list[str],
    baseline: dict[str, dict[str, Any]],
    candidate: dict[str, dict[str, Any]],
    *,
    require_strict: bool,
) -> dict[str, Any]:
    missing = [name for name in names if name not in baseline or name not in candidate]
    issues: list[str] = []
    regressions: list[dict[str, Any]] = []
    coverage_gains: list[str] = []
    node_gains: list[dict[str, Any]] = []
    ratios: list[float] = []
    solved_count = 0
    capped_total = 0
    for name in names:
        if name not in baseline or name not in candidate:
            continue
        base = baseline[name]["evaluation"]
        arm = candidate[name]["evaluation"]
        if not base.get("score_eligible"):
            issues.append(f"baseline evidence ineligible on {name}")
            continue
        if not arm.get("score_eligible"):
            issues.append(f"candidate evidence ineligible on {name}")
            continue
        base_solved = bool(base.get("solved"))
        arm_solved = bool(arm.get("solved"))
        base_nodes = base.get("nodes")
        arm_nodes = arm.get("nodes")
        if not isinstance(base_nodes, int) or not isinstance(arm_nodes, int):
            issues.append(f"missing nodes on {name}")
            continue
        capped_total += min(arm_nodes, int(arm["node_cap"]) + 1)
        solved_count += int(arm_solved)
        if base_solved and not arm_solved:
            regressions.append({"name": name, "kind": "lost-solve"})
            continue
        if arm_solved and not base_solved:
            coverage_gains.append(name)
            continue
        if base_solved and arm_solved:
            ratio = max(1, arm_nodes) / max(1, base_nodes)
            ratios.append(ratio)
            if arm_nodes > base_nodes:
                regressions.append(
                    {
                        "name": name,
                        "kind": "more-nodes",
                        "baseline_nodes": base_nodes,
                        "candidate_nodes": arm_nodes,
                    }
                )
            elif arm_nodes < base_nodes:
                node_gains.append(
                    {
                        "name": name,
                        "baseline_nodes": base_nodes,
                        "candidate_nodes": arm_nodes,
                    }
                )
    strict = bool(coverage_gains or node_gains)
    accepted = not missing and not issues and not regressions and (
        strict or not require_strict
    )
    return {
        "accepted": accepted,
        "require_strict_improvement": require_strict,
        "strict_improvement": strict,
        "missing": missing,
        "issues": issues,
        "regressions": regressions,
        "coverage_gains": coverage_gains,
        "node_gains": node_gains,
        "solved_count": solved_count,
        "geometric_mean_node_ratio": geometric_mean(ratios),
        "capped_node_total": capped_total,
    }


def compare_wall_to_baseline(
    names: list[str],
    baseline: dict[str, dict[str, Any]],
    candidate: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    missing = [name for name in names if name not in baseline or name not in candidate]
    issues: list[str] = []
    regressions: list[dict[str, Any]] = []
    coverage_gains: list[str] = []
    wall_gains: list[dict[str, Any]] = []
    rows = []
    for name in names:
        if name not in baseline or name not in candidate:
            continue
        base = baseline[name]["evaluation"]
        arm = candidate[name]["evaluation"]
        if not base.get("score_eligible"):
            issues.append(f"baseline wall evidence ineligible on {name}")
            continue
        if not arm.get("score_eligible"):
            issues.append(f"candidate wall evidence ineligible on {name}")
            continue
        base_solved = bool(base.get("solved"))
        arm_solved = bool(arm.get("solved"))
        base_wall = base.get("median_outer_wall_sec")
        arm_wall = arm.get("median_outer_wall_sec")
        rows.append(
            {
                "name": name,
                "baseline_solved": base_solved,
                "candidate_solved": arm_solved,
                "baseline_median_wall_sec": base_wall,
                "candidate_median_wall_sec": arm_wall,
            }
        )
        if base_solved and not arm_solved:
            regressions.append({"name": name, "kind": "lost-production-solve"})
            continue
        if arm_solved and not base_solved:
            coverage_gains.append(name)
            continue
        if base_solved and arm_solved:
            if not isinstance(base_wall, (int, float)) or not isinstance(
                arm_wall, (int, float)
            ):
                issues.append(f"missing production wall median on {name}")
            elif arm_wall > base_wall:
                regressions.append(
                    {
                        "name": name,
                        "kind": "slower-production-wall",
                        "baseline_median_wall_sec": base_wall,
                        "candidate_median_wall_sec": arm_wall,
                    }
                )
            elif base_wall - arm_wall >= max(
                WALL_STRICT_ABSOLUTE_GAIN_SEC,
                WALL_STRICT_RELATIVE_GAIN * base_wall,
            ):
                wall_gains.append(
                    {
                        "name": name,
                        "baseline_median_wall_sec": base_wall,
                        "candidate_median_wall_sec": arm_wall,
                    }
                )
    strict = bool(coverage_gains or wall_gains)
    return {
        "accepted": not missing and not issues and not regressions and strict,
        "strict_improvement": strict,
        "missing": missing,
        "issues": issues,
        "regressions": regressions,
        "coverage_gains": coverage_gains,
        "wall_gains": wall_gains,
        "cases": rows,
        "order_balance": "four repetitions: AB, BA, AB, BA; reversed corpus in passes 3-4",
        "strict_gain_threshold": {
            "relative": WALL_STRICT_RELATIVE_GAIN,
            "absolute_sec": WALL_STRICT_ABSOLUTE_GAIN_SEC,
        },
    }


def aggregate_repetitions(
    indexed: dict[str, dict[str, Any]],
    *,
    metric: str,
    split: str,
    name: str,
    config_id: str,
) -> dict[str, Any] | None:
    count = NODE_REPETITIONS if metric == NODE_METRIC else WALL_REPETITIONS
    keys = [run_key(split, name, config_id, rep, metric) for rep in range(count)]
    if any(key not in indexed for key in keys):
        return None
    runs = [indexed[key] for key in keys]
    evaluations = [run["evaluation"] for run in runs]
    issues = []
    for repetition, evaluation in enumerate(evaluations, 1):
        if not evaluation.get("score_eligible"):
            issues.append(f"repetition {repetition} is ineligible")
    signatures = [
        (
            evaluation.get("status"),
            bool(evaluation.get("solved")),
            evaluation.get("nodes") if metric == NODE_METRIC else None,
        )
        for evaluation in evaluations
    ]
    if any(signature != signatures[0] for signature in signatures[1:]):
        issues.append(
            "repetitions changed status, solvedness, or node count: "
            + repr(signatures)
        )

    if metric == NODE_METRIC:
        aggregate = dict(evaluations[0])
        aggregate["score_eligible"] = not issues
        aggregate["replication_issues"] = issues
        aggregate["repetition_count"] = count
    else:
        walls = [evaluation.get("outer_wall_sec") for evaluation in evaluations]
        if any(
            not isinstance(wall, (int, float))
            or isinstance(wall, bool)
            or not math.isfinite(float(wall))
            or wall < 0
            for wall in walls
        ):
            issues.append("repetitions have missing/non-finite solver wall time")
        aggregate = {
            "status": evaluations[0].get("status"),
            "solved": bool(evaluations[0].get("solved")),
            "score_eligible": not issues,
            "replication_issues": issues,
            "repetition_count": count,
            "outer_wall_samples_sec": walls,
            "median_outer_wall_sec": (
                statistics.median(float(wall) for wall in walls)
                if not any("wall time" in issue for issue in issues)
                else None
            ),
        }
    return {"evaluation": aggregate, "replicate_keys": keys}


def split_records(
    indexed: dict[str, dict[str, Any]],
    metric: str,
    split: str,
    names: list[str],
    config_id: str,
) -> dict[str, dict[str, Any]]:
    aggregated = {}
    for name in names:
        record = aggregate_repetitions(
            indexed,
            metric=metric,
            split=split,
            name=name,
            config_id=config_id,
        )
        if record is not None:
            aggregated[name] = record
    return aggregated


def training_selection(
    indexed: dict[str, dict[str, Any]], train_names: list[str]
) -> dict[str, Any]:
    baseline = split_records(
        indexed, NODE_METRIC, "train", train_names, BASELINE_ID
    )
    default_replica = split_records(
        indexed,
        NODE_METRIC,
        "train",
        train_names,
        DEFAULT_GRID_CONFIG.config_id,
    )
    baseline_issues = []
    for name in train_names:
        if name not in baseline:
            baseline_issues.append(f"missing baseline run on {name}")
        elif not baseline[name]["evaluation"].get("score_eligible"):
            baseline_issues.append(f"baseline evidence ineligible on {name}")
    replica_issues = []
    for name in train_names:
        if name not in baseline or name not in default_replica:
            replica_issues.append(f"missing default determinism pair on {name}")
            continue
        left = baseline[name]["evaluation"]
        right = default_replica[name]["evaluation"]
        for field in ("status", "solved", "nodes"):
            if left.get(field) != right.get(field):
                replica_issues.append(
                    f"identical default changed {field} on {name}: "
                    f"{left.get(field)!r} != {right.get(field)!r}"
                )

    candidates = []
    for config in GRID:
        runs = split_records(
            indexed, NODE_METRIC, "train", train_names, config.config_id
        )
        comparison = compare_to_baseline(
            train_names, baseline, runs, require_strict=True
        )
        candidates.append(
            {
                "config_id": config.config_id,
                "coordinates": config.coordinate_dict(),
                "environment": config.env_dict(),
                "comparison": comparison,
            }
        )
    admissible = [row for row in candidates if row["comparison"]["accepted"]]

    def rank(row: dict[str, Any]) -> tuple[Any, ...]:
        comparison = row["comparison"]
        ratio = comparison["geometric_mean_node_ratio"]
        return (
            -comparison["solved_count"],
            math.inf if ratio is None else ratio,
            comparison["capped_node_total"],
            row["config_id"],
        )

    admissible.sort(key=rank)
    selected = (
        None
        if baseline_issues or replica_issues or not admissible
        else admissible[0]["config_id"]
    )
    return {
        "selected_config_id": selected,
        "selection_basis": "training-only",
        "grid_size": len(GRID),
        "baseline_issues": baseline_issues,
        "default_replication_issues": replica_issues,
        "admissible_count": len(admissible),
        "admissible_ranking": [row["config_id"] for row in admissible],
        "candidates": candidates,
    }


def soundness_alarms(records: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    alarms = []
    for record in records:
        if record.get("type") != "run":
            continue
        wrong = (record.get("evaluation") or {}).get("wrong_issues") or []
        if wrong:
            alarms.append({"run_key": record.get("run_key"), "issues": wrong})
    return alarms


def ineligible_run_records(
    records: Iterable[dict[str, Any]], metric: str | None = None
) -> list[dict[str, Any]]:
    return [
        {
            "run_key": record.get("run_key"),
            "invalid_issues": (record.get("evaluation") or {}).get(
                "invalid_issues", []
            ),
            "node_gate_issues": (record.get("evaluation") or {}).get(
                "node_gate_issues", []
            ),
        }
        for record in records
        if record.get("type") == "run"
        and (metric is None or record.get("metric") == metric)
        and not (record.get("evaluation") or {}).get("score_eligible")
    ]


def replication_issues_for(
    indexed: dict[str, dict[str, Any]],
    *,
    metric: str,
    split: str,
    names: list[str],
    config_ids: Iterable[str],
) -> list[dict[str, Any]]:
    issues = []
    for config_id in config_ids:
        for name in names:
            aggregate = aggregate_repetitions(
                indexed,
                metric=metric,
                split=split,
                name=name,
                config_id=config_id,
            )
            if aggregate is None:
                issues.append(
                    {
                        "metric": metric,
                        "split": split,
                        "name": name,
                        "config_id": config_id,
                        "issues": ["missing repetition"],
                    }
                )
                continue
            repeated = aggregate["evaluation"].get("replication_issues") or []
            if repeated:
                issues.append(
                    {
                        "metric": metric,
                        "split": split,
                        "name": name,
                        "config_id": config_id,
                        "issues": repeated,
                    }
                )
    return issues


def run_node_screen_ay(
    ay_binary: Path,
    model: Path,
    seed: int,
    hard_timeout: float,
    plan: Any,
    env: dict[str, str],
    env_posture: dict[str, Any],
    case_dir: Path,
    artifact_root: Path,
) -> dict[str, Any]:
    """Run node screening with no solver-internal wall deadline.

    The outer guarded timeout remains a hard safety envelope.  Removing only
    ``--time-limit`` prevents presolve/cut deadline shares from changing the
    model/tree under machine load; an arm that cannot hit its node cap before
    the outer timeout is invalid evidence rather than a partial score.
    """

    run_dir = case_dir / "ay"
    certificate = run_dir / "result.ayc"
    witness = run_dir / "result.sol"
    command = evidence.build_ay_command(
        ay_binary, model, hard_timeout, seed, certificate, witness
    )
    time_index = command.index("--time-limit")
    del command[time_index : time_index + 2]
    process = evidence.run_guarded_capture(
        command,
        memlimit_mb=plan.memlimit_mb,
        timeout_sec=hard_timeout,
        label="milp_joint_search.py[node-screen]",
        env=env,
        env_posture=env_posture,
        artifact_dir=run_dir,
        artifact_root=artifact_root,
    )
    verdict, parse_error = evidence.parse_process_json(process, artifact_root)
    return {
        "process": process,
        "verdict": verdict,
        "parse_error": parse_error,
        "certificate": evidence.artifact_identity(certificate, artifact_root),
        "witness": evidence.artifact_identity(witness, artifact_root),
    }


def run_one(
    *,
    metric: str,
    split: str,
    repetition: int,
    item: dict[str, Any],
    reference: dict[str, Any],
    model_identity: dict[str, Any],
    config_id: str,
    config_env: dict[str, str],
    ay_binary: Path,
    node_cap: int,
    solver_limit: float,
    hard_grace: float,
    checker_limit: float,
    plan: Any,
    artifact_root: Path,
    source_environment: dict[str, str],
    pair_order: str | None = None,
    order_position: int | None = None,
) -> dict[str, Any]:
    key = run_key(split, item["name"], config_id, repetition, metric)
    model = item["model_path"]
    current_identity = evidence.file_identity(model)
    if current_identity["sha256"] != model_identity["sha256"]:
        raise RuntimeError(f"benchmark input changed during campaign: {model}")
    case_dir = next_attempt_dir(artifact_root, key)
    env, env_posture = configured_environment(
        source_environment,
        config_env,
        node_cap if metric == NODE_METRIC else None,
        metric,
    )
    result = (
        run_node_screen_ay(
            ay_binary,
            model,
            evidence.SOLVER_SEED,
            solver_limit + hard_grace,
            plan,
            env,
            env_posture,
            case_dir,
            artifact_root,
        )
        if metric == NODE_METRIC
        else evidence.run_ay(
            ay_binary,
            model,
            solver_limit,
            evidence.SOLVER_SEED,
            solver_limit + hard_grace,
            plan,
            env,
            env_posture,
            case_dir,
            artifact_root,
        )
    )
    evidence.check_ay_evidence(
        ay_binary,
        model,
        result,
        plan,
        checker_limit,
        env,
        env_posture,
        case_dir,
        artifact_root,
    )
    evaluation = (
        evaluate_node_run(
            result,
            reference,
            model_identity["sense"],
            node_cap,
            inspect_node_trace(result, artifact_root),
        )
        if metric == NODE_METRIC
        else evaluate_wall_run(result, reference, model_identity["sense"])
    )
    return {
        "type": "run",
        "schema": SCHEMA,
        "completed_at": utc_now(),
        "run_key": key,
        "metric": metric,
        "split": split,
        "repetition": repetition,
        "name": item["name"],
        "config_id": config_id,
        "configuration_environment": dict(sorted(config_env.items())),
        "model_sha256": model_identity["sha256"],
        "reference": reference,
        "pair_order": pair_order,
        "order_position": order_position,
        "result": result,
        "evaluation": evaluation,
    }


def header_posture(args: argparse.Namespace) -> dict[str, Any]:
    return {
        "node_cap": args.node_cap,
        "node_screen_internal_time_limit": None,
        "node_screen_outer_safety_timeout_sec": (
            args.time_limit + args.hard_timeout_grace
        ),
        "production_wall_internal_time_limit_sec": args.time_limit,
        "outer_hard_timeout_sec": args.time_limit + args.hard_timeout_grace,
        "checker_timeout_sec": args.checker_timeout,
        "threads": 1,
        "seed": evidence.SOLVER_SEED,
        "solver_determinism_requested": True,
        "serial": True,
        "node_repetitions_per_case_arm": NODE_REPETITIONS,
        "production_wall_repetitions_per_case_arm": WALL_REPETITIONS,
        "node_screen_trace": "AY_MILP_TRACE=1; recognized root deadline truncation rejects",
        "production_wall_order": "four AB/BA passes; two starts per arm",
        "production_wall_strict_gain": {
            "relative": WALL_STRICT_RELATIVE_GAIN,
            "absolute_sec": WALL_STRICT_ABSOLUTE_GAIN_SEC,
        },
        "score": (
            "training solved-count descending, geometric-mean repeated-node "
            "ratio ascending, capped-node total ascending, config id"
        ),
        "train_acceptance": "no lost solves; no per-case node regression; strict gain",
        "holdout_acceptance": "same no-regression gate plus strict held-out gain",
        "unsolved_eligibility": "each repetition must reach AY_MILP_MAX_NODES",
        "replication_eligibility": (
            "all node repetitions exact-match status/solved/nodes; all wall "
            "repetitions exact-match status/solved"
        ),
        "terminal_evidence": (
            "exact point check; reference status/objective; independently checked "
            "infeasibility/unbounded certificate"
        ),
    }


def resource_record(plan: Any) -> dict[str, Any]:
    return {
        "requested_jobs": 1,
        "jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "memory_enforcement": "process-group rss_watchdog",
        "rss_grace_mb": 0,
        "lease": "one process-scoped host lease for complete campaign invocation",
    }


def prepare_cases(
    train_names: list[str],
    holdout_names: list[str],
    manifest_path: Path,
    solu_path: Path,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any], list[dict[str, Any]]]:
    all_names = train_names + holdout_names
    _, references, prepared = evidence.preflight_cases(
        all_names, manifest_path, solu_path
    )
    instance_records = []
    for item in prepared:
        identity = evidence.file_identity(item["model_path"])
        identity["name"] = item["name"]
        identity["sense"] = evidence.mps_sense(item["model_path"])
        identity["reference"] = references[item["name"]]
        identity["manifest"] = {
            key: item["manifest_entry"].get(key)
            for key in (
                "tier",
                "ref_status",
                "ref_obj",
                "rows",
                "cols",
                "nnz",
                "ints",
                "bins",
            )
        }
        instance_records.append(identity)
    return references, {item["name"]: item for item in prepared}, instance_records


def new_header(
    *,
    args: argparse.Namespace,
    train_path: Path,
    holdout_path: Path,
    train_names: list[str],
    holdout_names: list[str],
    manifest_path: Path,
    solu_path: Path,
    instance_records: list[dict[str, Any]],
    plan: Any,
    binary_identity: dict[str, Any],
    git_identity: dict[str, Any],
    environment_protocol: dict[str, Any],
) -> dict[str, Any]:
    return {
        "type": "header",
        "schema": SCHEMA,
        "created_at": utc_now(),
        "state": "running",
        "selection_protocol": {
            "train": train_names,
            "holdout": holdout_names,
            "holdout_runs_permitted_only_after_selection_record": True,
            "one_training_selected_configuration": True,
            "node_repetitions": NODE_REPETITIONS,
            "production_wall_repetitions": WALL_REPETITIONS,
            "production_wall_requires_node_admission": True,
        },
        "grid": {
            "coordinate_count": len(COORDINATES),
            "coordinate_sizes": {name: len(values) for name, values in COORDINATES},
            "configuration_count": len(GRID),
            "sha256": GRID_SHA256,
            "configurations": serialized_grid(),
        },
        "posture": header_posture(args),
        "environment_protocol": environment_protocol,
        "resource_envelope": resource_record(plan),
        "instances": instance_records,
        "provenance": {
            "harness": evidence.file_identity(Path(__file__)),
            "evidence_harness": evidence.file_identity(
                SCRIPT_DIR / "ay_gurobi_closure.py"
            ),
            "oom_guard": evidence.file_identity(SCRIPT_DIR / "_oom_guard.py"),
            "train_list": evidence.file_identity(train_path),
            "holdout_list": evidence.file_identity(holdout_path),
            "manifest": evidence.file_identity(manifest_path),
            "solution_reference": evidence.file_identity(solu_path),
            "ay_binary": binary_identity,
            "git": git_identity,
            "host": host_record(),
            "invocation": [str(Path(__file__).resolve()), *sys.argv[1:]],
        },
    }


def validate_resume(
    *,
    header: dict[str, Any],
    args: argparse.Namespace,
    train_path: Path,
    holdout_path: Path,
    train_names: list[str],
    holdout_names: list[str],
    manifest_path: Path,
    solu_path: Path,
    instance_records: list[dict[str, Any]],
    plan: Any,
    artifact_root: Path,
    environment_protocol: dict[str, Any],
) -> Path:
    if header.get("schema") != SCHEMA:
        raise ValueError(f"cannot resume schema {header.get('schema')!r}")
    expected = {
        "train": train_names,
        "holdout": holdout_names,
        "holdout_runs_permitted_only_after_selection_record": True,
        "one_training_selected_configuration": True,
        "node_repetitions": NODE_REPETITIONS,
        "production_wall_repetitions": WALL_REPETITIONS,
        "production_wall_requires_node_admission": True,
    }
    if header.get("selection_protocol") != expected:
        raise ValueError("split membership/protocol changed since campaign creation")
    if header.get("grid", {}).get("sha256") != GRID_SHA256:
        raise ValueError("joint grid changed since campaign creation")
    if header.get("posture") != header_posture(args):
        raise ValueError("node/time/evidence posture changed since campaign creation")
    if header.get("resource_envelope") != resource_record(plan):
        raise ValueError("resource envelope changed; runs would not be comparable")
    if header.get("environment_protocol") != environment_protocol:
        raise ValueError("effective environment changed; runs would not be comparable")
    provenance = header.get("provenance") or {}
    if provenance.get("host") != host_record():
        raise ValueError("host identity changed; repeated-node runs are not comparable")
    current_files = {
        "harness": Path(__file__),
        "evidence_harness": SCRIPT_DIR / "ay_gurobi_closure.py",
        "oom_guard": SCRIPT_DIR / "_oom_guard.py",
        "train_list": train_path,
        "holdout_list": holdout_path,
        "manifest": manifest_path,
        "solution_reference": solu_path,
    }
    for label, path in current_files.items():
        recorded = (provenance.get(label) or {}).get("sha256")
        if recorded != evidence.sha256_file(path):
            raise ValueError(f"{label} changed since campaign creation")
    recorded_instances = {
        item["name"]: item["sha256"] for item in header.get("instances", [])
    }
    current_instances = {item["name"]: item["sha256"] for item in instance_records}
    if recorded_instances != current_instances:
        raise ValueError("benchmark input bytes changed since campaign creation")
    frozen = provenance.get("ay_binary", {}).get("frozen") or {}
    frozen_path = Path(frozen.get("path", ""))
    if not frozen_path.is_file() or evidence.sha256_file(frozen_path) != frozen.get("sha256"):
        raise ValueError("frozen AY binary is missing or changed")
    try:
        frozen_path.relative_to(artifact_root)
    except ValueError as error:
        raise ValueError("recorded frozen binary is outside campaign artifacts") from error
    return frozen_path


def default_output_path() -> Path:
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    return REPO_ROOT / "evals" / "results" / "milp-joint-search" / f"{stamp}.jsonl"


def selection_record(selection: dict[str, Any]) -> dict[str, Any]:
    return {
        "type": "selection",
        "schema": SCHEMA,
        "selected_at": utc_now(),
        **selection,
    }


def find_single_record(
    records: list[dict[str, Any]], record_type: str
) -> dict[str, Any] | None:
    matching = [record for record in records if record.get("type") == record_type]
    if len(matching) > 1:
        raise ValueError(f"multiple {record_type} records in campaign")
    return matching[0] if matching else None


def wall_admission_record(
    records: list[dict[str, Any]],
    indexed: dict[str, dict[str, Any]],
    selection: dict[str, Any],
    train_names: list[str],
    holdout_names: list[str],
) -> dict[str, Any]:
    selected = selection.get("selected_config_id")
    if not selected:
        raise ValueError("cannot admit production wall without a selected arm")
    node_holdout = compare_to_baseline(
        holdout_names,
        split_records(
            indexed, NODE_METRIC, "holdout", holdout_names, BASELINE_ID
        ),
        split_records(indexed, NODE_METRIC, "holdout", holdout_names, selected),
        require_strict=True,
    )
    training_replication = replication_issues_for(
        indexed,
        metric=NODE_METRIC,
        split="train",
        names=train_names,
        config_ids=[BASELINE_ID, *(config.config_id for config in GRID)],
    )
    holdout_replication = replication_issues_for(
        indexed,
        metric=NODE_METRIC,
        split="holdout",
        names=holdout_names,
        config_ids=(BASELINE_ID, selected),
    )
    ineligible = ineligible_run_records(records, NODE_METRIC)
    alarms = soundness_alarms(
        record
        for record in records
        if record.get("type") != "run" or record.get("metric") == NODE_METRIC
    )
    return {
        "type": "wall-admission",
        "schema": SCHEMA,
        "admitted_at": utc_now(),
        "selected_config_id": selected,
        "node_holdout": node_holdout,
        "training_replication_issues": training_replication,
        "holdout_replication_issues": holdout_replication,
        "node_ineligible_runs": ineligible,
        "soundness_alarms": alarms,
        "admitted": bool(
            node_holdout["accepted"]
            and not training_replication
            and not holdout_replication
            and not ineligible
            and not alarms
        ),
    }


def final_summary(
    records: list[dict[str, Any]],
    indexed: dict[str, dict[str, Any]],
    selection: dict[str, Any],
    wall_admission: dict[str, Any] | None,
    train_names: list[str],
    holdout_names: list[str],
) -> dict[str, Any]:
    selected = selection.get("selected_config_id")
    node_holdout = wall_admission.get("node_holdout") if wall_admission else None
    wall_holdout = None
    if selected and wall_admission and wall_admission.get("admitted"):
        wall_holdout = compare_wall_to_baseline(
            holdout_names,
            split_records(
                indexed, WALL_METRIC, "holdout", holdout_names, BASELINE_ID
            ),
            split_records(
                indexed, WALL_METRIC, "holdout", holdout_names, selected
            ),
        )
    alarms = soundness_alarms(records)
    ineligible_runs = ineligible_run_records(records)
    replication_issues = replication_issues_for(
        indexed,
        metric=NODE_METRIC,
        split="train",
        names=train_names,
        config_ids=[BASELINE_ID, *(config.config_id for config in GRID)],
    )
    if selected and wall_admission:
        replication_issues.extend(
            replication_issues_for(
                indexed,
                metric=NODE_METRIC,
                split="holdout",
                names=holdout_names,
                config_ids=(BASELINE_ID, selected),
            )
        )
        if wall_admission.get("admitted"):
            replication_issues.extend(
                replication_issues_for(
                    indexed,
                    metric=WALL_METRIC,
                    split="holdout",
                    names=holdout_names,
                    config_ids=(BASELINE_ID, selected),
                )
            )
    return {
        "type": "final",
        "schema": SCHEMA,
        "finished_at": utc_now(),
        "selected_config_id": selected,
        "training_baseline_issues": selection.get("baseline_issues", []),
        "training_default_replication_issues": selection.get(
            "default_replication_issues", []
        ),
        "node_holdout": node_holdout,
        "production_wall_holdout": wall_holdout,
        "wall_admitted": bool(wall_admission and wall_admission.get("admitted")),
        "soundness_alarms": alarms,
        "ineligible_runs": ineligible_runs,
        "replication_issues": replication_issues,
        "accepted": bool(
            selected
            and node_holdout
            and node_holdout["accepted"]
            and wall_holdout
            and wall_holdout["accepted"]
            and not alarms
            and not ineligible_runs
            and not replication_issues
        ),
    }


def final_exit_code(final: dict[str, Any]) -> int:
    if final.get("soundness_alarms"):
        return 3
    if final.get("ineligible_runs") or final.get("replication_issues"):
        return 2
    if final.get("training_baseline_issues") or final.get(
        "training_default_replication_issues"
    ):
        return 2
    node_holdout = final.get("node_holdout")
    wall_holdout = final.get("production_wall_holdout")
    if final.get("selected_config_id") and (
        node_holdout is None
        or node_holdout.get("missing")
        or node_holdout.get("issues")
        or (final.get("wall_admitted") and wall_holdout is None)
        or (wall_holdout and (wall_holdout.get("missing") or wall_holdout.get("issues")))
    ):
        return 2
    return 0 if final.get("accepted") else 1


def validate_derived_records(
    records: list[dict[str, Any]], train_names: list[str], holdout_names: list[str]
) -> None:
    indexed = index_records(records)
    recorded_selection = find_single_record(records, "selection")
    if recorded_selection is None:
        return
    computed_selection = training_selection(indexed, train_names)
    persisted_selection = {
        key: recorded_selection.get(key) for key in computed_selection
    }
    if persisted_selection != computed_selection:
        raise ValueError("persisted training selection disagrees with recomputation")
    recorded_admission = find_single_record(records, "wall-admission")
    if recorded_selection.get("selected_config_id"):
        if recorded_admission is None:
            return
        computed_admission = wall_admission_record(
            records, indexed, recorded_selection, train_names, holdout_names
        )
        comparable_recorded_admission = dict(recorded_admission)
        comparable_computed_admission = dict(computed_admission)
        comparable_recorded_admission.pop("admitted_at", None)
        comparable_computed_admission.pop("admitted_at", None)
        if comparable_recorded_admission != comparable_computed_admission:
            raise ValueError("persisted wall admission disagrees with recomputation")
    elif recorded_admission is not None:
        raise ValueError("wall admission exists without a selected arm")
    recorded_final = find_single_record(records, "final")
    if recorded_final is None:
        return
    computed_final = final_summary(
        records,
        indexed,
        recorded_selection,
        recorded_admission,
        train_names,
        holdout_names,
    )
    comparable_recorded = dict(recorded_final)
    comparable_computed = dict(computed_final)
    comparable_recorded.pop("finished_at", None)
    comparable_computed.pop("finished_at", None)
    if comparable_recorded != comparable_computed:
        raise ValueError("persisted final summary disagrees with recomputation")


def print_final(final: dict[str, Any]) -> None:
    node_holdout = final.get("node_holdout") or {}
    wall_holdout = final.get("production_wall_holdout") or {}
    print(
        f"selected={final.get('selected_config_id') or '-'} "
        f"accepted={bool(final.get('accepted'))} "
        f"node_gains={len(node_holdout.get('coverage_gains', [])) + len(node_holdout.get('node_gains', []))} "
        f"wall_gains={len(wall_holdout.get('coverage_gains', [])) + len(wall_holdout.get('wall_gains', []))} "
        f"regressions={len(node_holdout.get('regressions', [])) + len(wall_holdout.get('regressions', []))} "
        f"soundness_alarms={len(final.get('soundness_alarms', []))} "
        f"ineligible_runs={len(final.get('ineligible_runs', []))} "
        f"replication_issues={len(final.get('replication_issues', []))}",
        flush=True,
    )


def cmd_describe(_args: argparse.Namespace) -> int:
    train, holdout = load_splits(TRAIN_LIST, HOLDOUT_LIST)
    print(
        json.dumps(
            {
                "schema": SCHEMA,
                "train": train,
                "holdout": holdout,
                "coordinate_sizes": {name: len(values) for name, values in COORDINATES},
                "grid_size": len(GRID),
                "grid_sha256": GRID_SHA256,
                "default_node_cap": DEFAULT_NODE_CAP,
                "node_repetitions": NODE_REPETITIONS,
                "production_wall_repetitions": WALL_REPETITIONS,
                "search_metric": "repeated exact-match node counts",
                "acceptance_gate": "separate order-balanced production wall",
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


def cmd_analyze(args: argparse.Namespace) -> int:
    path = args.result.expanduser().resolve(strict=True)
    artifact_root = path.with_name(f"{path.stem}.artifacts")
    if not artifact_root.is_dir():
        raise ValueError(f"campaign artifact directory is missing: {artifact_root}")
    records = load_jsonl(path)
    protocol = records[0].get("selection_protocol") or {}
    train_names = protocol.get("train")
    holdout_names = protocol.get("holdout")
    if not isinstance(train_names, list) or not isinstance(holdout_names, list):
        raise ValueError("header does not contain frozen train/holdout lists")
    validate_campaign_provenance(records[0], artifact_root)
    validate_record_protocol(records, train_names, holdout_names)
    validate_run_semantics(records, records[0], artifact_root)
    validate_derived_records(records, train_names, holdout_names)
    final = find_single_record(records, "final")
    if final is None:
        selection = find_single_record(records, "selection")
        print(
            f"campaign incomplete: runs={len(index_records(records))} "
            f"selection={'yes' if selection else 'no'}"
        )
        return 2
    print_final(final)
    if args.json:
        print(json.dumps(final, indent=2, sort_keys=True, allow_nan=False))
    return final_exit_code(final)


def cmd_run(args: argparse.Namespace) -> int:
    output = (args.out or default_output_path()).expanduser().resolve()
    artifact_root = output.with_name(f"{output.stem}.artifacts")
    train_path = args.train_list.expanduser().resolve(strict=True)
    holdout_path = args.holdout_list.expanduser().resolve(strict=True)
    manifest_path = args.manifest.expanduser().resolve(strict=True)
    solu_path = args.solu.expanduser().resolve(strict=True)
    train_names, holdout_names = load_splits(train_path, holdout_path)
    references, prepared_by_name, instance_records = prepare_cases(
        train_names, holdout_names, manifest_path, solu_path
    )
    model_by_name = {item["name"]: item for item in instance_records}
    source_environment = dict(os.environ)
    environment_protocol = campaign_environment_protocol(
        source_environment, args.node_cap
    )

    warn_concurrent_build()
    plan = plan_solver_resources(1, label="milp_joint_search.py")
    if plan.jobs != 1:
        raise RuntimeError(f"serial search received a non-serial plan: {plan}")

    if output.exists():
        if not args.resume:
            raise ValueError(f"output exists; pass --resume to continue: {output}")
        if not artifact_root.is_dir():
            raise ValueError(f"campaign artifact directory is missing: {artifact_root}")
        records = load_jsonl(output, repair_trailing=True)
        validate_record_protocol(records, train_names, holdout_names)
        header = records[0]
        ay_binary = validate_resume(
            header=header,
            args=args,
            train_path=train_path,
            holdout_path=holdout_path,
            train_names=train_names,
            holdout_names=holdout_names,
            manifest_path=manifest_path,
            solu_path=solu_path,
            instance_records=instance_records,
            plan=plan,
            artifact_root=artifact_root,
            environment_protocol=environment_protocol,
        )
        validate_campaign_provenance(header, artifact_root)
        validate_run_semantics(records, header, artifact_root)
        validate_derived_records(records, train_names, holdout_names)
    else:
        if args.resume:
            raise ValueError(f"--resume requested but output does not exist: {output}")
        if artifact_root.exists():
            raise ValueError(f"refusing pre-existing artifact directory: {artifact_root}")
        output.parent.mkdir(parents=True, exist_ok=True)
        git_identity = evidence.git_provenance(REPO_ROOT)
        artifact_root.mkdir(parents=True)
        frozen_path = artifact_root / "bin" / "ay-milp"
        binary_identity = evidence.freeze_binary(
            args.ay_bin.expanduser().resolve(strict=True), frozen_path
        )
        ay_binary = Path(binary_identity["frozen"]["path"])
        header = new_header(
            args=args,
            train_path=train_path,
            holdout_path=holdout_path,
            train_names=train_names,
            holdout_names=holdout_names,
            manifest_path=manifest_path,
            solu_path=solu_path,
            instance_records=instance_records,
            plan=plan,
            binary_identity=binary_identity,
            git_identity=git_identity,
            environment_protocol=environment_protocol,
        )
        append_jsonl(output, header, exclusive=True)
        records = [header]

    already_final = find_single_record(records, "final")
    if already_final is not None:
        print_final(already_final)
        return final_exit_code(already_final)

    indexed = index_records(records)

    def ensure_run(
        metric: str,
        split: str,
        name: str,
        config_id: str,
        repetition: int,
        *,
        pair_order: str | None = None,
        order_position: int | None = None,
    ) -> None:
        key = run_key(split, name, config_id, repetition, metric)
        if key in indexed:
            return
        print(
            f"[{len(indexed) + 1}] {metric} {split} rep={repetition + 1} "
            f"{name} {config_id}",
            flush=True,
        )
        record = run_one(
            metric=metric,
            split=split,
            repetition=repetition,
            item=prepared_by_name[name],
            reference=references[name],
            model_identity=model_by_name[name],
            config_id=config_id,
            config_env=config_environment(config_id),
            ay_binary=ay_binary,
            node_cap=args.node_cap,
            solver_limit=args.time_limit,
            hard_grace=args.hard_timeout_grace,
            checker_limit=args.checker_timeout,
            plan=plan,
            artifact_root=artifact_root,
            source_environment=source_environment,
            pair_order=pair_order,
            order_position=order_position,
        )
        append_jsonl(output, record)
        records.append(record)
        indexed[key] = record
        evaluation = record["evaluation"]
        detail = (
            f"nodes={evaluation['nodes']}"
            if metric == NODE_METRIC
            else f"wall={evaluation['outer_wall_sec']:.6f}s"
        )
        print(
            f"  status={evaluation['status']} {detail} "
            f"solved={evaluation['solved']} eligible={evaluation['score_eligible']}",
            flush=True,
        )

    # Three full passes separate every arm's repetitions. No held-out run is
    # launched until the one training winner has been durably persisted.
    for name, config_id, repetition in training_node_schedule(train_names):
        ensure_run(NODE_METRIC, "train", name, config_id, repetition)

    computed_selection = training_selection(indexed, train_names)
    recorded_selection = find_single_record(records, "selection")
    if recorded_selection is None:
        recorded_selection = selection_record(computed_selection)
        append_jsonl(output, recorded_selection)
        records.append(recorded_selection)
    else:
        persisted_selection = {
            key: recorded_selection.get(key) for key in computed_selection
        }
        if persisted_selection != computed_selection:
            raise ValueError("persisted training selection disagrees with recomputation")

    selected = recorded_selection.get("selected_config_id")
    recorded_admission = find_single_record(records, "wall-admission")
    if selected:
        for name, config_id, repetition in holdout_node_schedule(
            holdout_names, selected
        ):
            ensure_run(NODE_METRIC, "holdout", name, config_id, repetition)
        computed_admission = wall_admission_record(
            records, indexed, recorded_selection, train_names, holdout_names
        )
        if recorded_admission is None:
            recorded_admission = computed_admission
            append_jsonl(output, recorded_admission)
            records.append(recorded_admission)
        else:
            persisted = dict(recorded_admission)
            computed = dict(computed_admission)
            persisted.pop("admitted_at", None)
            computed.pop("admitted_at", None)
            if persisted != computed:
                raise ValueError("persisted wall admission disagrees with recomputation")
        if recorded_admission.get("admitted"):
            for name, config_id, repetition, pair_order, position in wall_holdout_schedule(
                holdout_names, selected
            ):
                ensure_run(
                    WALL_METRIC,
                    "holdout",
                    name,
                    config_id,
                    repetition,
                    pair_order=pair_order,
                    order_position=position,
                )

    final = final_summary(
        records,
        indexed,
        recorded_selection,
        recorded_admission,
        train_names,
        holdout_names,
    )
    append_jsonl(output, final)
    print(f"wrote {output}", flush=True)
    print_final(final)
    return final_exit_code(final)


def positive_float(parser: argparse.ArgumentParser, name: str, value: float) -> None:
    if not math.isfinite(value) or value <= 0:
        parser.error(f"--{name} must be finite and positive")


def build_parser() -> argparse.ArgumentParser:
    bench_root = evidence.default_bench_root()
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    sub = parser.add_subparsers(dest="command", required=True)
    describe = sub.add_parser("describe", help="print the frozen split/grid without running")
    describe.set_defaults(fn=cmd_describe)

    analyze = sub.add_parser("analyze", help="summarize an existing JSONL campaign")
    analyze.add_argument("result", type=Path)
    analyze.add_argument("--json", action="store_true")
    analyze.set_defaults(fn=cmd_analyze)

    run = sub.add_parser("run", help="run or resume the preregistered search")
    run.add_argument("--out", type=Path, default=None)
    run.add_argument("--resume", action="store_true")
    run.add_argument("--train-list", type=Path, default=TRAIN_LIST)
    run.add_argument("--holdout-list", type=Path, default=HOLDOUT_LIST)
    run.add_argument("--manifest", type=Path, default=bench_root / "manifest.json")
    run.add_argument(
        "--solu", type=Path, default=bench_root / "meta" / "miplib2017-v27.solu"
    )
    run.add_argument("--ay-bin", type=Path, default=DEFAULT_AY_BIN)
    run.add_argument("--node-cap", type=int, default=DEFAULT_NODE_CAP)
    run.add_argument("--time-limit", type=float, default=DEFAULT_SOLVER_LIMIT_SEC)
    run.add_argument("--hard-timeout-grace", type=float, default=DEFAULT_HARD_GRACE_SEC)
    run.add_argument("--checker-timeout", type=float, default=DEFAULT_CHECKER_LIMIT_SEC)
    run.set_defaults(fn=cmd_run)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.command == "run":
        if args.node_cap <= 0:
            parser.error("--node-cap must be positive")
        positive_float(parser, "time-limit", args.time_limit)
        positive_float(parser, "hard-timeout-grace", args.hard_timeout_grace)
        positive_float(parser, "checker-timeout", args.checker_timeout)
    try:
        return args.fn(args)
    except (OSError, RuntimeError, ValueError) as error:
        print(f"milp_joint_search.py: {type(error).__name__}: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
