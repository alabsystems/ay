#!/usr/bin/env python3
# ay-script: ay-gurobi-closure
"""Serial, evidence-gated AY-vs-Gurobi closure benchmark.

This is the authoritative rebaseline driver for the historical 101-instance
set on which Gurobi was known to beat AY.  It intentionally does less than a
general benchmark framework and makes the load-bearing posture difficult to
misstate:

* one host-wide :mod:`_oom_guard` lease and one guarded child at a time;
* a frozen copy of the production ``ay-milp`` binary, never the old example;
* AY and Gurobi at one thread, seed zero, zero Gurobi MIP gaps;
* exact AY point checking and independent AY certificate checking;
* Gurobi solution export followed by AY's exact point checker;
* raw outputs, binary/input hashes, git dirty identity, and resource envelope;
* a non-zero exit while any selected case remains a known Gurobi advantage.

Examples::

    scripts/ay_gurobi_closure.py --only first-panel --timeout 60
    scripts/ay_gurobi_closure.py --case rout --timeout 60 --repetitions 4
    scripts/ay_gurobi_closure.py --timeout 60 --repetitions 3 --out run.json

Exit codes are 0 for closed dominance, 1 for a measured Gurobi advantage,
2 for an incomplete campaign, and 3 for invalid or reference-disagreeing
evidence.  Solver and checker children are never run during module import.
"""

from __future__ import annotations

import argparse
import collections
import dataclasses
import datetime as dt
import gzip
import hashlib
import json
import math
import os
import platform
import re
import shutil
import statistics
import subprocess
import sys
import traceback
from fractions import Fraction
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
CASE_LIST_PATH = SCRIPT_DIR / "data" / "ay_gurobi_closure_101.txt"
DEFAULT_AY_BIN = REPO_ROOT / "target" / "release" / "ay-milp"
SCHEMA = "ay-gurobi-closure-v1"
SOLVER_SEED = 0
REFERENCE_RELATIVE_TOLERANCE = 1e-6

FIRST_PANEL = (
    "ej",
    "enlight4",
    "enlight8",
    "enlight9",
    "enlight11",
    "enlight_hard",
    "p0201",
    "qnet1",
    "qnet1_o",
    "nexp-50-20-1-1",
    "nexp-50-20-4-2",
    "rout",
    "supportcase14",
    "supportcase16",
    "app2-2",
    "cod105",
)

TERMINAL_STATUSES = frozenset(("OPTIMAL", "INFEASIBLE", "UNBOUNDED"))
INCUMBENT_STATUSES = frozenset(("OPTIMAL", "FEASIBLE"))
VERIFY_STATUSES = frozenset(
    ("VERIFIED", "UNVERIFIED", "PARTIAL", "REFUTED", "MISMATCH")
)
THREAD_ENV = {
    "OMP_NUM_THREADS": "1",
    "OPENBLAS_NUM_THREADS": "1",
    "MKL_NUM_THREADS": "1",
    "VECLIB_MAXIMUM_THREADS": "1",
    "NUMEXPR_NUM_THREADS": "1",
    "RAYON_NUM_THREADS": "1",
}
SOLVER_ENV_PREFIXES = ("AY_", "NY_")
SOLVER_RESOURCE_ENV_NAMES = frozenset(("MEMLIMIT", "NBCORE", "TIME_LIMIT"))
LICENSE_ENV_NAMES = (
    "GRB_LICENSE_FILE",
    "GRB_WLSACCESSID",
    "GRB_WLSSECRET",
    "GRB_LICENSEID",
    "GRB_COMPUTESERVER",
    "GRB_CLOUDACCESSID",
    "GRB_CLOUDSECRETKEY",
)

sys.path.insert(0, str(SCRIPT_DIR))
from _oom_guard import (  # noqa: E402
    physical_core_count,
    physical_ram_mb,
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)


GUROBI_CHILD = r'''import hashlib
import importlib.metadata
import importlib.util
import json
import math
import os
import sys
import time


def file_record(path):
    if not path or not os.path.isfile(path):
        return {"path": path, "sha256": None, "size_bytes": None}
    digest = hashlib.sha256()
    size = 0
    with open(path, "rb") as handle:
        while True:
            block = handle.read(1024 * 1024)
            if not block:
                break
            digest.update(block)
            size += len(block)
    return {"path": os.path.realpath(path), "sha256": digest.hexdigest(),
            "size_bytes": size}


def finite(value):
    try:
        number = float(value)
    except Exception:
        return None
    return number if math.isfinite(number) else None


def attribute(obj, name, default=None):
    try:
        return getattr(obj, name)
    except Exception:
        return default


def emit(record):
    print(json.dumps(record, sort_keys=True, allow_nan=False), flush=True)


def module_record(gp):
    try:
        package_version = importlib.metadata.version("gurobipy")
    except Exception:
        package_version = None
    try:
        core_spec = importlib.util.find_spec("gurobipy._core")
        core_path = core_spec.origin if core_spec is not None else None
    except Exception:
        core_path = None
    return {
        "gurobi_version": list(gp.gurobi.version()),
        "package_version": package_version,
        "python_module": file_record(getattr(gp, "__file__", None)),
        "native_module": file_record(core_path),
        "python": sys.version,
        "python_executable": os.path.realpath(sys.executable),
    }


def main():
    mode = sys.argv[1]
    stage = "import"
    env = None
    model = None
    try:
        import gurobipy as gp
        provenance = module_record(gp)
        stage = "license"
        env = gp.Env(empty=True)
        env.setParam("OutputFlag", 0)
        env.start()
        if mode == "probe":
            emit({"status": "PROBE_OK", "license_status": "accepted",
                  "provenance": provenance})
            return

        model_path = sys.argv[2]
        timeout = float(sys.argv[3])
        seed = int(sys.argv[4])
        solution_path = sys.argv[5]
        log_path = sys.argv[6]
        stage = "read-model"
        model = gp.read(model_path, env=env)
        model.setParam("Threads", 1)
        model.setParam("Seed", seed)
        model.setParam("TimeLimit", timeout)
        model.setParam("MIPGap", 0.0)
        model.setParam("MIPGapAbs", 0.0)
        model.setParam("LogToConsole", 0)
        model.setParam("LogFile", log_path)
        model.setParam("OutputFlag", 1)
        stage = "optimize"
        started = time.monotonic()
        model.optimize()
        optimize_wall = time.monotonic() - started
        status_code = int(attribute(model, "Status", -1))
        status_names = {
            1: "LOADED", 2: "OPTIMAL", 3: "INFEASIBLE",
            4: "INF_OR_UNBD", 5: "UNBOUNDED", 6: "CUTOFF",
            7: "ITERATION_LIMIT", 8: "NODE_LIMIT", 9: "TIMEOUT",
            10: "SOLUTION_LIMIT", 11: "INTERRUPTED", 12: "NUMERIC",
            13: "SUBOPTIMAL", 14: "IN_PROGRESS", 15: "USER_OBJ_LIMIT",
            16: "WORK_LIMIT", 17: "MEM_LIMIT",
        }
        solution_error = None
        solution_count = int(attribute(model, "SolCount", 0) or 0)
        if solution_count > 0:
            try:
                model.write(solution_path)
            except Exception as error:
                solution_error = f"{type(error).__name__}: {error}"
        record = {
            "status": status_names.get(status_code, f"STATUS_{status_code}"),
            "status_code": status_code,
            "license_status": "accepted-for-model",
            "objective": finite(attribute(model, "ObjVal")) if solution_count else None,
            "dual_bound": finite(attribute(model, "ObjBound")),
            "gap": finite(attribute(model, "MIPGap")) if solution_count else None,
            "nodes": finite(attribute(model, "NodeCount")),
            "simplex_iterations": finite(attribute(model, "IterCount")),
            "solver_runtime_sec": finite(attribute(model, "Runtime")),
            "optimize_wall_sec": optimize_wall,
            "solution_count": solution_count,
            "solution_error": solution_error,
            "model": {
                "rows": int(attribute(model, "NumConstrs", 0)),
                "columns": int(attribute(model, "NumVars", 0)),
                "nonzeros": int(attribute(model, "NumNZs", 0)),
                "integer_variables": int(attribute(model, "NumIntVars", 0)),
                "binary_variables": int(attribute(model, "NumBinVars", 0)),
                "sense": (
                    "minimize"
                    if int(attribute(model, "ModelSense", 1)) == 1
                    else "maximize"
                ),
            },
            "posture": {
                "threads": 1, "seed": seed, "time_limit_sec": timeout,
                "mip_gap": 0.0, "mip_gap_abs": 0.0,
            },
            "provenance": provenance,
        }
        emit(record)
    except Exception as error:
        message = str(error)
        lower = message.lower()
        license_status = "rejected" if "license" in lower else "unknown"
        if "size-limited" in lower or "size limited" in lower:
            license_status = "size-limited"
        emit({
            "status": "CHILD_ERROR",
            "stage": stage,
            "error_type": type(error).__name__,
            "error": message[:1000],
            "license_status": license_status,
        })
    finally:
        if model is not None:
            try:
                model.dispose()
            except Exception:
                pass
        if env is not None:
            try:
                env.dispose()
            except Exception:
                pass


main()
'''


def utc_now() -> str:
    """Return a stable RFC-3339 UTC timestamp."""

    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def file_identity(path: Path) -> dict[str, Any]:
    resolved = path.expanduser().resolve(strict=True)
    stat = resolved.stat()
    return {
        "path": str(resolved),
        "sha256": sha256_file(resolved),
        "size_bytes": stat.st_size,
        "mtime_ns": stat.st_mtime_ns,
    }


def artifact_identity(path: Path, root: Path) -> dict[str, Any]:
    if not path.is_file():
        return {"exists": False, "path": str(path.relative_to(root))}
    stat = path.stat()
    return {
        "exists": True,
        "path": str(path.relative_to(root)),
        "sha256": sha256_file(path),
        "size_bytes": stat.st_size,
    }


def load_case_list(path: Path = CASE_LIST_PATH) -> list[str]:
    names = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line and not line.startswith("#"):
            names.append(line)
    duplicates = sorted(name for name, count in collections.Counter(names).items() if count > 1)
    if duplicates:
        raise ValueError(f"duplicate closure instances: {', '.join(duplicates)}")
    if path == CASE_LIST_PATH and len(names) != 101:
        raise ValueError(f"frozen closure list has {len(names)} cases, expected 101")
    return names


def parse_solu(path: Path) -> dict[str, dict[str, Any]]:
    """Parse the MIPLIB ``.solu`` statuses used by this corpus."""

    status_map = {
        "=opt=": "OPTIMAL",
        "=inf=": "INFEASIBLE",
        "=unbd=": "UNBOUNDED",
        "=unkn=": "UNKNOWN",
        "=best=": "BEST_KNOWN",
    }
    entries: dict[str, dict[str, Any]] = {}
    for line_number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        fields = raw.split()
        if len(fields) < 2 or fields[0] not in status_map:
            continue
        name = fields[1]
        if name in entries:
            raise ValueError(f"duplicate .solu entry {name!r} at line {line_number}")
        objective_text = fields[2] if len(fields) >= 3 else None
        objective = None
        if objective_text is not None:
            try:
                objective = float(objective_text)
            except ValueError as error:
                raise ValueError(
                    f"invalid .solu objective at line {line_number}: {objective_text!r}"
                ) from error
            if not math.isfinite(objective):
                raise ValueError(
                    f"non-finite .solu objective at line {line_number}: "
                    f"{objective_text!r}"
                )
        entries[name] = {
            "status": status_map[fields[0]],
            "objective": objective,
            "objective_text": objective_text,
            "source_token": fields[0],
        }
    return entries


def mps_sense(path: Path) -> str:
    """Read ``OBJSENSE`` without parsing or changing the benchmark model."""

    opener = gzip.open if path.name.endswith(".gz") else open
    with opener(path, "rt", encoding="utf-8", errors="replace") as handle:
        in_obj_sense = False
        for raw in handle:
            line = raw.strip()
            if not line or line.startswith("*"):
                continue
            fields = line.upper().split()
            if fields[0] == "OBJSENSE":
                in_obj_sense = True
                if len(fields) > 1:
                    return "maximize" if fields[1].startswith("MAX") else "minimize"
                continue
            if in_obj_sense:
                return "maximize" if fields[0].startswith("MAX") else "minimize"
            if fields[0] == "ROWS":
                break
    return "minimize"


def close_number(left: float, right: float, relative_tolerance: float = 1e-6) -> bool:
    return abs(left - right) <= relative_tolerance * max(1.0, abs(left), abs(right))


def parse_last_json_object(text: str) -> dict[str, Any]:
    def finite_tree(value: Any) -> bool:
        if isinstance(value, float):
            return math.isfinite(value)
        if isinstance(value, dict):
            return all(finite_tree(item) for item in value.values())
        if isinstance(value, list):
            return all(finite_tree(item) for item in value)
        return True

    for line in reversed(text.splitlines()):
        candidate = line.strip()
        if not candidate.startswith("{"):
            continue
        try:
            value = json.loads(candidate)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict) and finite_tree(value):
            return value
    raise ValueError("no JSON object found in child stdout")


def parse_verify_output(text: str) -> dict[str, Any]:
    status = None
    census = None
    for raw in text.splitlines():
        line = raw.strip()
        if line.startswith("CLAIMS "):
            census = line
        if line in VERIFY_STATUSES:
            status = line
    claims: dict[str, str] = {}
    if census:
        for key, value in re.findall(r"(verified|refuted|unbacked)=([^ ]+)", census):
            claims[key] = value
    return {"status": status, "census": census, "claims": claims}


def parse_point_output(text: str) -> dict[str, Any]:
    status = None
    objective = None
    named_columns = None
    for raw in text.splitlines():
        line = raw.strip()
        match = re.match(r"point: (\d+) of (\d+) columns named$", line)
        if match:
            named_columns = {"named": int(match.group(1)), "total": int(match.group(2))}
        if line.startswith("FEASIBLE"):
            status = "FEASIBLE"
            objective_match = re.search(r"objective ([^ ]+)", line)
            objective = objective_match.group(1) if objective_match else None
        elif line.startswith("INFEASIBLE"):
            status = "INFEASIBLE"
    return {"status": status, "objective": objective, "columns": named_columns}


def controlled_environment(
    source: dict[str, str] | None = None,
) -> tuple[dict[str, str], dict[str, Any]]:
    env = dict(os.environ if source is None else source)
    removed = {
        key: env.pop(key)
        for key in sorted(env)
        if key.startswith(SOLVER_ENV_PREFIXES) or key in SOLVER_RESOURCE_ENV_NAMES
    }
    env.update(THREAD_ENV)
    fingerprint = sha256_text("".join(f"{key}={env[key]}\0" for key in sorted(env)))
    posture = {
        "thread_limits": dict(THREAD_ENV),
        "removed_solver_environment": removed,
        # Compatibility for deterministic tuning reports that separate the
        # explicitly searched MILP coordinates from every other scrubbed knob.
        "removed_ay_milp_environment": {
            key: value for key, value in removed.items() if key.startswith("AY_MILP_")
        },
        "environment_sha256": fingerprint,
        "gurobi_license_environment_names_present": [
            key for key in LICENSE_ENV_NAMES if key in env
        ],
    }
    return env, posture


def build_ay_command(
    ay_binary: Path,
    model: Path,
    timeout: float,
    seed: int,
    certificate: Path,
    witness: Path,
) -> list[str]:
    return [
        str(ay_binary),
        "solve",
        str(model),
        "--time-limit",
        str(timeout),
        "--threads",
        "1",
        "--seed",
        str(seed),
        "--deterministic",
        "--require",
        "witness",
        "--emit-cert",
        str(certificate),
        "--emit-witness",
        str(witness),
        "--witness-format",
        "rational",
        "--format",
        "json",
    ]


def build_gurobi_probe_command(python: Path) -> list[str]:
    return [str(python), "-c", GUROBI_CHILD, "probe"]


def build_gurobi_command(
    python: Path,
    model: Path,
    timeout: float,
    seed: int,
    solution: Path,
    log: Path,
) -> list[str]:
    return [
        str(python),
        "-c",
        GUROBI_CHILD,
        "solve",
        str(model),
        str(timeout),
        str(seed),
        str(solution),
        str(log),
    ]


def display_command(command: list[str]) -> list[str]:
    if len(command) >= 3 and command[1] == "-c" and command[2] == GUROBI_CHILD:
        return [
            command[0],
            "-c",
            f"<GUROBI_CHILD sha256={sha256_text(GUROBI_CHILD)}>",
            *command[3:],
        ]
    return list(command)


def command_identity(command: list[str]) -> dict[str, Any]:
    raw = b"\0".join(os.fsencode(part) for part in command)
    return {"argv": display_command(command), "argv_sha256": sha256_bytes(raw)}


def run_guarded_capture(
    command: list[str],
    *,
    memlimit_mb: int,
    timeout_sec: float,
    label: str,
    env: dict[str, str],
    env_posture: dict[str, Any],
    artifact_dir: Path,
    artifact_root: Path,
) -> dict[str, Any]:
    artifact_dir.mkdir(parents=True, exist_ok=True)
    stdout_path = artifact_dir / "stdout.txt"
    stderr_path = artifact_dir / "stderr.txt"
    started = utc_now()
    try:
        captured = run_captured(
            command,
            memlimit_mb,
            timeout_sec,
            label=label,
            env=env,
            cwd=str(REPO_ROOT),
        )
        fields = dataclasses.asdict(captured)
        stdout = fields.pop("stdout")
        stderr = fields.pop("stderr")
        launch_error = None
    except Exception as error:  # preserve campaign evidence before failing closed
        stdout = ""
        stderr = f"{type(error).__name__}: {error}\n"
        fields = {
            "returncode": None,
            "timed_out": False,
            "memout": False,
            "wall_sec": None,
            "stdout_truncated": False,
            "stderr_truncated": False,
            "cancelled": False,
        }
        launch_error = stderr.strip()
    stdout_path.write_text(stdout, encoding="utf-8")
    stderr_path.write_text(stderr, encoding="utf-8")
    return {
        **command_identity(command),
        "started_at": started,
        "hard_timeout_sec": timeout_sec,
        "memlimit_mb": memlimit_mb,
        "environment": env_posture,
        **fields,
        "launch_error": launch_error,
        "stdout": artifact_identity(stdout_path, artifact_root),
        "stderr": artifact_identity(stderr_path, artifact_root),
    }


def process_is_clean(process: dict[str, Any]) -> bool:
    return (
        process.get("launch_error") is None
        and process.get("returncode") == 0
        and not process.get("timed_out")
        and not process.get("memout")
        and not process.get("cancelled")
        and not process.get("stdout_truncated")
        and not process.get("stderr_truncated")
    )


def parse_process_json(
    process: dict[str, Any], artifact_root: Path
) -> tuple[dict[str, Any] | None, str | None]:
    stdout_path = artifact_root / process["stdout"]["path"]
    try:
        return parse_last_json_object(stdout_path.read_text(encoding="utf-8")), None
    except (OSError, ValueError) as error:
        return None, f"{type(error).__name__}: {error}"


def run_ay(
    ay_binary: Path,
    model: Path,
    timeout: float,
    seed: int,
    hard_timeout: float,
    plan: Any,
    env: dict[str, str],
    env_posture: dict[str, Any],
    case_dir: Path,
    artifact_root: Path,
    extra_args: list[str] | None = None,
) -> dict[str, Any]:
    """`extra_args` appends a caller-owned argv fragment to the solve command.

    Added for the joint-search harness, whose measurement axes moved from
    `AY_MILP_*` environment spellings to engine CLI flags (B38). Optional and
    defaulted, so every existing caller is byte-identical.
    """
    run_dir = case_dir / "ay"
    certificate = run_dir / "result.ayc"
    witness = run_dir / "result.sol"
    command = build_ay_command(ay_binary, model, timeout, seed, certificate, witness)
    if extra_args:
        command.extend(extra_args)
    process = run_guarded_capture(
        command,
        memlimit_mb=plan.memlimit_mb,
        timeout_sec=hard_timeout,
        label="ay_gurobi_closure.py[ay]",
        env=env,
        env_posture=env_posture,
        artifact_dir=run_dir,
        artifact_root=artifact_root,
    )
    verdict, parse_error = parse_process_json(process, artifact_root)
    return {
        "process": process,
        "verdict": verdict,
        "parse_error": parse_error,
        "certificate": artifact_identity(certificate, artifact_root),
        "witness": artifact_identity(witness, artifact_root),
    }


def run_gurobi(
    python: Path,
    model: Path,
    timeout: float,
    seed: int,
    hard_timeout: float,
    plan: Any,
    env: dict[str, str],
    env_posture: dict[str, Any],
    case_dir: Path,
    artifact_root: Path,
) -> dict[str, Any]:
    run_dir = case_dir / "gurobi"
    run_dir.mkdir(parents=True, exist_ok=True)
    solution = run_dir / "result.sol"
    log = run_dir / "gurobi.log"
    command = build_gurobi_command(python, model, timeout, seed, solution, log)
    process = run_guarded_capture(
        command,
        memlimit_mb=plan.memlimit_mb,
        timeout_sec=hard_timeout,
        label="ay_gurobi_closure.py[gurobi]",
        env=env,
        env_posture=env_posture,
        artifact_dir=run_dir,
        artifact_root=artifact_root,
    )
    verdict, parse_error = parse_process_json(process, artifact_root)
    return {
        "process": process,
        "verdict": verdict,
        "parse_error": parse_error,
        "solution": artifact_identity(solution, artifact_root),
        "solver_log": artifact_identity(log, artifact_root),
    }


def run_checker(
    command: list[str],
    *,
    parser: Any,
    plan: Any,
    timeout: float,
    env: dict[str, str],
    env_posture: dict[str, Any],
    artifact_dir: Path,
    artifact_root: Path,
) -> dict[str, Any]:
    process = run_guarded_capture(
        command,
        memlimit_mb=plan.memlimit_mb,
        timeout_sec=timeout,
        label="ay_gurobi_closure.py[checker]",
        env=env,
        env_posture=env_posture,
        artifact_dir=artifact_dir,
        artifact_root=artifact_root,
    )
    stdout_path = artifact_root / process["stdout"]["path"]
    parsed = parser(stdout_path.read_text(encoding="utf-8"))
    return {"process": process, "parsed": parsed}


def skipped_checker(reason: str) -> dict[str, Any]:
    return {"not_run": True, "reason": reason, "process": None, "parsed": None}


def check_ay_evidence(
    ay_binary: Path,
    model: Path,
    result: dict[str, Any],
    plan: Any,
    timeout: float,
    env: dict[str, str],
    env_posture: dict[str, Any],
    case_dir: Path,
    artifact_root: Path,
) -> None:
    certificate_path = artifact_root / result["certificate"]["path"]
    witness_path = artifact_root / result["witness"]["path"]
    if certificate_path.is_file():
        result["certificate_check"] = run_checker(
            [str(ay_binary), "verify", "--model", str(model), "--cert", str(certificate_path)],
            parser=parse_verify_output,
            plan=plan,
            timeout=timeout,
            env=env,
            env_posture=env_posture,
            artifact_dir=case_dir / "ay-certificate-check",
            artifact_root=artifact_root,
        )
    else:
        result["certificate_check"] = skipped_checker("certificate was not emitted")
    if witness_path.is_file():
        result["point_check"] = run_checker(
            [str(ay_binary), "check-point", "--model", str(model), "--point", str(witness_path)],
            parser=parse_point_output,
            plan=plan,
            timeout=timeout,
            env=env,
            env_posture=env_posture,
            artifact_dir=case_dir / "ay-point-check",
            artifact_root=artifact_root,
        )
    else:
        result["point_check"] = skipped_checker("witness was not emitted")


def check_gurobi_evidence(
    ay_binary: Path,
    model: Path,
    result: dict[str, Any],
    plan: Any,
    timeout: float,
    env: dict[str, str],
    env_posture: dict[str, Any],
    case_dir: Path,
    artifact_root: Path,
) -> None:
    solution_path = artifact_root / result["solution"]["path"]
    if solution_path.is_file():
        result["point_check"] = run_checker(
            [
                str(ay_binary),
                "check-point",
                "--model",
                str(model),
                "--point",
                str(solution_path),
                "--repair-continuous",
                "--repair-time-limit",
                str(min(timeout, 10.0)),
                "--memory-budget",
                str(plan.memlimit_mb * 1024 * 1024),
            ],
            parser=parse_point_output,
            plan=plan,
            timeout=timeout,
            env=env,
            env_posture=env_posture,
            artifact_dir=case_dir / "gurobi-point-check",
            artifact_root=artifact_root,
        )
    else:
        result["point_check"] = skipped_checker("Gurobi did not emit a solution")


def numeric(value: Any) -> float | None:
    try:
        number = float(Fraction(value)) if isinstance(value, str) and "/" in value else float(value)
    except (TypeError, ValueError, ZeroDivisionError, OverflowError):
        return None
    return number if math.isfinite(number) else None


def solver_value(solver: str, verdict: dict[str, Any]) -> float | None:
    key = "value" if solver == "ay" else "objective"
    return numeric(verdict.get(key))


def evaluate_solver(
    solver: str,
    result: dict[str, Any],
    reference: dict[str, Any],
    sense: str,
    tolerance: float,
) -> dict[str, Any]:
    invalid: list[str] = []
    wrong: list[str] = []
    process = result["process"]
    if not process_is_clean(process):
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
    if solver == "gurobi":
        child_sense = (verdict.get("model") or {}).get("sense")
        if child_sense is not None and child_sense != sense:
            invalid.append(
                f"Gurobi parsed objective sense {child_sense}, expected {sense}"
            )
    outer_wall = numeric(process.get("wall_sec"))
    if outer_wall is None or outer_wall < 0:
        invalid.append("solver process has no finite non-negative wall time")

    value = solver_value(solver, verdict)
    bound = numeric(verdict.get("dual_bound"))
    has_incumbent = status in INCUMBENT_STATUSES or (
        solver == "gurobi"
        and numeric(verdict.get("solution_count")) is not None
        and numeric(verdict.get("solution_count")) > 0
    )
    point_check = result.get("point_check") or {}
    point_parsed = point_check.get("parsed") or {}
    point_verified = (
        has_incumbent
        and point_parsed.get("status") == "FEASIBLE"
        and point_check.get("process") is not None
        and process_is_clean(point_check["process"])
    )
    if has_incumbent and not point_verified:
        invalid.append("reported incumbent did not pass the exact point checker")
    point_objective = numeric(point_parsed.get("objective"))
    if has_incumbent and point_verified and (
        value is None
        or point_objective is None
        or not close_number(value, point_objective, tolerance)
    ):
        invalid.append(
            f"reported objective {value!r} disagrees with checked point "
            f"objective {point_parsed.get('objective')!r}"
        )

    certificate_status = None
    certificate_census = None
    certificate_claims: dict[str, str] = {}
    required_certificate_claims: set[str] = set()
    missing_verified_claims: set[str] = set()
    if solver == "ay":
        certificate_check = result.get("certificate_check") or {}
        certificate_parsed = certificate_check.get("parsed") or {}
        certificate_status = certificate_parsed.get("status")
        certificate_census = certificate_parsed.get("census")
        certificate_claims = certificate_parsed.get("claims") or {}
        if status in TERMINAL_STATUSES and certificate_status is None:
            invalid.append("terminal AY verdict has no certificate-check status")
        expected_checker_exit = {
            "VERIFIED": 0,
            "UNVERIFIED": 10,
            "PARTIAL": 11,
            "REFUTED": 20,
            "MISMATCH": 30,
        }.get(certificate_status)
        certificate_process = certificate_check.get("process")
        if certificate_status is not None and (
            certificate_process is None
            or certificate_process.get("launch_error") is not None
            or certificate_process.get("timed_out")
            or certificate_process.get("memout")
            or certificate_process.get("cancelled")
            or certificate_process.get("stdout_truncated")
            or certificate_process.get("stderr_truncated")
            or certificate_process.get("returncode") != expected_checker_exit
        ):
            invalid.append(
                "AY certificate checker process did not match its reported status"
            )
        if certificate_status in ("REFUTED", "MISMATCH"):
            invalid.append(f"AY certificate checker returned {certificate_status}")
        verified_claims = set(
            certificate_claims.get("verified", "-").split(",")
        ) - {"-", ""}
        if status == "OPTIMAL":
            required_certificate_claims = {"primal", "dual"}
        elif status == "INFEASIBLE":
            required_certificate_claims = {"infeasible"}
        elif status == "UNBOUNDED":
            required_certificate_claims = {"unbounded"}
        if status in TERMINAL_STATUSES and certificate_status != "VERIFIED":
            invalid.append(
                f"terminal AY {status} verdict requires certificate status VERIFIED, "
                f"got {certificate_status or 'MISSING'}"
            )
        missing_verified_claims = required_certificate_claims - verified_claims
        if status == "OPTIMAL" and missing_verified_claims:
            invalid.append(
                "AY OPTIMAL verdict lacks independently verified certificate "
                f"claim(s): {','.join(sorted(missing_verified_claims))}"
            )
        if status == "INFEASIBLE" and missing_verified_claims:
            invalid.append(
                "AY INFEASIBLE verdict lacks an independently verified "
                "infeasible claim"
            )
        if status == "UNBOUNDED" and missing_verified_claims:
            invalid.append(
                "AY UNBOUNDED verdict lacks an independently verified "
                "unbounded claim"
            )

    ref_status = reference["status"]
    ref_value = reference.get("objective")
    if ref_status == "OPTIMAL":
        if status == "OPTIMAL":
            if (
                value is None
                or ref_value is None
                or not close_number(value, ref_value, tolerance)
            ):
                wrong.append(
                    f"OPTIMAL objective {value!r} disagrees with reference "
                    f"{ref_value!r}"
                )
        elif status in ("INFEASIBLE", "UNBOUNDED"):
            wrong.append(f"{status} contradicts the reference optimum")
        if value is not None and has_incumbent and ref_value is not None:
            slack = tolerance * max(1.0, abs(ref_value))
            impossible = (
                value < ref_value - slack
                if sense == "minimize"
                else value > ref_value + slack
            )
            if impossible:
                wrong.append(
                    f"incumbent {value} beats reference optimum {ref_value}"
                )
        if bound is not None and ref_value is not None:
            slack = tolerance * max(1.0, abs(ref_value))
            impossible = (
                bound > ref_value + slack
                if sense == "minimize"
                else bound < ref_value - slack
            )
            if impossible:
                wrong.append(
                    f"dual bound {bound} is on the wrong side of optimum "
                    f"{ref_value}"
                )
    elif ref_status == "INFEASIBLE":
        if has_incumbent and point_verified:
            wrong.append("exactly checked incumbent contradicts INFEASIBLE reference")
        elif status == "UNBOUNDED":
            wrong.append("UNBOUNDED contradicts INFEASIBLE reference")
    elif ref_status == "UNBOUNDED":
        if status in ("OPTIMAL", "INFEASIBLE"):
            wrong.append(f"{status} contradicts UNBOUNDED reference")

    solved = status in TERMINAL_STATUSES and not invalid and not wrong
    if ref_status == "OPTIMAL":
        solved = solved and status == "OPTIMAL"
    elif ref_status == "INFEASIBLE":
        solved = solved and status == "INFEASIBLE"
    elif ref_status == "UNBOUNDED":
        solved = solved and status == "UNBOUNDED"
    return {
        "status": status,
        "value": value,
        "dual_bound": bound,
        "has_incumbent": has_incumbent,
        "point_verified": point_verified,
        "checked_point_objective": point_parsed.get("objective"),
        "certificate_status": certificate_status,
        "certificate_census": certificate_census,
        "certificate_claims": certificate_claims,
        "certificate_required_claims": sorted(required_certificate_claims),
        "certificate_missing_verified_claims": sorted(missing_verified_claims),
        "certificate_complete": (
            certificate_status == "VERIFIED" and not missing_verified_claims
        ),
        "invalid_issues": invalid,
        "wrong_issues": wrong,
        "valid": not invalid,
        "correct_against_reference": not wrong,
        "solved": solved,
        "outer_wall_sec": outer_wall,
    }


def compare_trial(ay: dict[str, Any], gurobi: dict[str, Any]) -> dict[str, Any]:
    if (
        ay["invalid_issues"]
        or ay["wrong_issues"]
        or gurobi["invalid_issues"]
        or gurobi["wrong_issues"]
    ):
        return {"classification": "INCONCLUSIVE_INVALID", "ratio": None}
    if ay["solved"] and not gurobi["solved"]:
        return {"classification": "AY_ONLY", "ratio": None}
    if gurobi["solved"] and not ay["solved"]:
        return {"classification": "GUROBI_ONLY", "ratio": None}
    if not ay["solved"] and not gurobi["solved"]:
        return {"classification": "NEITHER", "ratio": None}
    ay_wall = ay["outer_wall_sec"]
    gurobi_wall = gurobi["outer_wall_sec"]
    if ay_wall is None or gurobi_wall is None:
        return {"classification": "INCONCLUSIVE_INVALID", "ratio": None}
    if ay_wall < gurobi_wall:
        return {"classification": "AY_FASTER", "ratio": gurobi_wall / ay_wall}
    if gurobi_wall < ay_wall:
        return {"classification": "GUROBI_FASTER", "ratio": ay_wall / gurobi_wall}
    return {"classification": "TIE", "ratio": 1.0}


def aggregate_rows(
    rows: list[dict[str, Any]], names: list[str], repetitions: int
) -> dict[str, Any]:
    grouped: dict[str, list[dict[str, Any]]] = collections.defaultdict(list)
    for row in rows:
        grouped[row["name"]].append(row)
    cases = []
    for name in names:
        trials = grouped.get(name, [])
        repetition_counts = collections.Counter(row.get("repetition") for row in trials)
        expected_repetitions = set(range(repetitions))
        complete_repetitions = (
            len(trials) == repetitions
            and set(repetition_counts) == expected_repetitions
            and all(count == 1 for count in repetition_counts.values())
        )
        if not complete_repetitions:
            cases.append({
                "name": name,
                "classification": "INCOMPLETE",
                "trials": len(trials),
                "repetition_counts": {
                    str(repetition): count
                    for repetition, count in sorted(
                        repetition_counts.items(), key=lambda item: str(item[0])
                    )
                },
                "ay_solved": 0,
                "gurobi_solved": 0,
            })
            continue
        invalid = any(
            row["ay_evaluation"]["invalid_issues"]
            or row["ay_evaluation"]["wrong_issues"]
            or row["gurobi_evaluation"]["invalid_issues"]
            or row["gurobi_evaluation"]["wrong_issues"]
            for row in trials
        )
        ay_solved = [row for row in trials if row["ay_evaluation"]["solved"]]
        grb_solved = [row for row in trials if row["gurobi_evaluation"]["solved"]]
        ay_walls = [row["ay_evaluation"]["outer_wall_sec"] for row in ay_solved]
        grb_walls = [row["gurobi_evaluation"]["outer_wall_sec"] for row in grb_solved]
        ay_median = statistics.median(ay_walls) if ay_walls else None
        grb_median = statistics.median(grb_walls) if grb_walls else None
        trial_classifications = [
            compare_trial(row["ay_evaluation"], row["gurobi_evaluation"])[
                "classification"
            ]
            for row in trials
        ]
        gurobi_trial_advantages = [
            classification
            for classification in trial_classifications
            if classification in ("GUROBI_ONLY", "GUROBI_FASTER")
        ]
        ratio = None
        if invalid:
            classification = "INCONCLUSIVE_INVALID"
        elif gurobi_trial_advantages:
            # Literal dominance is per observation, not a median-only claim.  A
            # median can summarize stable timings, but it must never erase a
            # clean repetition in which Gurobi solved more or finished first.
            classification = "GUROBI_TRIAL_ADVANTAGE"
        elif len(ay_solved) == repetitions and len(grb_solved) < repetitions:
            classification = "AY_MORE_SOLVES"
        elif len(grb_solved) == repetitions and len(ay_solved) < repetitions:
            classification = "GUROBI_MORE_SOLVES"
        elif len(ay_solved) < repetitions or len(grb_solved) < repetitions:
            classification = (
                "NEITHER"
                if not ay_solved and not grb_solved
                else "INCONCLUSIVE_UNSTABLE"
            )
        elif ay_median < grb_median:
            classification = "AY_FASTER"
            ratio = grb_median / ay_median
        elif grb_median < ay_median:
            classification = "GUROBI_FASTER"
            ratio = ay_median / grb_median
        else:
            classification = "TIE"
            ratio = 1.0
        cases.append({
            "name": name,
            "classification": classification,
            "trials": len(trials),
            "ay_solved": len(ay_solved),
            "gurobi_solved": len(grb_solved),
            "ay_median_outer_wall_sec": ay_median,
            "gurobi_median_outer_wall_sec": grb_median,
            "faster_ratio": ratio,
            "trial_classifications": trial_classifications,
            "gurobi_advantage_trials": len(gurobi_trial_advantages),
        })

    class_counts = collections.Counter(case["classification"] for case in cases)
    gurobi_advantages = [
        case["name"]
        for case in cases
        if case["classification"] in (
            "GUROBI_MORE_SOLVES",
            "GUROBI_FASTER",
            "GUROBI_TRIAL_ADVANTAGE",
        )
    ]
    inconclusive = [
        case["name"]
        for case in cases
        if case["classification"] in (
            "INCOMPLETE",
            "INCONCLUSIVE_INVALID",
            "INCONCLUSIVE_UNSTABLE",
            "NEITHER",
        )
    ]
    wrong_counts = {
        solver: sum(bool(row[f"{solver}_evaluation"]["wrong_issues"]) for row in rows)
        for solver in ("ay", "gurobi")
    }
    invalid_counts = {
        solver: sum(bool(row[f"{solver}_evaluation"]["invalid_issues"]) for row in rows)
        for solver in ("ay", "gurobi")
    }
    certificate_counts = collections.Counter(
        row["ay_evaluation"]["certificate_status"] or "MISSING" for row in rows
    )
    point_counts = {
        solver: sum(row[f"{solver}_evaluation"]["point_verified"] for row in rows)
        for solver in ("ay", "gurobi")
    }
    solved_counts = {
        solver: sum(row[f"{solver}_evaluation"]["solved"] for row in rows)
        for solver in ("ay", "gurobi")
    }
    status_counts = {
        solver: dict(sorted(collections.Counter(
            row[f"{solver}_evaluation"]["status"] for row in rows
        ).items()))
        for solver in ("ay", "gurobi")
    }
    total_outer_wall = {
        solver: sum(
            row[f"{solver}_evaluation"]["outer_wall_sec"] or 0.0 for row in rows
        )
        for solver in ("ay", "gurobi")
    }
    dominance_closed = (
        len(rows) == len(names) * repetitions
        and not gurobi_advantages
        and not inconclusive
        and not any(wrong_counts.values())
        and not any(invalid_counts.values())
    )
    return {
        "expected_trials": len(names) * repetitions,
        "completed_trials": len(rows),
        "classification_counts": dict(sorted(class_counts.items())),
        "wrong_trials": wrong_counts,
        "invalid_trials": invalid_counts,
        "solved_trials": solved_counts,
        "status_counts": status_counts,
        "total_solver_outer_wall_sec": total_outer_wall,
        "ay_certificate_status_counts": dict(sorted(certificate_counts.items())),
        "point_verified_trials": point_counts,
        "known_gurobi_advantages": gurobi_advantages,
        "inconclusive_cases": inconclusive,
        "dominance_closed": dominance_closed,
        "cases": cases,
    }


def git_provenance(repo: Path) -> dict[str, Any]:
    def git(*args: str) -> bytes:
        # These are provenance probes, not solver children.  Every
        # solver and checker process goes through run_guarded_capture above.
        completed = subprocess.run(
            ["git", *args],
            cwd=repo,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return completed.stdout

    try:
        head = git("rev-parse", "HEAD").decode().strip()
        status = git("status", "--short", "--untracked-files=all").decode(
            "utf-8", errors="replace"
        )
        diff = git("diff", "--binary", "--no-ext-diff", "HEAD", "--", ".")
        untracked_raw = git("ls-files", "--others", "--exclude-standard", "-z")
    except (OSError, subprocess.CalledProcessError) as error:
        return {"error": f"{type(error).__name__}: {error}"}

    untracked = sorted(
        field.decode("utf-8", errors="surrogateescape")
        for field in untracked_raw.split(b"\0")
        if field
    )
    untracked_digest = hashlib.sha256()
    untracked_files = []
    for relative in untracked:
        path = repo / relative
        if path.is_symlink():
            content_hash = sha256_bytes(os.fsencode(os.readlink(path)))
            size = len(os.fsencode(os.readlink(path)))
        elif path.is_file():
            content_hash = sha256_file(path)
            size = path.stat().st_size
        else:
            content_hash = sha256_bytes(b"<missing>")
            size = None
        untracked_digest.update(os.fsencode(relative))
        untracked_digest.update(b"\0")
        untracked_digest.update(content_hash.encode("ascii"))
        untracked_digest.update(b"\0")
        untracked_files.append({"path": relative, "sha256": content_hash, "size_bytes": size})
    combined = hashlib.sha256()
    combined.update(head.encode("ascii"))
    combined.update(b"\0")
    combined.update(diff)
    combined.update(b"\0")
    combined.update(untracked_digest.digest())
    return {
        "head": head,
        "dirty": bool(status),
        "status": status.splitlines(),
        "tracked_diff_sha256": sha256_bytes(diff),
        "untracked_fingerprint_sha256": untracked_digest.hexdigest(),
        "worktree_fingerprint_sha256": combined.hexdigest(),
        "untracked_files": untracked_files,
    }


def freeze_binary(source: Path, destination: Path) -> dict[str, Any]:
    source_identity = file_identity(source)
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)
    destination.chmod(destination.stat().st_mode | 0o100)
    frozen_identity = file_identity(destination)
    if source_identity["sha256"] != frozen_identity["sha256"]:
        raise RuntimeError("AY binary changed while it was being frozen")
    return {"source": source_identity, "frozen": frozen_identity}


def resolve_executable(value: str) -> Path:
    candidate = Path(value).expanduser()
    if candidate.is_absolute() or os.sep in value:
        return candidate.resolve(strict=True)
    found = shutil.which(value)
    if not found:
        raise FileNotFoundError(f"cannot find executable {value!r}")
    return Path(found).resolve(strict=True)


def atomic_write_json(path: Path, payload: dict[str, Any]) -> None:
    temporary = path.with_name(f".{path.name}.tmp")
    temporary.write_text(
        json.dumps(payload, indent=2, sort_keys=True, allow_nan=False) + "\n",
        encoding="utf-8",
    )
    os.replace(temporary, path)


def default_bench_root() -> Path:
    override = os.environ.get("AY_BENCH_ROOT")
    return Path(override).expanduser() if override else Path.home() / "ay-bench" / "milp"


def default_output_path() -> Path:
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    return REPO_ROOT / "evals" / "results" / "ay-gurobi-closure" / f"{stamp}.json"


def build_parser() -> argparse.ArgumentParser:
    bench_root = default_bench_root()
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--only", choices=("all", "first-panel"), default="all")
    selection.add_argument(
        "--case", metavar="NAME", help="run one named instance from the frozen corpus"
    )
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--hard-timeout-grace", type=float, default=120.0)
    parser.add_argument("--checker-timeout", type=float, default=120.0)
    parser.add_argument("--repetitions", type=int, default=1)
    parser.add_argument("--manifest", type=Path, default=bench_root / "manifest.json")
    parser.add_argument(
        "--solu", type=Path, default=bench_root / "meta" / "miplib2017-v27.solu"
    )
    parser.add_argument("--ay-bin", type=Path, default=DEFAULT_AY_BIN)
    parser.add_argument("--gurobi-python", default=sys.executable)
    parser.add_argument("--out", type=Path, default=None)
    return parser


def select_names(
    args: argparse.Namespace, all_names: list[str], parser: argparse.ArgumentParser
) -> list[str]:
    """Resolve the requested subset without admitting models outside the corpus."""

    if not set(FIRST_PANEL).issubset(all_names):
        parser.error("FIRST_PANEL is not a subset of the frozen closure corpus")
    if args.case is not None:
        if args.case not in all_names:
            parser.error(f"--case {args.case!r} is not in the frozen closure corpus")
        return [args.case]
    return list(FIRST_PANEL) if args.only == "first-panel" else list(all_names)


def validate_args(args: argparse.Namespace, parser: argparse.ArgumentParser) -> None:
    for name in ("timeout", "hard_timeout_grace", "checker_timeout"):
        value = getattr(args, name)
        if not math.isfinite(value) or value <= 0:
            parser.error(f"--{name.replace('_', '-')} must be finite and positive")
    if args.repetitions <= 0:
        parser.error("--repetitions must be positive")


def preflight_cases(
    names: list[str], manifest_path: Path, solu_path: Path
) -> tuple[dict[str, Any], dict[str, dict[str, Any]], list[dict[str, Any]]]:
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    instances = manifest.get("instances")
    if not isinstance(instances, dict):
        raise ValueError("manifest has no object-valued 'instances' field")
    references = parse_solu(solu_path)
    prepared = []
    for name in names:
        if name not in instances:
            raise ValueError(f"closure instance {name!r} is absent from manifest")
        if name not in references:
            raise ValueError(f"closure instance {name!r} is absent from .solu")
        reference = references[name]
        if reference["status"] not in TERMINAL_STATUSES:
            raise ValueError(
                f"closure instance {name!r} has non-terminal reference status "
                f"{reference['status']}"
            )
        if reference["status"] == "OPTIMAL" and reference.get("objective") is None:
            raise ValueError(
                f"closure instance {name!r} has no finite reference objective"
            )
        model = Path(instances[name]["file"]).expanduser().resolve(strict=True)
        expected = {
            "opt": "OPTIMAL",
            "inf": "INFEASIBLE",
            "unbd": "UNBOUNDED",
        }.get(instances[name].get("ref_status"))
        if expected and expected != reference["status"]:
            raise ValueError(
                f"manifest/.solu status mismatch for {name}: {expected} vs "
                f"{reference['status']}"
            )
        prepared.append({
            "name": name,
            "model_path": model,
            "manifest_entry": dict(instances[name]),
        })
    return manifest, references, prepared


def campaign_exit_code(summary: dict[str, Any]) -> int:
    if any(summary["wrong_trials"].values()) or any(summary["invalid_trials"].values()):
        return 3
    if summary["inconclusive_cases"]:
        return 2
    if summary["known_gurobi_advantages"]:
        return 1
    return 0 if summary["dominance_closed"] else 2


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    validate_args(args, parser)
    all_names = load_case_list()
    names = select_names(args, all_names, parser)

    output = (args.out or default_output_path()).expanduser().resolve()
    artifacts = output.with_name(f"{output.stem}.artifacts")
    if output.exists() or artifacts.exists():
        parser.error(f"refusing to overwrite existing output/artifacts: {output}, {artifacts}")
    output.parent.mkdir(parents=True, exist_ok=True)

    manifest_path = args.manifest.expanduser().resolve(strict=True)
    solu_path = args.solu.expanduser().resolve(strict=True)
    ay_source = args.ay_bin.expanduser().resolve(strict=True)
    gurobi_python = resolve_executable(args.gurobi_python)
    _, references, prepared = preflight_cases(names, manifest_path, solu_path)

    warn_concurrent_build()
    plan = plan_solver_resources(1, label="ay_gurobi_closure.py")
    if plan.jobs != 1:
        raise RuntimeError(f"serial closure harness received a non-serial plan: {plan}")
    # Capture the source identity before creating result artifacts inside the
    # repository.  Otherwise the benchmark would fingerprint its own frozen
    # binary and ever-changing result JSON as part of the dirty worktree.
    source_git_provenance = git_provenance(REPO_ROOT)
    artifacts.mkdir(parents=True)
    frozen_ay = artifacts / "bin" / "ay-milp"
    ay_binary_identity = freeze_binary(ay_source, frozen_ay)
    ay_binary = Path(ay_binary_identity["frozen"]["path"])
    env, env_posture = controlled_environment()

    instance_records = []
    for item in prepared:
        identity = file_identity(item["model_path"])
        identity["name"] = item["name"]
        identity["sense"] = mps_sense(item["model_path"])
        identity["manifest"] = {
            key: item["manifest_entry"].get(key)
            for key in (
                "tier", "ref_status", "ref_obj", "rows", "cols", "nnz",
                "ints", "bins",
            )
        }
        instance_records.append(identity)
    by_name = {record["name"]: record for record in instance_records}

    document: dict[str, Any] = {
        "schema": SCHEMA,
        "state": "running",
        "started_at": utc_now(),
        "finished_at": None,
        "selection": {
            "only": args.only,
            "case": args.case,
            "instances": names,
            "count": len(names),
            "repetitions": args.repetitions,
            "frozen_list": file_identity(CASE_LIST_PATH),
            "frozen_list_count": len(all_names),
            "first_panel": list(FIRST_PANEL),
        },
        "posture": {
            "serial": True,
            "threads": 1,
            "seed": SOLVER_SEED,
            "time_limit_sec": args.timeout,
            "outer_hard_timeout_sec": args.timeout + args.hard_timeout_grace,
            "checker_timeout_sec": args.checker_timeout,
            "gurobi_mip_gap": 0.0,
            "gurobi_mip_gap_abs": 0.0,
            "ay_require": "witness",
            "ay_certificate_emission": True,
            "ay_certificate_checker": "independent ay-milp verify",
            "point_checker": "ay-milp check-point exact rational arithmetic",
            "gurobi_proof_mode": "none available; status checked against MIPLIB .solu",
            "solver_order": "alternating by instance index and repetition",
            "relative_tolerance": REFERENCE_RELATIVE_TOLERANCE,
            "solved_definition": sorted(TERMINAL_STATUSES),
            "environment": env_posture,
        },
        "resource_envelope": {
            "requested_jobs": 1,
            "jobs": plan.jobs,
            "memlimit_mb_per_child": plan.memlimit_mb,
            "nbcore_per_child": plan.nbcore,
            "headroom_mb": plan.headroom_mb,
            "memory_enforcement": "process-group rss_watchdog",
            "rss_grace_mb": 0,
            "lease": "one process-scoped host lease for the complete campaign",
        },
        "provenance": {
            "harness": file_identity(Path(__file__)),
            "oom_guard": file_identity(SCRIPT_DIR / "_oom_guard.py"),
            "gurobi_child_sha256": sha256_text(GUROBI_CHILD),
            "manifest": file_identity(manifest_path),
            "solution_reference": file_identity(solu_path),
            "ay_binary": ay_binary_identity,
            "gurobi_python": file_identity(gurobi_python),
            "git": source_git_provenance,
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
        "instances": instance_records,
        "gurobi_probe": None,
        "rows": [],
        "summary": aggregate_rows([], names, args.repetitions),
    }
    atomic_write_json(output, document)

    probe_command = build_gurobi_probe_command(gurobi_python)
    probe_process = run_guarded_capture(
        probe_command,
        memlimit_mb=plan.memlimit_mb,
        timeout_sec=args.checker_timeout,
        label="ay_gurobi_closure.py[gurobi-probe]",
        env=env,
        env_posture=env_posture,
        artifact_dir=artifacts / "gurobi-probe",
        artifact_root=artifacts,
    )
    probe_verdict, probe_error = parse_process_json(probe_process, artifacts)
    document["gurobi_probe"] = {
        "process": probe_process,
        "result": probe_verdict,
        "parse_error": probe_error,
    }
    if (
        not process_is_clean(probe_process)
        or probe_error is not None
        or not probe_verdict
        or probe_verdict.get("status") != "PROBE_OK"
    ):
        document["state"] = "incomplete"
        document["finished_at"] = utc_now()
        document["failure"] = "Gurobi import/license probe failed"
        atomic_write_json(output, document)
        print(f"Gurobi probe failed; evidence preserved in {output}", file=sys.stderr)
        return 2
    atomic_write_json(output, document)

    total = len(names) * args.repetitions
    completed = 0
    hard_timeout = args.timeout + args.hard_timeout_grace
    for repetition in range(args.repetitions):
        for name_index, name in enumerate(names):
            trial_index = repetition * len(names) + name_index
            order = (
                ("ay", "gurobi")
                if (name_index + repetition) % 2 == 0
                else ("gurobi", "ay")
            )
            model = Path(by_name[name]["path"])
            if file_identity(model)["sha256"] != by_name[name]["sha256"]:
                raise RuntimeError(f"benchmark input changed during campaign: {model}")
            case_dir = artifacts / f"{trial_index:04d}-{name}-r{repetition + 1}"
            print(
                f"[{completed + 1}/{total}] {name} r{repetition + 1}/{args.repetitions} "
                f"order={order[0]}->{order[1]}",
                flush=True,
            )
            results: dict[str, dict[str, Any]] = {}
            for solver in order:
                if solver == "ay":
                    results[solver] = run_ay(
                        ay_binary, model, args.timeout, SOLVER_SEED, hard_timeout,
                        plan, env, env_posture, case_dir, artifacts,
                    )
                else:
                    results[solver] = run_gurobi(
                        gurobi_python, model, args.timeout, SOLVER_SEED, hard_timeout,
                        plan, env, env_posture, case_dir, artifacts,
                    )

            check_ay_evidence(
                ay_binary, model, results["ay"], plan, args.checker_timeout,
                env, env_posture, case_dir, artifacts,
            )
            check_gurobi_evidence(
                ay_binary, model, results["gurobi"], plan, args.checker_timeout,
                env, env_posture, case_dir, artifacts,
            )
            reference = references[name]
            sense = by_name[name]["sense"]
            ay_evaluation = evaluate_solver(
                "ay", results["ay"], reference, sense,
                REFERENCE_RELATIVE_TOLERANCE,
            )
            gurobi_evaluation = evaluate_solver(
                "gurobi", results["gurobi"], reference, sense,
                REFERENCE_RELATIVE_TOLERANCE,
            )
            comparison = compare_trial(ay_evaluation, gurobi_evaluation)
            row = {
                "name": name,
                "repetition": repetition,
                "trial_index": trial_index,
                "solver_order": list(order),
                "model": by_name[name],
                "reference": reference,
                "ay": results["ay"],
                "gurobi": results["gurobi"],
                "ay_evaluation": ay_evaluation,
                "gurobi_evaluation": gurobi_evaluation,
                "comparison": comparison,
            }
            document["rows"].append(row)
            document["summary"] = aggregate_rows(document["rows"], names, args.repetitions)
            atomic_write_json(output, document)
            completed += 1
            print(
                f"  AY={ay_evaluation['status']} {ay_evaluation['outer_wall_sec']}s; "
                f"Gurobi={gurobi_evaluation['status']} "
                f"{gurobi_evaluation['outer_wall_sec']}s; "
                f"{comparison['classification']}",
                flush=True,
            )

    document["state"] = "complete"
    document["finished_at"] = utc_now()
    document["summary"] = aggregate_rows(document["rows"], names, args.repetitions)
    atomic_write_json(output, document)
    summary = document["summary"]
    print(
        f"wrote {output}; closed={summary['dominance_closed']} "
        f"Gurobi-advantages={len(summary['known_gurobi_advantages'])} "
        f"inconclusive={len(summary['inconclusive_cases'])}",
        flush=True,
    )
    return campaign_exit_code(summary)


if __name__ == "__main__":
    try:
        exit_code = main()
    except Exception:
        traceback.print_exc()
        exit_code = 2
    raise SystemExit(exit_code)
