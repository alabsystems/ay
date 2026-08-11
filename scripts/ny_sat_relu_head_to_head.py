#!/usr/bin/env python3
# ay-script: ny-sat-relu-head-to-head
"""Evidence-gated NY production-route versus Gurobi sat_relu benchmark.

The VNN-COMP 2025 ``sat_relu`` inputs are ONNX + VNN-LIB, an interface Gurobi
does not accept.  This harness makes that boundary explicit: NY receives the
original files, while Gurobi receives a deterministic, full-network Big-M MPS
generated before timing from the same files.  It never presents backend/window
MIP dumps as though they were the original problem.

Load-bearing posture:

* all 100 physical ``instances.csv`` rows run serially (including duplicates);
* ``NY_NO_CNF_ROUTE`` and every other NY/AY tuning variable are scrubbed;
* NY and Gurobi are both constrained to one CPU thread;
* every child is protected by the process-group RSS watchdog under one host
  lease, including the main NY binary and Gurobi, which have no MEMLIMIT knob;
* a NY UNSAT counts only with the in-process resolution-DAG validation marker;
* a NY SAT counts only with the Boolean recovery and trusted-ORT gate markers,
  plus an independent exact replay of the recovered CNF;
* a Gurobi SAT is rounded only when every input is within a strict Boolean
  tolerance, then reconstructed exactly and checked by ``ay-milp check-point``;
* raw stdout/stderr, result files, MPS files, hashes, source identities, and the
  enforced resource envelope are retained.

The generated encoding is deliberately favorable to Gurobi: translation is
outside its timed solve and its exact point checker is outside timing, while
NY's ONNX loading, route detection, certificate validation, and trusted ORT
gate remain inside NY's process wall.  It is an honest same-source comparison,
not a claim that both solvers consumed identical bytes.

Exit codes: 0 means Phase 0 passed (``--mode ny-only``), or every measured
head-to-head trial was valid and NY's process wall was no greater; 1 means a
valid Gurobi-faster trial remains; 2 means incomplete evidence; 3 means invalid
or reference-disagreeing evidence.
"""

from __future__ import annotations

import argparse
import collections
import csv
import dataclasses
import datetime as dt
import hashlib
import json
import math
import os
import platform
import re
import shutil
import statistics
import struct
import subprocess
import sys
from decimal import Decimal, InvalidOperation
from pathlib import Path
from typing import Any, Iterable


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(SCRIPT_DIR))

from _oom_guard import (  # noqa: E402
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)
from milp2mps import emit as emit_mps  # noqa: E402


SCHEMA = "ny-sat-relu-head-to-head-v1"
EXPECTED_ROWS = 100
EXPECTED_UNIQUE = 98
SOLVER_SEED = 0
BOOLEAN_TOLERANCE = Decimal("0.000001")
THREAD_ENV = {
    "OMP_NUM_THREADS": "1",
    "OPENBLAS_NUM_THREADS": "1",
    "MKL_NUM_THREADS": "1",
    "VECLIB_MAXIMUM_THREADS": "1",
    "NUMEXPR_NUM_THREADS": "1",
    "RAYON_NUM_THREADS": "1",
}
RESOURCE_ENV = frozenset(("MEMLIMIT", "NBCORE", "TIME_LIMIT"))
EXTRA_ROUTE_ENV = frozenset(("GPU_AVAILABLE",))
LICENSE_ENV_NAMES = (
    "GRB_LICENSE_FILE",
    "GRB_WLSACCESSID",
    "GRB_WLSSECRET",
    "GRB_LICENSEID",
    "GRB_COMPUTESERVER",
    "GRB_CLOUDACCESSID",
    "GRB_CLOUDSECRETKEY",
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
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
            size += len(block)
    return {"path": os.path.realpath(path), "sha256": digest.hexdigest(),
            "size_bytes": size}


def finite(value):
    try:
        value = float(value)
    except Exception:
        return None
    return value if math.isfinite(value) else None


def attribute(obj, name, default=None):
    try:
        return getattr(obj, name)
    except Exception:
        return default


def emit(value):
    print(json.dumps(value, sort_keys=True, allow_nan=False), flush=True)


def provenance(gp):
    try:
        package_version = importlib.metadata.version("gurobipy")
    except Exception:
        package_version = None
    try:
        spec = importlib.util.find_spec("gurobipy._core")
        core_path = spec.origin if spec is not None else None
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
        prov = provenance(gp)
        stage = "license"
        env = gp.Env(empty=True)
        env.setParam("OutputFlag", 0)
        env.start()
        if mode == "probe":
            emit({"status": "PROBE_OK", "license_status": "accepted",
                  "provenance": prov})
            return

        model_path, timeout, seed, solution_path, log_path = (
            sys.argv[2], float(sys.argv[3]), int(sys.argv[4]), sys.argv[5], sys.argv[6]
        )
        stage = "read-model"
        model = gp.read(model_path, env=env)
        model.setParam("Threads", 1)
        model.setParam("Seed", seed)
        model.setParam("TimeLimit", timeout)
        model.setParam("MIPGap", 0.0)
        model.setParam("MIPGapAbs", 0.0)
        # Feasibility models must distinguish INFEASIBLE from INF_OR_UNBD.
        model.setParam("DualReductions", 0)
        model.setParam("LogToConsole", 0)
        model.setParam("LogFile", log_path)
        model.setParam("OutputFlag", 1)
        stage = "optimize"
        started = time.monotonic()
        model.optimize()
        optimize_wall = time.monotonic() - started
        status_code = int(attribute(model, "Status", -1))
        names = {
            1: "LOADED", 2: "OPTIMAL", 3: "INFEASIBLE",
            4: "INF_OR_UNBD", 5: "UNBOUNDED", 6: "CUTOFF",
            7: "ITERATION_LIMIT", 8: "NODE_LIMIT", 9: "TIMEOUT",
            10: "SOLUTION_LIMIT", 11: "INTERRUPTED", 12: "NUMERIC",
            13: "SUBOPTIMAL", 14: "IN_PROGRESS", 15: "USER_OBJ_LIMIT",
            16: "WORK_LIMIT", 17: "MEM_LIMIT",
        }
        solution_count = int(attribute(model, "SolCount", 0) or 0)
        solution_error = None
        if solution_count:
            try:
                model.write(solution_path)
            except Exception as error:
                solution_error = "%s: %s" % (type(error).__name__, error)
        emit({
            "status": names.get(status_code, "STATUS_%d" % status_code),
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
            "fingerprint": int(attribute(model, "Fingerprint", 0)),
            "model": {
                "rows": int(attribute(model, "NumConstrs", 0)),
                "columns": int(attribute(model, "NumVars", 0)),
                "nonzeros": int(attribute(model, "NumNZs", 0)),
                "integer_variables": int(attribute(model, "NumIntVars", 0)),
                "binary_variables": int(attribute(model, "NumBinVars", 0)),
            },
            "posture": {
                "threads": int(model.Params.Threads),
                "seed": int(model.Params.Seed),
                "time_limit_sec": float(model.Params.TimeLimit),
                "mip_gap": float(model.Params.MIPGap),
                "mip_gap_abs": float(model.Params.MIPGapAbs),
                "dual_reductions": int(model.Params.DualReductions),
                "feasibility_tolerance": float(model.Params.FeasibilityTol),
                "integer_feasibility_tolerance": float(model.Params.IntFeasTol),
            },
            "provenance": prov,
        })
    except Exception as error:
        message = str(error)
        lower = message.lower()
        license_status = "rejected" if "license" in lower else "unknown"
        if "size-limited" in lower or "size limited" in lower:
            license_status = "size-limited"
        emit({
            "status": "CHILD_ERROR", "stage": stage,
            "error_type": type(error).__name__, "error": message[:2000],
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


@dataclasses.dataclass(frozen=True)
class CorpusRow:
    index: int
    onnx_relative: str
    vnnlib_relative: str
    timeout_sec: float
    expected: str
    onnx: Path
    vnnlib: Path
    source_key: str


@dataclasses.dataclass(frozen=True)
class SatReluNetwork:
    n_inputs: int
    w1: tuple[tuple[int, ...], ...]
    b1: tuple[int, ...]
    w2: tuple[tuple[int, ...], tuple[int, ...]]
    b2: tuple[int, int]
    clauses: tuple[tuple[int, ...], ...]

    @property
    def n_hidden(self) -> int:
        return len(self.w1)


@dataclasses.dataclass(frozen=True)
class BigMEncoding:
    text: str
    n_columns: int
    n_rows: int
    input_columns: tuple[int, ...]
    hidden_columns: tuple[int, ...]
    activation_columns: tuple[tuple[int, int], ...]
    intervals: tuple[tuple[int, int], ...]

    def activation_map(self) -> dict[int, int]:
        return dict(self.activation_columns)


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
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


def relative_artifact(path: Path, root: Path) -> dict[str, Any]:
    relative = str(path.relative_to(root))
    if not path.is_file():
        return {"exists": False, "path": relative}
    stat = path.stat()
    return {
        "exists": True,
        "path": relative,
        "sha256": sha256_file(path),
        "size_bytes": stat.st_size,
    }


def formula_sha256(network: SatReluNetwork) -> str:
    body = json.dumps(
        {"n_vars": network.n_inputs, "clauses": network.clauses},
        separators=(",", ":"),
    ).encode("ascii")
    return sha256_bytes(body)


def _read_varint(data: bytes, position: int, end: int) -> tuple[int, int]:
    value = 0
    shift = 0
    for _ in range(10):
        if position >= end:
            raise ValueError("truncated protobuf varint")
        byte = data[position]
        position += 1
        value |= (byte & 0x7F) << shift
        if byte < 0x80:
            return value, position
        shift += 7
    raise ValueError("protobuf varint exceeds ten bytes")


def _proto_fields(data: bytes) -> dict[int, list[tuple[int, Any]]]:
    fields: dict[int, list[tuple[int, Any]]] = collections.defaultdict(list)
    position = 0
    while position < len(data):
        key, position = _read_varint(data, position, len(data))
        number, wire = key >> 3, key & 7
        if number == 0:
            raise ValueError("protobuf field zero is invalid")
        if wire == 0:
            value, position = _read_varint(data, position, len(data))
        elif wire == 1:
            if position + 8 > len(data):
                raise ValueError("truncated protobuf fixed64")
            value = data[position : position + 8]
            position += 8
        elif wire == 2:
            length, position = _read_varint(data, position, len(data))
            if length > len(data) - position:
                raise ValueError("truncated protobuf length-delimited value")
            value = data[position : position + length]
            position += length
        elif wire == 5:
            if position + 4 > len(data):
                raise ValueError("truncated protobuf fixed32")
            value = data[position : position + 4]
            position += 4
        else:
            raise ValueError(f"unsupported protobuf wire type {wire}")
        fields[number].append((wire, value))
    return dict(fields)


def _one(fields: dict[int, list[tuple[int, Any]]], number: int, wire: int) -> Any:
    values = fields.get(number, [])
    if len(values) != 1 or values[0][0] != wire:
        raise ValueError(f"protobuf field {number} expected one wire-{wire} value")
    return values[0][1]


def _optional(
    fields: dict[int, list[tuple[int, Any]]], number: int, wire: int, default: Any
) -> Any:
    values = fields.get(number, [])
    if not values:
        return default
    if len(values) != 1 or values[0][0] != wire:
        raise ValueError(f"protobuf field {number} expected at most one wire-{wire} value")
    return values[0][1]


def _strings(fields: dict[int, list[tuple[int, Any]]], number: int) -> list[str]:
    result = []
    for wire, value in fields.get(number, []):
        if wire != 2:
            raise ValueError(f"protobuf string field {number} has wire type {wire}")
        result.append(value.decode("utf-8", errors="strict"))
    return result


def _packed_varints(value: bytes) -> list[int]:
    result = []
    position = 0
    while position < len(value):
        item, position = _read_varint(value, position, len(value))
        result.append(item)
    return result


def _integer_f32(value: float, label: str) -> int:
    if not math.isfinite(value) or value != int(value):
        raise ValueError(f"{label} is not a finite exact integer f32: {value!r}")
    integer = int(value)
    if abs(integer) > 1_000_000:
        raise ValueError(f"{label} integer is unexpectedly large: {integer}")
    return integer


def _parse_tensor(message: bytes) -> tuple[str, tuple[int, ...], tuple[int, ...]]:
    fields = _proto_fields(message)
    name = _one(fields, 8, 2).decode("utf-8", errors="strict")
    data_type = _one(fields, 2, 0)
    if data_type != 1:
        raise ValueError(f"initializer {name!r} is not ONNX FLOAT")
    if fields.get(3) or fields.get(13) or _optional(fields, 14, 0, 0) != 0:
        raise ValueError(f"initializer {name!r} uses unsupported segment/external storage")
    dims: list[int] = []
    for wire, value in fields.get(1, []):
        if wire == 0:
            dims.append(value)
        elif wire == 2:
            dims.extend(_packed_varints(value))
        else:
            raise ValueError(f"initializer {name!r} has malformed dimensions")
    if not dims or any(dim <= 0 for dim in dims):
        raise ValueError(f"initializer {name!r} has invalid dimensions {dims}")
    if any(fields.get(number) for number in (4, 5, 6, 7, 10, 11)):
        raise ValueError(f"initializer {name!r} mixes raw and typed tensor payloads")
    raw = _one(fields, 9, 2)
    count = math.prod(dims)
    if len(raw) != count * 4:
        raise ValueError(
            f"initializer {name!r} has {len(raw)} raw bytes, expected {count * 4}"
        )
    unpacked = struct.unpack(f"<{count}f", raw)
    values = tuple(_integer_f32(value, f"{name}[{index}]") for index, value in enumerate(unpacked))
    return name, tuple(dims), values


def _parse_attribute(message: bytes) -> tuple[str, float | int]:
    fields = _proto_fields(message)
    name = _one(fields, 1, 2).decode("utf-8", errors="strict")
    if fields.get(2):
        raw = _one(fields, 2, 5)
        value: float | int = struct.unpack("<f", raw)[0]
        expected_type = 1
    elif fields.get(3):
        value = int(_one(fields, 3, 0))
        expected_type = 2
    else:
        raise ValueError(f"ONNX attribute {name!r} has no scalar value")
    attr_type = _optional(fields, 20, 0, expected_type)
    if attr_type != expected_type:
        raise ValueError(f"ONNX attribute {name!r} has inconsistent type {attr_type}")
    return name, value


def _parse_node(message: bytes) -> dict[str, Any]:
    fields = _proto_fields(message)
    attributes: dict[str, float | int] = {}
    for wire, value in fields.get(5, []):
        if wire != 2:
            raise ValueError("ONNX node attribute has malformed wire type")
        key, item = _parse_attribute(value)
        if key in attributes:
            raise ValueError(f"duplicate ONNX attribute {key!r}")
        attributes[key] = item
    return {
        "inputs": _strings(fields, 1),
        "outputs": _strings(fields, 2),
        "name": _optional(fields, 3, 2, b"").decode("utf-8", errors="strict"),
        "op": _one(fields, 4, 2).decode("utf-8", errors="strict"),
        "domain": _optional(fields, 7, 2, b"").decode("utf-8", errors="strict"),
        "attributes": attributes,
    }


def _value_info_name(message: bytes) -> str:
    return _one(_proto_fields(message), 1, 2).decode("utf-8", errors="strict")


def _validate_gemm(node: dict[str, Any], label: str) -> None:
    if node["op"] != "Gemm" or node["domain"] not in ("", "ai.onnx"):
        raise ValueError(f"{label} is not a standard-domain Gemm")
    if len(node["inputs"]) != 3 or len(node["outputs"]) != 1:
        raise ValueError(f"{label} does not have three inputs and one output")
    defaults: dict[str, float | int] = {
        "alpha": 1.0,
        "beta": 1.0,
        "transA": 0,
        "transB": 0,
    }
    unknown = set(node["attributes"]) - set(defaults)
    if unknown:
        raise ValueError(f"{label} has unsupported attributes {sorted(unknown)}")
    defaults.update(node["attributes"])
    if defaults != {"alpha": 1.0, "beta": 1.0, "transA": 0, "transB": 1}:
        raise ValueError(f"{label} has unsupported Gemm posture {defaults}")


def _recover_cnf(
    n: int,
    w1: tuple[tuple[int, ...], ...],
    b1: tuple[int, ...],
    w2: tuple[tuple[int, ...], tuple[int, ...]],
    b2: tuple[int, int],
) -> tuple[tuple[int, ...], ...]:
    hidden = len(w1)
    if not n or len(b1) != hidden or len(w2[0]) != hidden or len(w2[1]) != hidden:
        raise ValueError("sat_relu matrix dimensions are inconsistent")
    if b2 != (1, 0):
        raise ValueError("sat_relu output bias is not (1, 0)")
    identity_seen = [False] * n
    boolean_seen = [False] * n
    clauses: list[tuple[int, ...]] = []
    for i, row in enumerate(w1):
        if len(row) != n:
            raise ValueError(f"W1 row {i} has the wrong length")
        c0, c1 = w2[0][i], w2[1][i]
        if (c0, c1) == (-1, 0):
            literals: list[int] = []
            positive_entries = 0
            for j, coefficient in enumerate(row):
                if coefficient == 0:
                    continue
                if coefficient == 1:
                    positive_entries += 1
                    literals.append(-(j + 1))
                elif coefficient == -1:
                    literals.append(j + 1)
                else:
                    raise ValueError(f"clause row {i} has coefficient {coefficient}")
            if not literals or b1[i] != 1 - positive_entries:
                raise ValueError(f"clause row {i} has an invalid bias or is empty")
            clauses.append(tuple(literals))
        elif (c0, c1) == (0, 1):
            positions = [j for j, value in enumerate(row) if value != 0]
            if (
                len(positions) != 1
                or row[positions[0]] != 1
                or b1[i] != 0
                or identity_seen[positions[0]]
            ):
                raise ValueError(f"identity row {i} is malformed or duplicated")
            identity_seen[positions[0]] = True
        elif (c0, c1) == (0, -1):
            positions = [j for j, value in enumerate(row) if value != 0]
            if (
                len(positions) != 1
                or row[positions[0]] != 2
                or b1[i] != -1
                or boolean_seen[positions[0]]
            ):
                raise ValueError(f"Booleanization row {i} is malformed or duplicated")
            boolean_seen[positions[0]] = True
        else:
            raise ValueError(f"hidden row {i} has unrecognized W2 column {(c0, c1)}")
    if (
        not clauses
        or not all(identity_seen)
        or not all(boolean_seen)
        or hidden != len(clauses) + 2 * n
    ):
        raise ValueError("sat_relu gadget does not contain every required row exactly once")
    return tuple(clauses)


def parse_sat_relu_onnx(path: Path) -> SatReluNetwork:
    model_fields = _proto_fields(path.read_bytes())
    graph = _one(model_fields, 7, 2)
    graph_fields = _proto_fields(graph)
    if graph_fields.get(15):
        raise ValueError("sparse initializers are not supported")
    nodes = []
    for wire, value in graph_fields.get(1, []):
        if wire != 2:
            raise ValueError("ONNX graph node has malformed wire type")
        nodes.append(_parse_node(value))
    if len(nodes) != 3:
        raise ValueError(f"expected exactly three ONNX nodes, found {len(nodes)}")
    first, relu, second = nodes
    _validate_gemm(first, "first node")
    _validate_gemm(second, "third node")
    if (
        relu["op"] != "Relu"
        or relu["domain"] not in ("", "ai.onnx")
        or relu["attributes"]
        or len(relu["inputs"]) != 1
        or len(relu["outputs"]) != 1
        or first["outputs"] != relu["inputs"]
        or relu["outputs"] != second["inputs"][:1]
    ):
        raise ValueError("ONNX graph is not Gemm -> Relu -> Gemm")

    graph_inputs = [
        _value_info_name(value)
        for wire, value in graph_fields.get(11, [])
        if wire == 2
    ]
    graph_outputs = [
        _value_info_name(value)
        for wire, value in graph_fields.get(12, [])
        if wire == 2
    ]
    if graph_inputs != first["inputs"][:1] or graph_outputs != second["outputs"]:
        raise ValueError("ONNX graph input/output names do not match the chain")

    tensors: dict[str, tuple[tuple[int, ...], tuple[int, ...]]] = {}
    for wire, value in graph_fields.get(5, []):
        if wire != 2:
            raise ValueError("ONNX initializer has malformed wire type")
        name, dims, values = _parse_tensor(value)
        if name in tensors:
            raise ValueError(f"duplicate ONNX initializer {name!r}")
        tensors[name] = (dims, values)
    used = set(first["inputs"][1:]) | set(second["inputs"][1:])
    if set(tensors) != used:
        raise ValueError("ONNX initializers are missing, extra, or not chain-local")

    w1_dims, w1_flat = tensors[first["inputs"][1]]
    b1_dims, b1 = tensors[first["inputs"][2]]
    w2_dims, w2_flat = tensors[second["inputs"][1]]
    b2_dims, b2_raw = tensors[second["inputs"][2]]
    if len(w1_dims) != 2:
        raise ValueError("W1 is not a matrix")
    hidden, n = w1_dims
    if b1_dims != (hidden,) or w2_dims != (2, hidden) or b2_dims != (2,):
        raise ValueError("sat_relu initializer dimensions are not hxn, h, 2xh, 2")
    w1 = tuple(tuple(w1_flat[i * n : (i + 1) * n]) for i in range(hidden))
    w2 = (
        tuple(w2_flat[:hidden]),
        tuple(w2_flat[hidden : 2 * hidden]),
    )
    b2 = (b2_raw[0], b2_raw[1])
    clauses = _recover_cnf(n, w1, b1, w2, b2)
    return SatReluNetwork(n, w1, b1, w2, b2, clauses)


_DECLARE_RE = re.compile(r"^\(declare-const ([XY])_(\d+) Real\)$")
_ASSERT_RE = re.compile(
    r"^\(assert \((<=|>=) ([XY])_(\d+) ([+-]?(?:\d+(?:\.\d*)?|\.\d+))\)\)$"
)


def validate_sat_relu_vnnlib(path: Path, n_inputs: int) -> None:
    declarations: list[tuple[str, int]] = []
    assertions: list[tuple[str, str, int, Decimal]] = []
    for line_number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.split(";", 1)[0].strip()
        if not line:
            continue
        declare = _DECLARE_RE.fullmatch(line)
        if declare:
            declarations.append((declare.group(1), int(declare.group(2))))
            continue
        assertion = _ASSERT_RE.fullmatch(line)
        if assertion:
            try:
                number = Decimal(assertion.group(4))
            except InvalidOperation as error:
                raise ValueError(f"invalid decimal on VNN-LIB line {line_number}") from error
            assertions.append(
                (assertion.group(1), assertion.group(2), int(assertion.group(3)), number)
            )
            continue
        raise ValueError(f"unsupported VNN-LIB expression on line {line_number}: {line!r}")
    expected_declarations = [("X", i) for i in range(n_inputs)] + [("Y", 0), ("Y", 1)]
    if declarations != expected_declarations:
        raise ValueError("VNN-LIB declarations are not contiguous X_0..X_n-1,Y_0,Y_1")
    expected_assertions = {
        *(("<=", "X", i, Decimal(1)) for i in range(n_inputs)),
        *((">=", "X", i, Decimal(0)) for i in range(n_inputs)),
        (">=", "Y", 0, Decimal(1)),
        ("<=", "Y", 1, Decimal(0)),
    }
    if len(assertions) != len(expected_assertions) or set(assertions) != expected_assertions:
        raise ValueError("VNN-LIB is not exactly x in [0,1], Y_0>=1, Y_1<=0")


def generate_big_m(network: SatReluNetwork, name: str) -> BigMEncoding:
    n, hidden = network.n_inputs, network.n_hidden
    input_columns = tuple(range(n))
    hidden_columns = tuple(range(n, n + hidden))
    intervals: list[tuple[int, int]] = []
    unstable: list[int] = []
    for i, row in enumerate(network.w1):
        lower = network.b1[i] + sum(min(0, value) for value in row)
        upper = network.b1[i] + sum(max(0, value) for value in row)
        intervals.append((lower, upper))
        if lower < 0 < upper:
            unstable.append(i)
    activation_columns = tuple(
        (hidden_index, n + hidden + position)
        for position, hidden_index in enumerate(unstable)
    )
    activation_map = dict(activation_columns)

    columns: list[tuple[float, float, float, bool]] = []
    columns.extend((0.0, 1.0, 0.0, False) for _ in input_columns)
    for lower, upper in intervals:
        columns.append((0.0, float(max(0, upper)), 0.0, False))
    columns.extend((0.0, 1.0, 0.0, True) for _ in activation_columns)

    neg_inf, pos_inf = float("-inf"), float("inf")
    rows: list[tuple[float, float, list[tuple[int, float]]]] = []
    for i, coefficients in enumerate(network.w1):
        lower, upper = intervals[i]
        hidden_column = hidden_columns[i]
        base = [(hidden_column, 1.0)] + [
            (input_columns[j], float(-value))
            for j, value in enumerate(coefficients)
            if value
        ]
        bias = float(network.b1[i])
        if lower >= 0:
            rows.append((bias, bias, base))
        elif upper <= 0:
            # The H_i bound is fixed at zero. No redundant affine row is needed.
            continue
        else:
            activation = activation_map[i]
            rows.append((bias, pos_inf, base))
            rows.append(
                (
                    neg_inf,
                    float(network.b1[i] - lower),
                    base + [(activation, float(-lower))],
                )
            )
            rows.append(
                (neg_inf, 0.0, [(hidden_column, 1.0), (activation, float(-upper))])
            )

    rows.append(
        (
            float(1 - network.b2[0]),
            pos_inf,
            [
                (hidden_columns[i], float(value))
                for i, value in enumerate(network.w2[0])
                if value
            ],
        )
    )
    rows.append(
        (
            neg_inf,
            float(-network.b2[1]),
            [
                (hidden_columns[i], float(value))
                for i, value in enumerate(network.w2[1])
                if value
            ],
        )
    )
    text = emit_mps(columns, rows, name=re.sub(r"[^A-Za-z0-9_]", "_", name)[:30])
    return BigMEncoding(
        text=text,
        n_columns=len(columns),
        n_rows=len(rows),
        input_columns=input_columns,
        hidden_columns=hidden_columns,
        activation_columns=activation_columns,
        intervals=tuple(intervals),
    )


def assignment_satisfies(network: SatReluNetwork, assignment: Iterable[int]) -> bool:
    values = tuple(assignment)
    if len(values) != network.n_inputs or any(value not in (0, 1) for value in values):
        return False
    return all(
        any((literal > 0 and values[literal - 1] == 1) or
            (literal < 0 and values[-literal - 1] == 0) for literal in clause)
        for clause in network.clauses
    )


def exact_point(
    network: SatReluNetwork, encoding: BigMEncoding, assignment: Iterable[int]
) -> tuple[int, ...]:
    inputs = tuple(assignment)
    if not assignment_satisfies(network, inputs):
        raise ValueError("Boolean assignment does not satisfy the recovered CNF")
    hidden = tuple(
        max(0, network.b1[i] + sum(a * b for a, b in zip(row, inputs)))
        for i, row in enumerate(network.w1)
    )
    activation_map = encoding.activation_map()
    activations = []
    for hidden_index, _column in encoding.activation_columns:
        affine = network.b1[hidden_index] + sum(
            a * b for a, b in zip(network.w1[hidden_index], inputs)
        )
        activations.append(1 if affine > 0 else 0)
    point = inputs + hidden + tuple(activations)
    if len(point) != encoding.n_columns or set(activation_map) != {
        item[0] for item in encoding.activation_columns
    }:
        raise AssertionError("internal Big-M point layout mismatch")
    return point


def parse_boolean_assignments(text: str, prefix: str, count: int) -> tuple[int, ...]:
    values: dict[int, Decimal] = {}
    pattern = re.compile(
        rf"^\(?{re.escape(prefix)}(\d+)\s+([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?)\)?$"
    )
    for raw in text.splitlines():
        line = raw.strip().strip("()")
        match = pattern.fullmatch(line)
        if not match:
            continue
        index = int(match.group(1))
        if index in values:
            raise ValueError(f"duplicate assignment for {prefix}{index}")
        try:
            values[index] = Decimal(match.group(2))
        except InvalidOperation as error:
            raise ValueError(f"invalid assignment for {prefix}{index}") from error
    if set(values) != set(range(count)):
        missing = sorted(set(range(count)) - set(values))
        raise ValueError(f"assignments do not cover {prefix}0..{count - 1}; missing {missing[:8]}")
    result = []
    for index in range(count):
        value = values[index]
        if abs(value) <= BOOLEAN_TOLERANCE:
            result.append(0)
        elif abs(value - 1) <= BOOLEAN_TOLERANCE:
            result.append(1)
        else:
            raise ValueError(f"{prefix}{index}={value} is not within Boolean tolerance")
    return tuple(result)


def parse_ny_witness(text: str, count: int) -> tuple[int, ...]:
    return parse_boolean_assignments(text, "X_", count)


def parse_gurobi_solution(text: str, count: int) -> tuple[int, ...]:
    return parse_boolean_assignments(text, "X", count)


def load_corpus(corpus: Path) -> tuple[list[CorpusRow], dict[str, Any]]:
    root = corpus.expanduser().resolve(strict=True)
    instances_path = root / "instances.csv"
    rows: list[CorpusRow] = []
    with instances_path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.reader(handle)
        for index, fields in enumerate(reader):
            if len(fields) != 3:
                raise ValueError(f"instances.csv row {index + 1} does not have three fields")
            onnx_relative, vnnlib_relative, timeout_text = (item.strip() for item in fields)
            if Path(onnx_relative).is_absolute() or Path(vnnlib_relative).is_absolute():
                raise ValueError("instances.csv contains an absolute path")
            onnx = (root / onnx_relative).resolve(strict=True)
            vnnlib = (root / vnnlib_relative).resolve(strict=True)
            if root not in onnx.parents or root not in vnnlib.parents:
                raise ValueError("instances.csv path escapes the corpus root")
            try:
                timeout = float(timeout_text)
            except ValueError as error:
                raise ValueError(f"instances.csv row {index + 1} has invalid timeout") from error
            if not math.isfinite(timeout) or timeout <= 0:
                raise ValueError(f"instances.csv row {index + 1} has nonpositive timeout")
            stem = onnx.stem
            if stem.startswith("sat_"):
                expected = "sat"
            elif stem.startswith("unsat_"):
                expected = "unsat"
            else:
                raise ValueError(f"cannot infer reference label from {onnx_relative!r}")
            if Path(vnnlib_relative).stem != stem:
                raise ValueError(f"ONNX/VNN-LIB stems disagree on row {index + 1}")
            key_material = f"{onnx_relative}\0{vnnlib_relative}".encode("utf-8")
            rows.append(
                CorpusRow(
                    index=index,
                    onnx_relative=onnx_relative,
                    vnnlib_relative=vnnlib_relative,
                    timeout_sec=timeout,
                    expected=expected,
                    onnx=onnx,
                    vnnlib=vnnlib,
                    source_key=f"{stem}-{sha256_bytes(key_material)[:12]}",
                )
            )
    pairs = [(row.onnx_relative, row.vnnlib_relative) for row in rows]
    duplicate_pairs = [
        {"onnx": pair[0], "vnnlib": pair[1], "count": count}
        for pair, count in sorted(collections.Counter(pairs).items())
        if count > 1
    ]
    stats = {
        "instances_csv": file_identity(instances_path),
        "physical_rows": len(rows),
        "unique_source_pairs": len(set(pairs)),
        "expected_counts": dict(sorted(collections.Counter(row.expected for row in rows).items())),
        "duplicate_pairs": duplicate_pairs,
        "authoritative_shape": len(rows) == EXPECTED_ROWS and len(set(pairs)) == EXPECTED_UNIQUE,
    }
    return rows, stats


def validate_corpus(corpus: Path) -> tuple[list[CorpusRow], dict[str, SatReluNetwork], dict[str, Any]]:
    rows, stats = load_corpus(corpus)
    networks: dict[str, SatReluNetwork] = {}
    source_records = []
    for row in rows:
        if row.source_key in networks:
            continue
        network = parse_sat_relu_onnx(row.onnx)
        validate_sat_relu_vnnlib(row.vnnlib, network.n_inputs)
        encoding = generate_big_m(network, row.source_key)
        networks[row.source_key] = network
        source_records.append(
            {
                "source_key": row.source_key,
                "onnx": file_identity(row.onnx),
                "vnnlib": file_identity(row.vnnlib),
                "n_inputs": network.n_inputs,
                "n_hidden": network.n_hidden,
                "n_clauses": len(network.clauses),
                "formula_sha256": formula_sha256(network),
                "mps_sha256": sha256_bytes(encoding.text.encode("utf-8")),
                "mps_rows": encoding.n_rows,
                "mps_columns": encoding.n_columns,
                "mps_binary_columns": len(encoding.activation_columns),
            }
        )
    detail = {
        **stats,
        "sources": sorted(source_records, key=lambda item: item["source_key"]),
        "all_structurally_recognized": len(networks) == stats["unique_source_pairs"],
    }
    return rows, networks, detail


def controlled_environment(plan: Any) -> tuple[dict[str, str], dict[str, Any]]:
    env = dict(os.environ)
    removed: dict[str, str] = {}
    for key in sorted(list(env)):
        if key.startswith(("AY_", "NY_")) or key in RESOURCE_ENV or key in EXTRA_ROUTE_ENV:
            removed[key] = sha256_bytes(env.pop(key).encode("utf-8"))
    env.update(THREAD_ENV)
    env["MEMLIMIT"] = str(plan.memlimit_mb)
    env["NBCORE"] = str(plan.nbcore)
    if "NY_NO_CNF_ROUTE" in env:
        raise AssertionError("NY_NO_CNF_ROUTE survived environment scrubbing")
    fingerprint = hashlib.sha256()
    for key in sorted(env):
        fingerprint.update(key.encode("utf-8"))
        fingerprint.update(b"=")
        fingerprint.update(env[key].encode("utf-8"))
        fingerprint.update(b"\0")
    return env, {
        "thread_limits": dict(THREAD_ENV),
        "resource_environment": {"MEMLIMIT": env["MEMLIMIT"], "NBCORE": env["NBCORE"]},
        "removed_solver_environment_value_sha256": removed,
        "ny_no_cnf_route_present": False,
        "cnf_route_semantics": "default enabled; NY_NO_CNF_ROUTE=1 would disable it",
        "environment_sha256": fingerprint.hexdigest(),
        "gurobi_license_environment_names_present": [
            key for key in LICENSE_ENV_NAMES if key in env
        ],
        "license_environment_values_recorded": False,
    }


def git_provenance(repo: Path) -> dict[str, Any]:
    def git(*arguments: str) -> bytes:
        return subprocess.run(
            ["git", *arguments], cwd=repo, check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        ).stdout

    try:
        head = git("rev-parse", "HEAD").decode().strip()
        status = git("status", "--short", "--untracked-files=all").decode(
            "utf-8", errors="replace"
        )
        diff = git("diff", "--binary", "--no-ext-diff", "HEAD", "--", ".")
    except (OSError, subprocess.CalledProcessError) as error:
        return {"error": f"{type(error).__name__}: {error}"}
    return {
        "head": head,
        "dirty": bool(status),
        "status": status.splitlines(),
        "tracked_diff_sha256": sha256_bytes(diff),
    }


def freeze_binary(source: Path, destination: Path) -> dict[str, Any]:
    source_identity = file_identity(source)
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)
    destination.chmod(destination.stat().st_mode | 0o100)
    frozen_identity = file_identity(destination)
    if source_identity["sha256"] != frozen_identity["sha256"]:
        raise RuntimeError("binary changed while being frozen")
    return {"source": source_identity, "frozen": frozen_identity}


def validate_ny_receipt(binary: Path, ny_repo: Path) -> dict[str, Any]:
    helper = ny_repo / "vnncomp_scripts" / "submission_binary_receipt.sh"
    completed = subprocess.run(
        ["bash", str(helper), "validate", str(binary), str(ny_repo)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
    )
    receipt_path = Path(f"{binary}.receipt")
    receipt_fields = None
    if completed.returncode == 0 and receipt_path.is_file():
        parsed: dict[str, str] = {}
        for raw in receipt_path.read_text(encoding="utf-8").splitlines():
            key, separator, value = raw.partition("=")
            if not separator or not key or key in parsed:
                raise ValueError("validated NY receipt has malformed/duplicate fields")
            parsed[key] = value
        receipt_fields = parsed
    return {
        "valid": completed.returncode == 0,
        "returncode": completed.returncode,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
        "helper": file_identity(helper),
        "receipt": file_identity(receipt_path)
        if receipt_path.is_file()
        else {"path": str(receipt_path), "exists": False},
        "fields": receipt_fields,
    }


def canonical_ny_ay_commit(lock_path: Path) -> str:
    pattern = re.compile(
        r'^source = "git\+https://github\.com/alabsystems/ay\.git\?rev='
        r'([0-9a-f]{40})#([0-9a-f]{40})"$'
    )
    commits = set()
    mentions = 0
    for raw in lock_path.read_text(encoding="utf-8").splitlines():
        if "alabsystems/ay" not in raw:
            continue
        mentions += 1
        match = pattern.fullmatch(raw)
        if not match or match.group(1) != match.group(2):
            raise ValueError(f"non-canonical AY source in NY Cargo.lock: {raw!r}")
        commits.add(match.group(1))
    if mentions == 0 or len(commits) != 1:
        raise ValueError("NY Cargo.lock does not contain exactly one canonical AY revision")
    return next(iter(commits))


def command_identity(command: list[str], embedded: str | None = None) -> dict[str, Any]:
    shown = list(command)
    if embedded is not None:
        shown = [
            f"<embedded Python sha256={sha256_bytes(embedded.encode('utf-8'))}>"
            if item == embedded
            else item
            for item in shown
        ]
    raw = b"\0".join(os.fsencode(item) for item in command)
    return {"argv": shown, "argv_sha256": sha256_bytes(raw)}


def run_capture(
    command: list[str],
    *,
    plan: Any,
    timeout: float,
    env: dict[str, str],
    env_posture: dict[str, Any],
    artifact_dir: Path,
    artifact_root: Path,
    label: str,
    embedded: str | None = None,
) -> dict[str, Any]:
    artifact_dir.mkdir(parents=True, exist_ok=True)
    stdout_path = artifact_dir / "stdout.txt"
    stderr_path = artifact_dir / "stderr.txt"
    try:
        captured = run_captured(
            command,
            plan.memlimit_mb,
            timeout,
            label=label,
            env=env,
            cwd=str(REPO_ROOT),
        )
        fields = dataclasses.asdict(captured)
        stdout = fields.pop("stdout")
        stderr = fields.pop("stderr")
        launch_error = None
    except Exception as error:
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
        **command_identity(command, embedded),
        "started_at": utc_now(),
        "hard_timeout_sec": timeout,
        "memlimit_mb": plan.memlimit_mb,
        "environment": env_posture,
        **fields,
        "launch_error": launch_error,
        "stdout": relative_artifact(stdout_path, artifact_root),
        "stderr": relative_artifact(stderr_path, artifact_root),
    }


def process_clean(process: dict[str, Any]) -> bool:
    return (
        process.get("launch_error") is None
        and process.get("returncode") == 0
        and not process.get("timed_out")
        and not process.get("memout")
        and not process.get("cancelled")
        and not process.get("stdout_truncated")
        and not process.get("stderr_truncated")
    )


def last_json(text: str) -> dict[str, Any]:
    for raw in reversed(text.splitlines()):
        line = raw.strip()
        if not line.startswith("{"):
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            return value
    raise ValueError("child stdout contained no JSON object")


def artifact_text(record: dict[str, Any], artifact_root: Path) -> str:
    return (artifact_root / record["path"]).read_text(encoding="utf-8")


def run_ny(
    binary: Path,
    row: CorpusRow,
    network: SatReluNetwork,
    *,
    plan: Any,
    env: dict[str, str],
    env_posture: dict[str, Any],
    hard_grace: float,
    run_dir: Path,
    artifact_root: Path,
) -> dict[str, Any]:
    result_path = run_dir / "result.txt"
    command = [
        str(binary),
        "-v",
        "--log-format",
        "json",
        "vnncomp",
        "v1",
        "sat_relu",
        str(row.onnx),
        str(row.vnnlib),
        str(result_path),
        str(row.timeout_sec),
    ]
    process = run_capture(
        command,
        plan=plan,
        timeout=row.timeout_sec + hard_grace,
        env=env,
        env_posture=env_posture,
        artifact_dir=run_dir,
        artifact_root=artifact_root,
        label="ny_sat_relu_head_to_head.py[ny]",
    )
    output = ""
    verdict = None
    witness = ""
    result_error = None
    if result_path.is_file():
        output = result_path.read_text(encoding="utf-8")
        lines = output.splitlines()
        verdict = lines[0].strip().lower() if lines else None
        witness = "\n".join(lines[1:])
    else:
        result_error = "NY did not create the result file"
    stdout = artifact_text(process["stdout"], artifact_root)
    stderr = artifact_text(process["stderr"], artifact_root)
    telemetry = stdout + "\n" + stderr
    markers = {
        "qualifies": "CNF recovery qualifies:" in telemetry,
        "boolean_counterexample_confirmed":
            "confirmed boolean counterexample" in telemetry,
        "resolution_dag_validated":
            "resolution-DAG certificate VALIDATED" in telemetry,
        "trusted_ort_sat_upheld":
            "Trusted-oracle gate:" in telemetry and "sat upheld" in telemetry,
    }
    witness_check: dict[str, Any] = {"not_run": True}
    if verdict == "sat" and witness:
        try:
            assignment = parse_ny_witness(witness, network.n_inputs)
            witness_check = {
                "not_run": False,
                "assignment_sha256": sha256_bytes(bytes(assignment)),
                "satisfies_recovered_cnf": assignment_satisfies(network, assignment),
                "error": None,
            }
        except ValueError as error:
            witness_check = {
                "not_run": False,
                "assignment_sha256": None,
                "satisfies_recovered_cnf": False,
                "error": str(error),
            }
    correct = verdict == row.expected
    gates = markers["qualifies"] and (
        markers["resolution_dag_validated"]
        if verdict == "unsat"
        else (
            markers["boolean_counterexample_confirmed"]
            and markers["trusted_ort_sat_upheld"]
            and witness_check.get("satisfies_recovered_cnf") is True
        )
        if verdict == "sat"
        else False
    )
    valid = process_clean(process) and result_error is None and correct and gates
    return {
        "process": process,
        "verdict": verdict,
        "reference_expected": row.expected,
        "correct": correct,
        "markers": markers,
        "witness_check": witness_check,
        "valid": valid,
        "result_error": result_error,
        "result": relative_artifact(result_path, artifact_root),
    }


def write_exact_point(path: Path, point: tuple[int, ...]) -> None:
    path.write_text(
        "# exact Boolean/ReLU reconstruction from Gurobi input assignment\n"
        + "".join(f"X{index} {value}\n" for index, value in enumerate(point)),
        encoding="utf-8",
    )


def parse_point_checker(text: str) -> dict[str, Any]:
    named = None
    status = None
    for raw in text.splitlines():
        line = raw.strip()
        match = re.fullmatch(r"point: (\d+) of (\d+) columns named", line)
        if match:
            named = {"named": int(match.group(1)), "total": int(match.group(2))}
        if line.startswith("FEASIBLE"):
            status = "FEASIBLE"
        elif line.startswith("INFEASIBLE"):
            status = "INFEASIBLE"
    return {"status": status, "columns": named}


def run_gurobi(
    python: Path,
    checker: Path,
    row: CorpusRow,
    network: SatReluNetwork,
    encoding: BigMEncoding,
    mps_path: Path,
    *,
    plan: Any,
    env: dict[str, str],
    env_posture: dict[str, Any],
    hard_grace: float,
    checker_timeout: float,
    run_dir: Path,
    artifact_root: Path,
) -> dict[str, Any]:
    solution_path = run_dir / "gurobi.sol"
    log_path = run_dir / "gurobi.log"
    command = [
        str(python), "-c", GUROBI_CHILD, "solve", str(mps_path),
        str(row.timeout_sec), str(SOLVER_SEED), str(solution_path), str(log_path),
    ]
    process = run_capture(
        command,
        plan=plan,
        timeout=row.timeout_sec + hard_grace,
        env=env,
        env_posture=env_posture,
        artifact_dir=run_dir,
        artifact_root=artifact_root,
        label="ny_sat_relu_head_to_head.py[gurobi]",
        embedded=GUROBI_CHILD,
    )
    try:
        child = last_json(artifact_text(process["stdout"], artifact_root))
        parse_error = None
    except ValueError as error:
        child = None
        parse_error = str(error)
    verdict = None
    if child is not None:
        if int(child.get("solution_count") or 0) > 0:
            verdict = "sat"
        elif child.get("status") == "INFEASIBLE":
            verdict = "unsat"
        elif child.get("status") in ("TIMEOUT", "MEM_LIMIT"):
            verdict = "timeout"
        else:
            verdict = "unknown"

    point_check: dict[str, Any] = {"not_run": True, "reason": "no SAT solution"}
    if verdict == "sat" and solution_path.is_file():
        exact_path = run_dir / "exact-reconstruction.sol"
        try:
            assignment = parse_gurobi_solution(
                solution_path.read_text(encoding="utf-8"), network.n_inputs
            )
            point = exact_point(network, encoding, assignment)
            write_exact_point(exact_path, point)
            checker_dir = run_dir / "exact-checker"
            checker_command = [
                str(checker), "check-point", "--model", str(mps_path),
                "--point", str(exact_path),
            ]
            checker_process = run_capture(
                checker_command,
                plan=plan,
                timeout=checker_timeout,
                env=env,
                env_posture=env_posture,
                artifact_dir=checker_dir,
                artifact_root=artifact_root,
                label="ny_sat_relu_head_to_head.py[checker]",
            )
            parsed = parse_point_checker(
                artifact_text(checker_process["stdout"], artifact_root)
            )
            point_check = {
                "not_run": False,
                "assignment_sha256": sha256_bytes(bytes(assignment)),
                "satisfies_recovered_cnf": True,
                "reconstruction": relative_artifact(exact_path, artifact_root),
                "process": checker_process,
                "parsed": parsed,
                "valid": process_clean(checker_process)
                and parsed["status"] == "FEASIBLE"
                and parsed["columns"] == {
                    "named": encoding.n_columns, "total": encoding.n_columns
                },
                "error": None,
            }
        except (OSError, ValueError) as error:
            point_check = {
                "not_run": False,
                "assignment_sha256": None,
                "satisfies_recovered_cnf": False,
                "reconstruction": relative_artifact(exact_path, artifact_root),
                "process": None,
                "parsed": None,
                "valid": False,
                "error": f"{type(error).__name__}: {error}",
            }
    correct = verdict == row.expected
    solver_valid = (
        process_clean(process)
        and parse_error is None
        and child is not None
        and child.get("status") != "CHILD_ERROR"
        and correct
        and (point_check.get("valid") is True if verdict == "sat" else verdict == "unsat")
    )
    return {
        "process": process,
        "child": child,
        "parse_error": parse_error,
        "verdict": verdict,
        "reference_expected": row.expected,
        "correct": correct,
        "point_check": point_check,
        "solver_valid": solver_valid,
        "solution": relative_artifact(solution_path, artifact_root),
        "solver_log": relative_artifact(log_path, artifact_root),
    }


def summarize(document: dict[str, Any]) -> dict[str, Any]:
    trials = document["trials"]
    ny_valid = sum(trial.get("ny", {}).get("valid") is True for trial in trials)
    gurobi_valid = sum(
        trial.get("gurobi", {}).get("evidence_valid") is True for trial in trials
    )
    wrong = []
    invalid = []
    incomplete = []
    advantages = []
    ny_walls = []
    gurobi_walls = []
    for trial in trials:
        label = f"row-{trial['row_index']:03d}/rep-{trial['repetition']:02d}"
        ny = trial.get("ny")
        grb = trial.get("gurobi")
        if ny is not None:
            if ny.get("verdict") not in (None, trial["expected"]):
                wrong.append(f"{label}:ny")
            elif not ny.get("valid"):
                invalid.append(f"{label}:ny")
            wall = ny.get("process", {}).get("wall_sec")
            if isinstance(wall, (int, float)):
                ny_walls.append(float(wall))
        if document["selection"]["mode"] == "both":
            if grb is None:
                incomplete.append(f"{label}:gurobi-missing")
                continue
            if grb.get("verdict") not in (None, trial["expected"]):
                wrong.append(f"{label}:gurobi")
            elif not grb.get("evidence_valid"):
                if grb.get("verdict") in ("timeout", "unknown", None):
                    incomplete.append(f"{label}:gurobi")
                else:
                    invalid.append(f"{label}:gurobi")
            wall = grb.get("process", {}).get("wall_sec")
            if isinstance(wall, (int, float)):
                gurobi_walls.append(float(wall))
            if (
                ny is not None
                and ny.get("valid")
                and grb.get("evidence_valid")
                and float(ny["process"]["wall_sec"]) > float(grb["process"]["wall_sec"])
            ):
                advantages.append(
                    {
                        "trial": label,
                        "ny_wall_sec": ny["process"]["wall_sec"],
                        "gurobi_wall_sec": grb["process"]["wall_sec"],
                    }
                )
    expected_trials = document["selection"]["physical_rows"] * document["selection"]["repetitions"]
    if len(trials) < expected_trials:
        incomplete.append(f"campaign has {len(trials)} of {expected_trials} trials")
    if document.get("provenance", {}).get("post_campaign_inputs_unchanged") is False:
        invalid.append("corpus inputs changed during the campaign")
    mode = document["selection"]["mode"]
    phase0 = (
        len(trials) == expected_trials
        and ny_valid == expected_trials
        and not wrong
        and not invalid
    )
    dominance = (
        mode == "both"
        and phase0
        and gurobi_valid == expected_trials
        and not incomplete
        and not advantages
    )
    return {
        "expected_trials": expected_trials,
        "completed_trials": len(trials),
        "ny_valid_trials": ny_valid,
        "gurobi_valid_trials": gurobi_valid,
        "wrong_trials": wrong,
        "invalid_trials": invalid,
        "incomplete_trials": incomplete,
        "known_gurobi_advantages": advantages,
        "ny_wall_total_sec": sum(ny_walls) if ny_walls else None,
        "gurobi_wall_total_sec": sum(gurobi_walls) if gurobi_walls else None,
        "ny_wall_median_sec": statistics.median(ny_walls) if ny_walls else None,
        "gurobi_wall_median_sec": statistics.median(gurobi_walls) if gurobi_walls else None,
        "phase0_production_route_verified": phase0,
        "dominance_closed_on_this_campaign": dominance,
    }


def atomic_json(path: Path, document: dict[str, Any]) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(document, indent=2, sort_keys=True, allow_nan=False) + "\n",
        encoding="utf-8",
    )
    os.replace(temporary, path)


def default_output() -> Path:
    stamp = dt.datetime.now().strftime("%Y%m%d-%H%M%S")
    return REPO_ROOT / "target" / "ny-sat-relu" / f"run-{stamp}.json"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--mode", choices=("ny-only", "both"), default="both")
    parser.add_argument("--ny-repo", type=Path, default=Path.home() / "ny")
    parser.add_argument("--ny-bin", type=Path, default=None)
    parser.add_argument(
        "--ay-checker", type=Path, default=REPO_ROOT / "target" / "release" / "ay-milp"
    )
    parser.add_argument("--gurobi-python", type=Path, default=Path(sys.executable))
    parser.add_argument("--repetitions", type=int, default=1)
    parser.add_argument("--hard-timeout-grace", type=float, default=15.0)
    parser.add_argument("--checker-timeout", type=float, default=60.0)
    parser.add_argument("--out", type=Path, default=None)
    parser.add_argument("--allow-unreceipted-ny", action="store_true")
    parser.add_argument(
        "--validate-only",
        action="store_true",
        help="parse all inputs and construct every MPS in memory; run no children",
    )
    return parser


def validate_arguments(args: argparse.Namespace, parser: argparse.ArgumentParser) -> None:
    if args.repetitions <= 0:
        parser.error("--repetitions must be positive")
    if args.hard_timeout_grace <= 0 or args.checker_timeout <= 0:
        parser.error("timeouts must be positive")


def campaign_exit(summary: dict[str, Any], mode: str) -> int:
    if summary["wrong_trials"] or summary["invalid_trials"]:
        return 3
    if summary["incomplete_trials"]:
        return 2
    if mode == "ny-only":
        return 0 if summary["phase0_production_route_verified"] else 2
    if summary["known_gurobi_advantages"]:
        return 1
    return 0 if summary["dominance_closed_on_this_campaign"] else 2


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    validate_arguments(args, parser)
    corpus = args.corpus.expanduser().resolve(strict=True)
    rows, networks, corpus_detail = validate_corpus(corpus)
    if args.validate_only:
        print(
            json.dumps(
                {"schema": SCHEMA, "mode": "validate-only", "corpus": corpus_detail},
                indent=2,
                sort_keys=True,
            )
        )
        return 0 if corpus_detail["authoritative_shape"] else 2
    if not corpus_detail["authoritative_shape"]:
        parser.error(
            f"authoritative run needs {EXPECTED_ROWS} rows/{EXPECTED_UNIQUE} unique pairs; "
            f"found {corpus_detail['physical_rows']}/{corpus_detail['unique_source_pairs']}"
        )

    ny_repo = args.ny_repo.expanduser().resolve(strict=True)
    ny_lock = (ny_repo / "Cargo.lock").resolve(strict=True)
    ny_ay_commit = canonical_ny_ay_commit(ny_lock)
    ny_source = (
        args.ny_bin.expanduser().resolve(strict=True)
        if args.ny_bin is not None
        else (ny_repo / "target" / "release" / "ny").resolve(strict=True)
    )
    checker_source = args.ay_checker.expanduser().resolve(strict=True)
    gurobi_python = args.gurobi_python.expanduser().resolve(strict=True)
    receipt = validate_ny_receipt(ny_source, ny_repo)
    if not receipt["valid"] and not args.allow_unreceipted_ny:
        parser.error(
            "NY release receipt validation failed; rebuild with NY's "
            "vnncomp_scripts/build_submission_binary.sh or explicitly use "
            "--allow-unreceipted-ny for a non-authoritative exploratory run\n"
            + receipt["stderr"]
        )

    output = (args.out or default_output()).expanduser().resolve()
    artifacts = output.with_name(output.stem + ".artifacts")
    if output.exists() or artifacts.exists():
        parser.error(f"refusing to overwrite {output} or {artifacts}")
    output.parent.mkdir(parents=True, exist_ok=True)

    warn_concurrent_build()
    plan = plan_solver_resources(1, label="ny_sat_relu_head_to_head.py")
    if plan.jobs != 1:
        raise RuntimeError(f"serial harness received non-serial resource plan {plan}")
    env, env_posture = controlled_environment(plan)

    ay_git = git_provenance(REPO_ROOT)
    ny_git = git_provenance(ny_repo)
    artifacts.mkdir(parents=True)
    frozen_ny_record = freeze_binary(ny_source, artifacts / "bin" / "ny")
    frozen_checker_record = freeze_binary(checker_source, artifacts / "bin" / "ay-milp")
    frozen_ny = Path(frozen_ny_record["frozen"]["path"])
    frozen_checker = Path(frozen_checker_record["frozen"]["path"])

    model_records: dict[str, dict[str, Any]] = {}
    encodings: dict[str, BigMEncoding] = {}
    model_dir = artifacts / "models"
    model_dir.mkdir()
    for source_key, network in sorted(networks.items()):
        encoding = generate_big_m(network, source_key)
        encodings[source_key] = encoding
        mps = model_dir / f"{source_key}.mps"
        mps.write_text(encoding.text, encoding="utf-8")
        metadata = model_dir / f"{source_key}.json"
        metadata.write_text(
            json.dumps(
                {
                    "schema": "ny-sat-relu-big-m-v1",
                    "source_key": source_key,
                    "formula_sha256": formula_sha256(network),
                    "n_inputs": network.n_inputs,
                    "n_hidden": network.n_hidden,
                    "n_clauses": len(network.clauses),
                    "columns": encoding.n_columns,
                    "rows": encoding.n_rows,
                    "binary_columns": len(encoding.activation_columns),
                    "input_columns": [f"X{index}" for index in encoding.input_columns],
                    "hidden_columns": [f"X{index}" for index in encoding.hidden_columns],
                    "activation_columns": [
                        {"hidden_index": hidden, "column": f"X{column}"}
                        for hidden, column in encoding.activation_columns
                    ],
                    "translation_timed": False,
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        model_records[source_key] = {
            "mps": relative_artifact(mps, artifacts),
            "metadata": relative_artifact(metadata, artifacts),
        }

    document: dict[str, Any] = {
        "schema": SCHEMA,
        "state": "running",
        "started_at": utc_now(),
        "finished_at": None,
        "selection": {
            "mode": args.mode,
            "physical_rows": len(rows),
            "unique_source_pairs": len(networks),
            "repetitions": args.repetitions,
            "duplicates_preserved": True,
        },
        "interface_boundary": {
            "ny_input": "original ONNX + VNN-LIB",
            "gurobi_input": "deterministic full-network exact-integer Big-M MPS",
            "same_source_semantics": True,
            "identical_input_bytes": False,
            "translation_in_gurobi_timing": False,
            "gurobi_exact_point_check_in_timing": False,
            "ny_loading_route_certificate_and_ort_gate_in_timing": True,
            "existing_window_mip_dumps_used": False,
        },
        "posture": {
            "serial": True,
            "threads": 1,
            "seed": SOLVER_SEED,
            "gurobi_mip_gap": 0.0,
            "gurobi_mip_gap_abs": 0.0,
            "gurobi_dual_reductions": 0,
            "ny_info_telemetry": True,
            "solver_order": "alternating by physical row index and repetition",
            "strict_dominance_rule": "NY process wall <= Gurobi process wall on every trial",
            "environment": env_posture,
        },
        "resource_envelope": {
            "requested_jobs": 1,
            "jobs": plan.jobs,
            "memlimit_mb_per_child": plan.memlimit_mb,
            "nbcore_per_child": plan.nbcore,
            "headroom_mb": plan.headroom_mb,
            "memory_enforcement": "process-group rss_watchdog, zero grace",
            "lease": "one process-scoped host lease for the complete campaign",
        },
        "corpus": corpus_detail,
        "models": model_records,
        "provenance": {
            "harness": file_identity(Path(__file__)),
            "oom_guard": file_identity(SCRIPT_DIR / "_oom_guard.py"),
            "mps_emitter": file_identity(SCRIPT_DIR / "milp2mps.py"),
            "gurobi_child_sha256": sha256_bytes(GUROBI_CHILD.encode("utf-8")),
            "ny_binary": frozen_ny_record,
            "ay_checker_binary": frozen_checker_record,
            "ny_receipt": receipt,
            "authoritative_receipted_ny": receipt["valid"],
            "ny_cargo_lock": file_identity(ny_lock),
            "ny_pinned_ay_commit": ny_ay_commit,
            "ny_pin_matches_ay_worktree_head": ny_ay_commit == ay_git.get("head"),
            "ay_git": ay_git,
            "ny_git": ny_git,
            "gurobi_python": file_identity(gurobi_python),
            "host": {
                "node": platform.node(),
                "platform": platform.platform(),
                "machine": platform.machine(),
                "processor": platform.processor(),
                "python": sys.version,
            },
        },
        "trials": [],
        "summary": {},
    }
    document["summary"] = summarize(document)
    atomic_json(output, document)

    if args.mode == "both":
        probe_dir = artifacts / "gurobi-probe"
        probe_command = [str(gurobi_python), "-c", GUROBI_CHILD, "probe"]
        probe = run_capture(
            probe_command,
            plan=plan,
            timeout=60.0,
            env=env,
            env_posture=env_posture,
            artifact_dir=probe_dir,
            artifact_root=artifacts,
            label="ny_sat_relu_head_to_head.py[gurobi-probe]",
            embedded=GUROBI_CHILD,
        )
        try:
            probe["verdict"] = last_json(artifact_text(probe["stdout"], artifacts))
        except ValueError as error:
            probe["parse_error"] = str(error)
        document["provenance"]["gurobi_probe"] = probe
        atomic_json(output, document)

    try:
        for row in rows:
            network = networks[row.source_key]
            encoding = encodings[row.source_key]
            mps_path = artifacts / model_records[row.source_key]["mps"]["path"]
            for repetition in range(args.repetitions):
                trial: dict[str, Any] = {
                    "row_index": row.index,
                    "repetition": repetition,
                    "onnx_relative": row.onnx_relative,
                    "vnnlib_relative": row.vnnlib_relative,
                    "source_key": row.source_key,
                    "expected": row.expected,
                    "timeout_sec": row.timeout_sec,
                    "order": [],
                }
                document["trials"].append(trial)
                run_root = artifacts / "rows" / f"{row.index:03d}" / f"rep-{repetition:02d}"
                order = ["ny"] if args.mode == "ny-only" else (
                    ["ny", "gurobi"] if (row.index + repetition) % 2 == 0
                    else ["gurobi", "ny"]
                )
                trial["order"] = order
                for solver in order:
                    if solver == "ny":
                        trial["ny"] = run_ny(
                            frozen_ny, row, network,
                            plan=plan, env=env, env_posture=env_posture,
                            hard_grace=args.hard_timeout_grace,
                            run_dir=run_root / "ny", artifact_root=artifacts,
                        )
                    else:
                        trial["gurobi"] = run_gurobi(
                            gurobi_python, frozen_checker, row, network, encoding, mps_path,
                            plan=plan, env=env, env_posture=env_posture,
                            hard_grace=args.hard_timeout_grace,
                            checker_timeout=args.checker_timeout,
                            run_dir=run_root / "gurobi", artifact_root=artifacts,
                        )
                    document["summary"] = summarize(document)
                    atomic_json(output, document)
                if args.mode == "both":
                    gurobi = trial["gurobi"]
                    gurobi["unsat_reference_gate"] = (
                        "NY production route returned expected UNSAT with validated resolution DAG"
                        if gurobi.get("verdict") == "unsat" and trial["ny"].get("valid")
                        else None
                    )
                    gurobi["evidence_valid"] = bool(
                        gurobi.get("solver_valid")
                        and (
                            trial["ny"].get("valid")
                            if gurobi.get("verdict") == "unsat"
                            else True
                        )
                    )
                    document["summary"] = summarize(document)
                    atomic_json(output, document)
    except BaseException as error:
        document["state"] = "aborted"
        document["finished_at"] = utc_now()
        document["abort"] = f"{type(error).__name__}: {error}"
        document["summary"] = summarize(document)
        atomic_json(output, document)
        raise

    # Detect input mutation over a potentially long campaign.
    post_inputs = {
        source["source_key"]: {
            "onnx_sha256": sha256_file(
                next(row.onnx for row in rows if row.source_key == source["source_key"])
            ),
            "vnnlib_sha256": sha256_file(
                next(row.vnnlib for row in rows if row.source_key == source["source_key"])
            ),
        }
        for source in corpus_detail["sources"]
    }
    document["provenance"]["post_campaign_input_hashes"] = post_inputs
    initial_sources = {source["source_key"]: source for source in corpus_detail["sources"]}
    document["provenance"]["post_campaign_inputs_unchanged"] = all(
        hashes["onnx_sha256"] == initial_sources[source_key]["onnx"]["sha256"]
        and hashes["vnnlib_sha256"] == initial_sources[source_key]["vnnlib"]["sha256"]
        for source_key, hashes in post_inputs.items()
    )
    document["state"] = "complete"
    document["finished_at"] = utc_now()
    document["summary"] = summarize(document)
    atomic_json(output, document)
    print(json.dumps(document["summary"], indent=2, sort_keys=True))
    print(f"evidence: {output}", file=sys.stderr)
    return campaign_exit(document["summary"], args.mode)


if __name__ == "__main__":
    raise SystemExit(main())
