# ay-script: ny-sat-relu-head-to-head-tests
"""Pure-stdlib tests for the NY sat_relu head-to-head harness.

No test imports Gurobi or launches a solver.  The ONNX fixture is assembled as
raw protobuf bytes so the structural decoder and exact gadget recognizer are
tested without the third-party ``onnx`` package.
"""

import os
import struct
import sys
import tempfile
import types
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS_DIR))

import ny_sat_relu_head_to_head as harness  # noqa: E402


def varint(value):
    encoded = bytearray()
    while value >= 0x80:
        encoded.append((value & 0x7F) | 0x80)
        value >>= 7
    encoded.append(value)
    return bytes(encoded)


def field_varint(number, value):
    return varint(number << 3) + varint(value)


def field_bytes(number, value):
    return varint((number << 3) | 2) + varint(len(value)) + value


def tensor(name, dims, values):
    packed_dims = b"".join(varint(value) for value in dims)
    raw = struct.pack(f"<{len(values)}f", *values)
    return b"".join(
        (
            field_bytes(1, packed_dims),
            field_varint(2, 1),
            field_bytes(8, name.encode()),
            field_bytes(9, raw),
        )
    )


def int_attribute(name, value):
    return b"".join(
        (field_bytes(1, name.encode()), field_varint(3, value), field_varint(20, 2))
    )


def node(inputs, outputs, operation, attributes=()):
    pieces = [field_bytes(1, value.encode()) for value in inputs]
    pieces.extend(field_bytes(2, value.encode()) for value in outputs)
    pieces.append(field_bytes(4, operation.encode()))
    pieces.extend(field_bytes(5, value) for value in attributes)
    return b"".join(pieces)


def value_info(name):
    return field_bytes(1, name.encode())


def sat_relu_model(output_bias=(1.0, 0.0)):
    # One CNF variable, clause (x1), then the required identity and
    # Booleanization rows.  A satisfying Boolean assignment is x1=true.
    initializers = (
        tensor("w1", (3, 1), (-1.0, 1.0, 2.0)),
        tensor("b1", (3,), (1.0, 0.0, -1.0)),
        tensor("w2", (2, 3), (-1.0, 0.0, 0.0, 0.0, 1.0, -1.0)),
        tensor("b2", (2,), output_bias),
    )
    nodes = (
        node(("input", "w1", "b1"), ("linear",), "Gemm", (int_attribute("transB", 1),)),
        node(("linear",), ("relu",), "Relu"),
        node(("relu", "w2", "b2"), ("output",), "Gemm", (int_attribute("transB", 1),)),
    )
    graph = b"".join(
        [field_bytes(1, value) for value in nodes]
        + [field_bytes(5, value) for value in initializers]
        + [field_bytes(11, value_info("input")), field_bytes(12, value_info("output"))]
    )
    return field_bytes(7, graph)


def vnnlib_text():
    return "\n".join(
        (
            "(declare-const X_0 Real)",
            "(declare-const Y_0 Real)",
            "(declare-const Y_1 Real)",
            "(assert (<= X_0 1.0))",
            "(assert (>= X_0 0.0))",
            "(assert (>= Y_0 1.0))",
            "(assert (<= Y_1 0.0))",
            "",
        )
    )


def clean_process(wall):
    return {
        "launch_error": None,
        "returncode": 0,
        "timed_out": False,
        "memout": False,
        "cancelled": False,
        "stdout_truncated": False,
        "stderr_truncated": False,
        "wall_sec": wall,
    }


class StructuralDecoderTest(unittest.TestCase):
    def test_raw_onnx_is_recognized_and_encoded(self):
        with tempfile.TemporaryDirectory() as directory:
            onnx = Path(directory, "sat_v1_c1.onnx")
            spec = Path(directory, "sat_v1_c1.vnnlib")
            onnx.write_bytes(sat_relu_model())
            spec.write_text(vnnlib_text())
            network = harness.parse_sat_relu_onnx(onnx)
            harness.validate_sat_relu_vnnlib(spec, network.n_inputs)

        self.assertEqual(network.n_inputs, 1)
        self.assertEqual(network.n_hidden, 3)
        self.assertEqual(network.clauses, ((1,),))
        encoding = harness.generate_big_m(network, "fixture")
        self.assertEqual(encoding.n_columns, 5)  # input + 3 H + Booleanization A
        self.assertEqual(len(encoding.activation_columns), 1)
        self.assertIn("'INTORG'", encoding.text)
        self.assertIn("OBJSENSE", encoding.text)
        point = harness.exact_point(network, encoding, (1,))
        self.assertEqual(point, (1, 0, 1, 1, 1))

    def test_output_bias_mutation_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            onnx = Path(directory, "mutated.onnx")
            onnx.write_bytes(sat_relu_model(output_bias=(0.0, 0.0)))
            with self.assertRaisesRegex(ValueError, "output bias"):
                harness.parse_sat_relu_onnx(onnx)

    def test_extra_vnnlib_assertion_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            spec = Path(directory, "mutated.vnnlib")
            spec.write_text(vnnlib_text() + "(assert (>= Y_1 -1.0))\n")
            with self.assertRaisesRegex(ValueError, "not exactly"):
                harness.validate_sat_relu_vnnlib(spec, 1)


class AssignmentGateTest(unittest.TestCase):
    def setUp(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory, "model.onnx")
            path.write_bytes(sat_relu_model())
            self.network = harness.parse_sat_relu_onnx(path)

    def test_ny_witness_requires_all_boolean_inputs(self):
        self.assertEqual(harness.parse_ny_witness("((X_0 0.9999999))", 1), (1,))
        with self.assertRaisesRegex(ValueError, "Boolean tolerance"):
            harness.parse_ny_witness("((X_0 0.5))", 1)

    def test_gurobi_solution_is_replayed_against_cnf(self):
        assignment = harness.parse_gurobi_solution("# solution\nX0 1\n", 1)
        self.assertTrue(harness.assignment_satisfies(self.network, assignment))
        self.assertFalse(harness.assignment_satisfies(self.network, (0,)))


class PostureAndSummaryTest(unittest.TestCase):
    def test_ny_lock_requires_one_matching_canonical_ay_revision(self):
        commit = "a" * 40
        with tempfile.TemporaryDirectory() as directory:
            lock = Path(directory, "Cargo.lock")
            lock.write_text(
                'source = "git+https://github.com/alabsystems/ay.git?rev='
                f'{commit}#{commit}"\n'
            )
            self.assertEqual(harness.canonical_ny_ay_commit(lock), commit)
            lock.write_text(
                'source = "git+https://github.com/alabsystems/ay.git?rev='
                f'{commit}#{"b" * 40}"\n'
            )
            with self.assertRaisesRegex(ValueError, "non-canonical"):
                harness.canonical_ny_ay_commit(lock)

    def test_environment_scrubs_kill_switch_and_forces_one_thread(self):
        plan = types.SimpleNamespace(memlimit_mb=4096, nbcore=1)
        old = dict(os.environ)
        try:
            os.environ["NY_NO_CNF_ROUTE"] = "1"
            os.environ["AY_MILP_EXAMPLE"] = "1"
            os.environ["GPU_AVAILABLE"] = "1"
            env, posture = harness.controlled_environment(plan)
        finally:
            os.environ.clear()
            os.environ.update(old)
        self.assertNotIn("NY_NO_CNF_ROUTE", env)
        self.assertNotIn("AY_MILP_EXAMPLE", env)
        self.assertNotIn("GPU_AVAILABLE", env)
        self.assertEqual(env["RAYON_NUM_THREADS"], "1")
        self.assertEqual(env["MEMLIMIT"], "4096")
        self.assertFalse(posture["ny_no_cnf_route_present"])
        self.assertIn("default enabled", posture["cnf_route_semantics"])

    def document(self, ny_wall=1.0, gurobi_wall=2.0):
        return {
            "selection": {"mode": "both", "physical_rows": 1, "repetitions": 1},
            "provenance": {},
            "trials": [
                {
                    "row_index": 0,
                    "repetition": 0,
                    "expected": "sat",
                    "ny": {
                        "valid": True,
                        "verdict": "sat",
                        "process": clean_process(ny_wall),
                    },
                    "gurobi": {
                        "evidence_valid": True,
                        "verdict": "sat",
                        "process": clean_process(gurobi_wall),
                    },
                }
            ],
        }

    def test_strict_per_trial_wall_detects_gurobi_advantage(self):
        summary = harness.summarize(self.document(ny_wall=2.01, gurobi_wall=2.0))
        self.assertEqual(len(summary["known_gurobi_advantages"]), 1)
        self.assertFalse(summary["dominance_closed_on_this_campaign"])

    def test_equal_wall_closes_trial(self):
        summary = harness.summarize(self.document(ny_wall=2.0, gurobi_wall=2.0))
        self.assertEqual(summary["known_gurobi_advantages"], [])
        self.assertTrue(summary["dominance_closed_on_this_campaign"])

    def test_input_mutation_invalidates_campaign(self):
        document = self.document()
        document["provenance"]["post_campaign_inputs_unchanged"] = False
        summary = harness.summarize(document)
        self.assertIn("corpus inputs changed during the campaign", summary["invalid_trials"])


if __name__ == "__main__":
    unittest.main()
