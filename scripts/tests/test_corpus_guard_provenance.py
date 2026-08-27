"""Focused tests for corpus-baseline provenance validation."""

import importlib.util
import json
import sys
import unittest
from pathlib import Path


SCRIPTS = Path(__file__).resolve().parents[1]
REPO = SCRIPTS.parent


def load_script(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


corpus_guard = load_script(
    "corpus_guard_under_test", SCRIPTS / "corpus_guard.py"
)


class CorpusGuardProvenanceTest(unittest.TestCase):
    def test_committed_composite_baseline_is_explicit_and_valid(self):
        with (REPO / "reports" / "corpus-baseline.json").open() as stream:
            baseline = json.load(stream)

        overrides = corpus_guard.validate_provenance_overrides(baseline)

        self.assertEqual(set(overrides), {"blend2", "qiu", "qnet1"})
        self.assertEqual(
            corpus_guard.format_provenance_overrides(overrides),
            "blend2@0ef81b835 [recorded 0ef81b835], "
            "qiu@0ce8efef2 [recorded 4385422fe], "
            "qnet1@5955651bf [recorded 5955651bf]",
        )

    def test_override_must_name_a_result(self):
        payload = {
            "results": {"known": {}},
            "provenance_overrides": {
                "missing": {
                    "measured_head": "abc",
                    "measured_when": None,
                    "recorded_in": "def",
                }
            },
        }

        with self.assertRaisesRegex(ValueError, "missing result"):
            corpus_guard.validate_provenance_overrides(payload)

    def test_unknown_measurement_time_must_be_null(self):
        payload = {
            "results": {"known": {}},
            "provenance_overrides": {
                "known": {
                    "measured_head": "abc",
                    "measured_when": 123,
                    "recorded_in": "def",
                }
            },
        }

        with self.assertRaisesRegex(ValueError, "string or null"):
            corpus_guard.validate_provenance_overrides(payload)


if __name__ == "__main__":
    unittest.main()
