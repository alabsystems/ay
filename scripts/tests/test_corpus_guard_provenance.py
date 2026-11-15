"""Focused tests for corpus-baseline provenance validation."""

import contextlib
import importlib.util
import io
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock


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
    def test_external_json_survives_source_cleanup_on_pass_failure_and_setup(self):
        # Exercise the real report writer and comparison, without running a solver.
        for nodes, expected_exit in ((7, 0), (70, 1), (7, 2)):
            with self.subTest(expected_exit=expected_exit), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                source = root / "disposable checkout"
                reports = source / "reports"
                reports.mkdir(parents=True)
                corpus = source / "fixture corpus"
                corpus.mkdir()
                solver = source / "fixture solver"
                solver.touch()
                baseline = reports / "corpus-baseline.json"
                row = {"status": "OPTIMAL", "obj": 3.0, "wall": 0.25,
                       "nodes": 7, "work": 11, "limit": 120.0,
                       "raw": "synthetic measurement fixture"}
                if expected_exit != 2:
                    baseline.write_text(json.dumps({"head": "fixture-base", "when": "fixture",
                                                    "limit": 120.0,
                                                    "results": {"receipt-fixture": row}}))
                measured = {"receipt-fixture": {**row, "nodes": nodes}}
                output = root / "preserved run output"
                output.mkdir()
                artifact = output / "milp-corpus.json"
                args = ["corpus_guard.py", "--check", "--corpus", str(corpus),
                        "--solver", str(solver), "--json", str(artifact)]
                with mock.patch.object(sys, "argv", args), \
                        mock.patch.object(corpus_guard, "REPO", str(source)), \
                        mock.patch.object(corpus_guard, "BASELINE", str(baseline)), \
                        mock.patch.object(corpus_guard, "HISTORY", str(reports / "corpus-history.jsonl")), \
                        mock.patch.object(corpus_guard, "measure", return_value=measured) as measure, \
                        mock.patch.object(corpus_guard.subprocess, "run",
                                          return_value=SimpleNamespace(stdout="fixture-head\n")), \
                        contextlib.redirect_stdout(io.StringIO()), \
                        contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(corpus_guard.main(), expected_exit)
                measure.assert_called_once_with(str(corpus), str(solver), 120.0, 3.0, None)
                saved = artifact.read_bytes()
                payload = json.loads(saved)
                self.assertEqual(payload["results"], measured)
                self.assertEqual(payload["head"], "fixture-head")
                shutil.rmtree(source)
                self.assertEqual(artifact.read_bytes(), saved)

    def test_committed_baseline_provenance_is_valid(self):
        # Whatever the committed baseline holds: a full --baseline capture
        # clears the override map, and a row measured by hand after it must
        # name its own provenance there.
        with (REPO / "reports" / "corpus-baseline.json").open() as stream:
            baseline = json.load(stream)

        overrides = corpus_guard.validate_provenance_overrides(baseline)

        self.assertLessEqual(set(overrides), set(baseline["results"]))

    def test_overrides_render_sorted_with_their_recording_commit(self):
        overrides = corpus_guard.validate_provenance_overrides({
            "results": {"qiu": {}, "blend2": {}},
            "provenance_overrides": {
                "qiu": {
                    "measured_head": "0ce8efef2",
                    "measured_when": None,
                    "recorded_in": "4385422fe",
                },
                "blend2": {
                    "measured_head": "0ef81b835",
                    "measured_when": None,
                    "recorded_in": "0ef81b835",
                },
            },
        })

        self.assertEqual(
            corpus_guard.format_provenance_overrides(overrides),
            "blend2@0ef81b835 [recorded 0ef81b835], "
            "qiu@0ce8efef2 [recorded 4385422fe]",
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
