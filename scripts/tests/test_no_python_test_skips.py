# ay-script: no-python-test-skips-tests
"""Self-tests for the first-party Python zero-skip quality gate."""

from pathlib import Path
import sys
import unittest


SCRIPTS = Path(__file__).resolve().parents[1]
REPO_ROOT = SCRIPTS.parent
sys.path.insert(0, str(SCRIPTS))

import check_no_python_test_skips as gate  # noqa: E402


class PythonSkipGateTest(unittest.TestCase):
    def test_literal_fixture_exercises_every_forbidden_family(self):
        fixture = (
            Path(__file__).parent
            / "fixtures"
            / "python_skip_gate"
            / "forbidden_examples.py"
        )
        findings = gate.scan_path(fixture)
        constructs = {finding.construct for finding in findings}
        self.assertEqual(
            constructs,
            {
                "pytest.importorskip",
                "pytest.mark.skip",
                "pytest.mark.skipif",
                "pytest.mark.xfail",
                "pytest.skip",
                "pytest.xfail",
                "test_case.skipTest",
                "unittest.SkipTest",
                "unittest.expectedFailure",
                "unittest.skip",
                "unittest.skipIf",
                "unittest.skipUnless",
            },
        )

    def test_aliases_and_star_imports_cannot_evade_gate(self):
        source = """
import pytest as pt
import unittest as ut
from unittest import skipIf as conditional
from unittest import *

@pt.mark.xfail(reason="alias")
def a():
    pass

@ut.skip("alias")
def b():
    pass

@conditional(True, "alias")
def c():
    pass

@skipUnless(False, "star import")
def d():
    pass
"""
        constructs = {
            finding.construct
            for finding in gate.scan_source(source, Path("aliases.py"))
        }
        self.assertEqual(
            constructs,
            {
                "pytest.mark.xfail",
                "unittest.skip",
                "unittest.skipIf",
                "unittest.skipUnless",
            },
        )

    def test_bare_marker_references_cannot_evade_gate(self):
        source = """
import pytest

pytestmark = [pytest.mark.skip]
case = pytest.param(1, marks=pytest.mark.xfail)
"""
        constructs = {
            finding.construct
            for finding in gate.scan_source(source, Path("bare_markers.py"))
        }
        self.assertEqual(
            constructs,
            {"pytest.mark.skip", "pytest.mark.xfail"},
        )

    def test_comments_docstrings_and_literal_source_are_not_active(self):
        source = '''
"""pytest.skip("not active")"""
# @unittest.skip("not active")
EXAMPLE = "@pytest.mark.xfail(reason='not active')"
'''
        self.assertEqual(gate.scan_source(source, Path("literals.py")), [])

    def test_syntax_errors_fail_closed(self):
        findings = gate.scan_source("def broken(:\\n", Path("broken.py"))
        self.assertEqual(len(findings), 1)
        self.assertIn("syntax error", findings[0].construct)

    def test_default_discovery_excludes_only_declared_external_and_fixture_trees(self):
        self.assertTrue(
            gate._is_default_excluded(
                Path("scripts/tests/fixtures/python_skip_gate/example.py")
            )
        )
        for path in (
            "external/example.py",
            "reference/example.py",
            "third_party/example.py",
            "vendor/example.py",
            "vendors/example.py",
        ):
            self.assertTrue(gate._is_default_excluded(Path(path)), path)
        self.assertFalse(
            gate._is_default_excluded(Path("bindings/python/tests/test_core.py"))
        )

    def test_repository_has_no_active_first_party_python_skips(self):
        files = gate.discover_tracked_python_files(REPO_ROOT)
        findings = gate.scan_files(files)
        self.assertEqual(
            findings,
            [],
            "\\n".join(finding.render(REPO_ROOT) for finding in findings),
        )


if __name__ == "__main__":
    unittest.main()
