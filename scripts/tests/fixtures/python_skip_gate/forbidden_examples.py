"""Literal forbidden constructs used only by the zero-skip gate self-test."""

import pytest
import unittest
from unittest import SkipTest

pytestmark = [pytest.mark.skip]


@unittest.skip("literal fixture")
def unittest_skip():
    raise AssertionError


@unittest.skipIf(True, "literal fixture")
def unittest_skip_if():
    raise AssertionError


@unittest.skipUnless(False, "literal fixture")
def unittest_skip_unless():
    raise AssertionError


@unittest.expectedFailure
def unittest_expected_failure():
    raise AssertionError


@pytest.mark.skip(reason="literal fixture")
def pytest_skip():
    raise AssertionError


@pytest.mark.skipif(True, reason="literal fixture")
def pytest_skip_if():
    raise AssertionError


@pytest.mark.xfail(reason="literal fixture")
def pytest_expected_failure():
    raise AssertionError


def runtime_skips(test_case):
    pytest.skip("literal fixture")
    pytest.xfail("literal fixture")
    pytest.importorskip("missing_literal_fixture")
    test_case.skipTest("literal fixture")
    raise SkipTest("literal fixture")
