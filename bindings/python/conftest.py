# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Makes the `ayz3` package importable when running pytest from this directory,
# and isolates tests from each other's default-context state.

import os
import sys

sys.path.insert(0, os.path.dirname(__file__))

import pytest  # noqa: E402

try:
    import z3 as reference_z3  # noqa: E402
except ImportError as error:
    raise pytest.UsageError(
        "the ayz3 test suite requires its reference solver; install the "
        "declared dev dependencies with `pip install -e 'bindings/python[dev]'`"
    ) from error

EXPECTED_Z3_API_VERSION = "5.0.0"
if reference_z3.get_version_string() != EXPECTED_Z3_API_VERSION:
    raise pytest.UsageError(
        "the ayz3 test suite requires z3-solver==5.0.0.0 "
        f"(API {EXPECTED_Z3_API_VERSION}), found API "
        f"{reference_z3.get_version_string()}"
    )

import ayz3  # noqa: E402  (needs the sys.path insert above)


@pytest.fixture(scope="session")
def required_reference_z3():
    """Expose the mandatory, version-pinned differential-test oracle."""
    return reference_z3


@pytest.fixture(autouse=True)
def _fresh_ayz3_default_context():
    """Give every test a pristine ayz3 default context.

    ayz3's module-level default context interns constants BY NAME for the life
    of the process, and its sort-collision soundness guard (correctly) rejects
    re-declaring a name at a different sort within one context. Without this
    reset, unrelated test files that reuse a short const name at different
    sorts (e.g. Int('a') vs Bool('a')) fail depending on suite ORDER. Resetting
    before each test removes the cross-test coupling without weakening the
    guard: within a single test the guard still fires exactly as documented.
    """
    ayz3._reset_default_context()
    yield
