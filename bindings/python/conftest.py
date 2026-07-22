# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Makes the `ayz3` package importable when running pytest from this directory,
# and isolates tests from each other's default-context state.

import os
import sys

sys.path.insert(0, os.path.dirname(__file__))

import ayz3  # noqa: E402  (needs the sys.path insert above)
import pytest  # noqa: E402


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
