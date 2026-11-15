# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Structural guards for the committed differential-fuzz inventory.

The companion guard over the committed findings file lives in
test_fuzz_findings_snapshot.py; that file and the findings it reads do not
ship in the public snapshot.
"""

from ayz3_fuzz.gen import FRAGMENTS
from ayz3_fuzz.inventory import DEFAULT_COUNTS


def test_inventory_defaults_cover_registered_generators():
    missing = sorted(set(FRAGMENTS) - set(DEFAULT_COUNTS))
    assert not missing, f"registered fragments missing default counts: {missing}"
