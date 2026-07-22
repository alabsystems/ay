# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Structural guards for the committed differential-fuzz inventory."""

from pathlib import Path

from ayz3_fuzz.gen import FRAGMENTS
from ayz3_fuzz.inventory import DEFAULT_COUNTS


def test_inventory_defaults_cover_registered_generators():
    missing = sorted(set(FRAGMENTS) - set(DEFAULT_COUNTS))
    assert not missing, f"registered fragments missing default counts: {missing}"


def test_committed_findings_cover_registered_generators():
    findings_path = Path(__file__).parents[1] / "ayz3_fuzz" / "FINDINGS.md"
    findings = findings_path.read_text(encoding="utf-8")
    missing = sorted(
        fragment
        for fragment in FRAGMENTS
        if f"| `{fragment}` (" not in findings
    )
    assert not missing, f"registered fragments missing from FINDINGS.md: {missing}"
