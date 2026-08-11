#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0
"""The refutation ledger: negative results that can be re-derived, and the citations that rest on them.

# Why this exists

`knobs.rs` states the project's rule for keeping ~350 environment switches:

    the negative results are only RE-CHECKABLE while their arms still exist. Losing
    the ability to re-derive a negative result is how a project pays twice for the
    same work.

The arms do exist. Nothing ever re-derives them, and nothing notices when the ground
a refutation stood on moves. A result recorded against an engine that has since
changed is an assertion about a binary that no longer exists.

# The documented failure this catches

`refutations/separator-family-selection.toml` records it to the hour:

    22:36  a42365dd7  the unbounded-column cut bail is removed. "18 more instances
                      separate"; zero-cut instances 28 -> 10.
    23:38  79121c416  "separator-family selection is CLOSED" is recorded, premised
                      on family inertness measured BEFORE that change.
    06:46  1c1ce672c  odd-cycle revived -- the first verdict gained from a
                      performance change in the whole campaign -- while CITING the
                      now-stale refutation as a reason not to broaden zero-half.

An eight-hour half-life, still being cited. That is what a citation graph makes
impossible to do silently.

# What this is and is not

This is `reverse experiments` / `long-term holdouts` from production A/B practice,
made affordable and exact by immortal byte-identical arms. Those techniques are
known and "require discipline and incur technical debt" precisely because the
rejected arm has to be kept alive; here `knobs.rs` keeps it alive by policy. The
claim is that combination, not a new artifact class.

Usage:
  scripts/refutation_ledger.py            # validate records, report stale citations
  scripts/refutation_ledger.py --graph    # print the full citation graph
"""
from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEDGER = ROOT / "refutations"
SCANNED = ("crates", "reports", "designs", "scripts")

REQUIRED = ("id", "claim", "status", "source", "premise")
VALID_STATUS = ("LIVE", "STALE", "REFUTED_AGAIN")


def parse(path: pathlib.Path) -> dict:
    """A deliberately tiny TOML subset: `key = "value"` and `key = ["a", "b"]`.

    No dependency, because this runs in CI next to `tests/env_ledger.rs` and a
    checker that needs installing is a checker that gets skipped.
    """
    out: dict[str, object] = {}
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        m = re.match(r'^(\w+)\s*=\s*(.+)$', line)
        if not m:
            continue
        key, raw = m.group(1), m.group(2).strip()
        if raw.startswith("["):
            out[key] = re.findall(r'"([^"]*)"', raw)
        else:
            out[key] = raw.strip('"')
    out["_path"] = str(path.relative_to(ROOT))
    return out


def citations(tag: str) -> list[str]:
    """Files mentioning `tag`, excluding the ledger record that defines it."""
    hits = []
    for top in SCANNED:
        base = ROOT / top
        if not base.is_dir():
            continue
        for p in base.rglob("*"):
            if not p.is_file() or "/target/" in str(p):
                continue
            if p.suffix not in (".rs", ".md", ".py", ".toml", ".sh"):
                continue
            try:
                if tag in p.read_text(errors="ignore"):
                    hits.append(str(p.relative_to(ROOT)))
            except OSError:
                continue
    return sorted(hits)


def main() -> int:
    if not LEDGER.is_dir():
        print(f"no ledger at {LEDGER}", file=sys.stderr)
        return 0

    records = [parse(p) for p in sorted(LEDGER.glob("*.toml"))]
    if not records:
        print("refutation ledger is empty")
        return 0

    problems: list[str] = []
    graph = "--graph" in sys.argv[1:]

    for r in records:
        for field in REQUIRED:
            if not r.get(field):
                problems.append(f"{r['_path']}: missing required field `{field}`")
        status = r.get("status")
        if status not in VALID_STATUS:
            problems.append(f"{r['_path']}: status {status!r} not one of {VALID_STATUS}")
        # A stale record must say what killed it. "Probably out of date" is not a
        # finding anybody can act on.
        if status == "STALE" and not (r.get("invalidated_by") and r.get("reason")):
            problems.append(
                f"{r['_path']}: STALE needs `invalidated_by` (a commit) and `reason` "
                f"(the specific fact that moved)"
            )

    stale_cites: list[str] = []
    for r in records:
        tags = r.get("tags") or []
        if isinstance(tags, str):
            tags = [tags]
        for tag in tags:
            # The record itself and the report it was recorded in are not
            # CITATIONS -- they are where the refutation lives. A consumer is
            # something that declines work because of it.
            own = {r["_path"], r.get("source", "")}
            where = [w for w in citations(tag) if w not in own]
            if graph:
                print(f"{r['id']:34} [{r['status']:5}] {tag:38} {len(where)} citation(s)")
                for w in where:
                    print(f"    {w}")
            if r.get("status") == "STALE" and where:
                for w in where:
                    stale_cites.append(f"  {w}\n      cites {tag} ({r['id']}), "
                                       f"invalidated by {r.get('invalidated_by')}")

    if problems:
        print("\nERROR: malformed refutation records:", file=sys.stderr)
        for p in problems:
            print(f"  {p}", file=sys.stderr)
        return 2

    if stale_cites:
        print(
            f"\nERROR: {len(stale_cites)} citation(s) of a STALE refutation. A refutation "
            f"whose premise has moved cannot be used to decline work:",
            file=sys.stderr,
        )
        for c in stale_cites:
            print(c, file=sys.stderr)
        print(
            "\nEither re-derive the refutation against the current engine and set status "
            "back to LIVE, or stop citing it.",
            file=sys.stderr,
        )
        return 1

    live = sum(1 for r in records if r.get("status") == "LIVE")
    print(f"OK: {len(records)} refutation(s), {live} live, no citation of a stale one")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
