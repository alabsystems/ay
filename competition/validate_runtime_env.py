#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Every `runtime_env` key a submission profile exports must be read by the solver.

# Why this exists

`knobs.rs` states the defect this guards against: `AY_MILP_NO_CUTZ=1` is a no-op, so
a campaign that sets it measures the wrong arm and records the result as a finding.
`ay-milp` gained an environment audit for that, and it covers one crate's own
process environment.

It does not cover the artifact that decides what a *scored submission* runs under.
`competition/sat_profile_matrix.json` declares a `runtime_env` block per lane, and
those keys are exported into the run environment of every solved instance. When this
checker was written, three of the eight declared keys were read by **no Rust source
in the repository**:

    AY_COMPETITION_ASYNC_COMPILE_BUDGET_MS   parallel (1000), cloud (2500)
    AY_COMPETITION_JIT_COUNTERS              experimental ("required")
    AY_COMPETITION_JIT_DEOPT_LOG             experimental ("required")

Two of them carried the literal value "required" — an unfilled template placeholder.
The submission's documented configuration was not the configuration that would run,
and nothing said so.

A key naming nothing is not a harmless leftover here: the profile matrix is how a
lane's configuration is reviewed, frozen and reproduced after the fact.

# What counts as "known", and why the bar is deliberately low

The name appearing as a quoted string **anywhere** under `crates/**/*.rs`.

That is much weaker than "is read", and the weakness is the point. A first version
of this checker looked for `env::var("NAME")` or a `const NAME: &str = "..."` binding
and reported five dead keys instead of three. The two extras —
`AY_SAT_COMPETITION_PROFILE` and `AY_SAT_PROFILE_ID` — are real: they are written
into a child process's environment and read back out of a map with `.get("…")`
(`ay-bench/src/native.rs`), never through `env::var`. A checker that blocks a
submission over a false positive gets deleted, and then the true positives go
unreported too.

So the bar is: does any Rust source in this repository so much as mention the name?
The three keys this found fail even that — they appear in
`competition/sat_profile_matrix.json` and in no `.rs` file at all.

Usage:
  competition/validate_runtime_env.py            # check every competition/*.json
  competition/validate_runtime_env.py --list     # print each key and its readers
"""
from __future__ import annotations

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
CRATES = ROOT / "crates"


def declared_keys() -> dict[str, list[str]]:
    """Every `runtime_env` key in competition/*.json -> the profiles declaring it."""
    out: dict[str, list[str]] = {}

    def walk(node, where: str) -> None:
        if isinstance(node, dict):
            ident = node.get("id") or node.get("profile_identity") or where
            env = node.get("runtime_env")
            if isinstance(env, dict):
                for key in env:
                    out.setdefault(key, []).append(str(ident))
            for value in node.values():
                walk(value, str(ident))
        elif isinstance(node, list):
            for value in node:
                walk(value, where)

    for path in sorted((ROOT / "competition").glob("*.json")):
        if path.name.endswith(".schema.json"):
            continue
        try:
            walk(json.loads(path.read_text()), path.name)
        except json.JSONDecodeError as exc:  # a malformed matrix is its own failure
            print(f"ERROR: {path}: {exc}", file=sys.stderr)
            raise SystemExit(2) from exc
    return out


def readers(name: str) -> list[str]:
    """Rust sources that mention `name` as a quoted string.

    Intentionally a mention rather than a read — see the module docstring. Keys are
    consumed through `env::var`, through a named constant, and through an env map
    the harness reads back with `.get(..)`; enumerating those forms is how a
    submission gets blocked by a checker bug.
    """
    quoted = '"' + name + '"'
    hits = []
    for path in CRATES.rglob("*.rs"):
        if "/target/" in str(path):
            continue
        try:
            text = path.read_text(errors="ignore")
        except OSError:
            continue
        if quoted in text:
            hits.append(str(path.relative_to(ROOT)))
    return hits


def main() -> int:
    keys = declared_keys()
    if not keys:
        print("no runtime_env keys declared in competition/*.json")
        return 0

    listing = "--list" in sys.argv[1:]
    dead: list[tuple[str, list[str]]] = []
    for key in sorted(keys):
        who = readers(key)
        if listing:
            print(f"{key:44} {len(who)} reader(s)  [{', '.join(keys[key])}]")
        if not who:
            dead.append((key, keys[key]))

    if dead:
        print(
            f"\nERROR: {len(dead)} runtime_env key(s) are exported by a submission "
            f"profile and read by NOTHING:",
            file=sys.stderr,
        )
        for key, profiles in dead:
            print(f"  {key:44} declared by: {', '.join(profiles)}", file=sys.stderr)
        print(
            "\nA scored run would export these and they would do nothing, so the "
            "profile does not describe the configuration that runs. Implement the "
            "key or remove it from the matrix.",
            file=sys.stderr,
        )
        return 1

    print(f"OK: all {len(keys)} runtime_env key(s) are read by the solver")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
