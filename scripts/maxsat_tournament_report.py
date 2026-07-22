#!/usr/bin/env python3
# ay-script: maxsat-tournament-report
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Merge `ay maxsat bench --solver` JSON reports into a same-hardware
tournament leaderboard per track.

Usage: scripts/maxsat_tournament_report.py <track> <report.json> [...]
Every report must cover the same instance directory; solvers are scored on
the INTERSECTION of instances present in all reports (guards against
partial runs), with solved = verified OPTIMUM/UNSAT and PAR-2 at the
runs' timeout.
"""

import json
import sys


def main():
    track = sys.argv[1]
    reports = []
    for path in sys.argv[2:]:
        doc = json.load(open(path))
        reports.append(
            (
                doc.get("solver", path),
                doc["timeout"],
                {r["instance"]: r for r in doc["results"]},
            )
        )

    timeout = reports[0][1]
    assert all(t == timeout for _, t, _ in reports), "timeout mismatch"
    common = set(reports[0][2])
    for _, _, rows in reports[1:]:
        common &= set(rows)
    common = sorted(common)

    print(f"### Same-hardware tournament — {track}: "
          f"{len(common)} instances, {timeout:.0f}s\n")
    print("| rank | solver | solved | PAR-2 | wrong | errors |")
    print("|-----:|--------|-------:|------:|------:|-------:|")

    scored = []
    for name, _, rows in reports:
        solved = wrong = errors = 0
        par2 = 0.0
        for inst in common:
            r = rows[inst]
            if r["status"] in ("OPTIMUM", "UNSAT"):
                solved += 1
                par2 += r["seconds"]
            else:
                par2 += 2 * timeout
                if r["status"] == "WRONG":
                    wrong += 1
                elif r["status"] == "ERROR":
                    errors += 1
        scored.append((name, solved, par2 / len(common), wrong, errors))

    scored.sort(key=lambda x: (-x[1], x[2]))
    for i, (name, solved, par2, wrong, errors) in enumerate(scored, 1):
        print(f"| {i} | {name} | {solved} | {par2:.2f} | {wrong} | {errors} |")
    print()


if __name__ == "__main__":
    main()
