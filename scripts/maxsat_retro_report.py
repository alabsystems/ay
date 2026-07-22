#!/usr/bin/env python3
# ay-script: maxsat-retro-report
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Summarize `ay maxsat bench` JSON reports into the retroactive MSE
leaderboard markdown (results/maxsat-2025-retroactive.md).

Usage: scripts/maxsat_retro_report.py <track:json:fieldcsv> [...]
  e.g. scripts/maxsat_retro_report.py \
      unweighted:results/maxsat-mse24-unweighted.json:benchmarks/maxsat/mse24/field-exact-unweighted.csv \
      weighted:results/maxsat-mse24-weighted.json:benchmarks/maxsat/mse24/field-exact-weighted.csv
"""

import csv
import json
import sys


def load_field(path):
    with open(path) as f:
        rows = list(csv.reader(f))
    header = rows[0]
    solvers = header[2:]
    data = {}
    for row in rows[1:]:
        times = [float(c) if c.strip() else None for c in row[2:]]
        data[row[0]] = times
    return solvers, data


def leaderboard(track, report_path, field_path):
    report = json.load(open(report_path))
    timeout = report["timeout"]
    results = report["results"]
    solvers, field = load_field(field_path)

    n = len(results)
    rows = []
    for si, solver in enumerate(solvers):
        solved, par2 = 0, 0.0
        for r in results:
            t = field.get(r["instance"], [None] * len(solvers))[si]
            if t is not None and t <= timeout:
                solved += 1
                par2 += t
            else:
                par2 += 2 * timeout
        rows.append((solver, solved, par2 / n))

    ay_solved = sum(1 for r in results if r["status"] in ("OPTIMUM", "UNSAT"))
    ay_par2 = (
        sum(
            r["seconds"] if r["status"] in ("OPTIMUM", "UNSAT") else 2 * timeout
            for r in results
        )
        / n
    )
    wrong = sum(1 for r in results if r["status"] == "WRONG")
    rows.append(("**AY**", ay_solved, ay_par2))
    rows.sort(key=lambda x: (-x[1], x[2]))

    lines = [
        f"### {track.capitalize()} track — {n} instances, {timeout:.0f}s timeout",
        "",
        f"AY wrong results: **{wrong}** (every reported optimum is verified"
        " against the reported model and the MSE 2024 known optima).",
        "",
        "| rank | solver | solved | PAR-2 |",
        "|-----:|--------|-------:|------:|",
    ]
    for i, (name, solved, par2) in enumerate(rows, 1):
        lines.append(f"| {i} | {name} | {solved} | {par2:.2f} |")
    lines.append("")
    return lines


def main():
    out = [
        "# Retroactive MaxSAT Evaluation 2025 — AY vs the standing field",
        "",
        "MSE 2025 was cancelled by its organizers, so the most recent held",
        "evaluation (MSE 2024) defines the standing competitive field. Every",
        "solver below is scored on **exactly the same instances** at the",
        "**same wall-clock timeout**, using the official MSE 2024 per-instance",
        "runtimes for the field and fresh local runs for AY",
        "(`ay maxsat bench`). Reference-solver runtimes come from MSE 2024",
        "hardware; AY runs locally (per the goal: algorithms, not hardware,",
        "are the subject).",
        "",
    ]
    for spec in sys.argv[1:]:
        track, report_path, field_path = spec.split(":")
        out.extend(leaderboard(track, report_path, field_path))
    print("\n".join(out))


if __name__ == "__main__":
    main()
