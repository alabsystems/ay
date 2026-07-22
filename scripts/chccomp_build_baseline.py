#!/usr/bin/env python3
# ay-script: chccomp-build-baseline
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Assemble a regression baseline from prior AY harness runs.

Collects every instance AY has correctly solved across the recorded runs into a
single baseline (instance -> {verdict, first_seen_tag}). The regression harness
(chccomp_regression.py) later re-runs these and FAILS on any that regress
(solved -> unsolved) or any wrong answer. This is the durable safety net that
makes long-term capability work safe: quality only ratchets up.

Usage: python scripts/chccomp_build_baseline.py [--out the development design notes]
"""
from __future__ import annotations
import argparse, glob, json, os
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
RESULTS = REPO / "evals/results/chccomp-harness"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(REPO / "the development design notes"))
    args = ap.parse_args()

    baseline: dict[str, dict] = {}
    # Scan every ay*.jsonl under the results tree.
    for path in glob.glob(str(RESULTS / "**" / "ay*.jsonl"), recursive=True):
        rel = os.path.relpath(path, RESULTS)
        parts = Path(rel).parts  # year/track/tag/ay*.jsonl
        year = parts[0] if len(parts) > 0 else "?"
        track = parts[1] if len(parts) > 1 else "?"
        tag = parts[2] if len(parts) > 2 else "?"
        for line in open(path, encoding="utf-8-sig"):
            if not line.strip():
                continue
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            inst = r.get("instance") or r.get("inst")
            if not inst:
                continue
            inst = inst.replace("\\", "/")
            status = r.get("status")
            correct = r.get("correct")
            verdict = r.get("verdict")
            # Only bank instances AY answered CORRECTLY (sat/unsat matching gt).
            if correct is True and status in ("sat", "unsat"):
                key = f"{year}/{track}/{inst}"
                wall = r.get("wall_sec") or r.get("wall") or 0.0
                if key not in baseline:
                    baseline[key] = {
                        "year": year, "track": track, "instance": inst,
                        "verdict": status, "first_tag": tag,
                        "wall": round(float(wall), 1),
                    }
                else:
                    # Keep the FASTEST observed solve time — the regression
                    # budget scales from it, so the fastest is the fair bar.
                    prev = baseline[key].get("wall", 0.0)
                    if wall and (prev == 0.0 or wall < prev):
                        baseline[key]["wall"] = round(float(wall), 1)
    # Sort for stable diffs.
    out = {k: baseline[k] for k in sorted(baseline)}
    Path(args.out).write_text(json.dumps(out, indent=1))
    by_track: dict[str, int] = {}
    for v in out.values():
        by_track[v["track"]] = by_track.get(v["track"], 0) + 1
    print(f"baseline: {len(out)} correctly-solved instances")
    for t, n in sorted(by_track.items(), key=lambda kv: -kv[1]):
        print(f"  {t}: {n}")
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
