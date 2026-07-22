#!/usr/bin/env bash
# ay-script: mc2026-run
# Copyright 2026 Andrew Yates
# Model Counting Competition run script: exactly one argument (the instance
# path); result on stdout in the MC-2026 output format (format spec v1.2).
#
# Track handling is via the instance's mandatory `c t` type line — the same
# binary serves mc (Track 1/1F), wmc incl. negative weights (Track 2B), pmc
# (Track 3), mixed wmc/pmc/pwmc (Track 4), and amc-complex (Track 5B), all
# in exact arbitrary-precision arithmetic (Ranking A).
set -u

DIR="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="$DIR/target/release/ay"

# Competition budgets: 3600 s wall / 32 GB. TD gets the sharpsat-td-style
# 120 s ceiling (adaptively scaled down for small graphs); phase 1 (no-TD)
# gets 60 s before the tree decomposition is computed for large instances;
# the component cache gets 24 GiB, leaving room for the formula + learned
# clauses + the TD subprocess.
exec "$BIN" model-count "$1" \
    --decot 120 \
    --phase1 60 \
    --cache-mb 24576
