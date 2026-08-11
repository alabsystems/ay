#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# THE STANDING DOMINANCE GATE, on real models.
#
# The invariant this crate now enforces is:
#
#   THE PORTFOLIO MUST PROVABLY DOMINATE ITS OWN FALLBACK. For every model,
#   routing must yield a verdict at least as strong AND evidence at least as
#   strong as `AY_MILP_NO_STRUCTURE_ROUTE=1` would have.
#
# `tests/portfolio_dominance.rs` pins the mechanism on synthetic models. This
# script pins the OUTCOME on a real corpus, which is the half that actually
# discriminated when it was written:
#
#   AY_MILP_ANCHOR_FIRST_REFUSAL_MS=0     7 evidence regressions / 46   (greedy routing)
#   AY_MILP_ANCHOR_FIRST_REFUSAL_MS=1000  1 evidence regression  / 46
#   AY_MILP_ANCHOR_FIRST_REFUSAL_MS=3000  0 regressions          / 46   (the shipped default)
#
# with 46/46 models DECIDED in every arm. A gate that cannot tell those three
# apart is not a gate, which is why this exists alongside the unit tests rather
# than instead of them.
#
# Usage:  portfolio_dominance_corpus.sh <dir-of-.mps> [time-limit-secs]
# Exit:   0 clean, 1 on any verdict-axis or evidence-axis regression.
#
# SERIAL by construction. Measuring two arms under contention manufactures
# phantom differences in both directions; this loop never runs two solves at
# once and neither should its caller.

set -u
DIR=${1:?usage: portfolio_dominance_corpus.sh <dir-of-.mps> [secs]}
TL=${2:-20}
BIN=${AY_MILP_BIN:-target/release/ay-milp}

# `verify` exit codes, as an evidence rank: 0 VERIFIED > 11 PARTIAL > 10
# UNVERIFIED > anything else. This is deliberately the CONSUMER's view — what a
# third party running `ay-milp verify` actually gets — rather than an internal
# field, because the internal census is split across `Outcome` and thirteen
# session side-fields and is easy to over-read.
rank() { case "$1" in 0) echo 3;; 11) echo 2;; 10) echo 1;; *) echo 0;; esac; }
decided() { case "$1" in UNKNOWN|"") echo 0;; *) echo 1;; esac; }

fail=0
total=0
for m in "$DIR"/*.mps "$DIR"/*.mps.gz; do
  [ -e "$m" ] || continue
  total=$((total + 1))
  for arm in routed anchor; do
    rm -f "$m.ayc"
    if [ "$arm" = anchor ]; then env_pfx=(env AY_MILP_NO_STRUCTURE_ROUTE=1); else env_pfx=(env); fi
    v=$("${env_pfx[@]}" "$BIN" solve "$m" --time-limit "$TL" 2>&1 \
        | grep -E '^(INFEASIBLE|OPTIMAL|UNKNOWN|FEASIBLE|UNBOUNDED|BOUND)' | head -1 | awk '{print $1}')
    "$BIN" verify --model "$m" --cert "$m.ayc" >/dev/null 2>&1; e=$?
    if [ "$arm" = routed ]; then rv=$v; re=$e; else av=$v; ae=$e; fi
    rm -f "$m.ayc"
  done
  if [ "$(decided "$rv")" -lt "$(decided "$av")" ]; then
    echo "VERDICT REGRESSION  $(basename "$m")  routed=$rv anchor=$av"
    fail=$((fail + 1))
  elif [ "$(rank "$re")" -lt "$(rank "$ae")" ]; then
    echo "EVIDENCE REGRESSION $(basename "$m")  routed=verify:$re anchor=verify:$ae"
    fail=$((fail + 1))
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "portfolio dominance: CLEAN over $total models (no verdict or evidence regression)"
  exit 0
fi
echo "portfolio dominance: $fail REGRESSION(S) over $total models"
exit 1
