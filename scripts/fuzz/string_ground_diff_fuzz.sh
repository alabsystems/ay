#!/usr/bin/env bash
# ay-script: string-ground-diff-fuzz
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Scale runner for the differential fuzz harness that guards the proof
# checker's INDEPENDENT ground string/regex evaluator
# (crates/ay-proof/src/checker/string_ground.rs — the validator behind
# `TheoryLemmaKind::StringGroundEval` / Alethe `:rule string_ground_eval`).
#
# That evaluator is the last line of defense for AY's self-certified UNSAT on
# ground QF_S / QF_SLIA refutations: if it calls a clause a tautology when it
# is not, AY emits a WRONG `unsat` and certifies it itself. It shares no code
# with the solver, so it needs an EXTERNAL cross-check — and the project's
# directive is that AY stands on its own evidence, so NO z3 is used here.
# The cross-checks are AY's own independently-written evaluators plus a spec
# model written directly from SMT-LIB 2.6:
#
#   1. the checker under test        (memoized interval matcher)
#   2. ay_strings::we_regex::WeRegex::matches   (Brzozowski derivatives)
#   3. ay_strings::ground_eval_in_re / ay_strings::eval::*  (solver side)
#   4. a spec model in the harness   (boolean interval matrices — adjudicator)
#
# Usage:
#   bash scripts/fuzz/string_ground_diff_fuzz.sh              # 10000 per lane
#   bash scripts/fuzz/string_ground_diff_fuzz.sh 50000        # 50000 per lane
#   bash scripts/fuzz/string_ground_diff_fuzz.sh 10000 12345  # explicit seed
#   AY_SGF_SWEEP=8 bash scripts/fuzz/string_ground_diff_fuzz.sh 10000
#       # 8 consecutive seeds, 10000 cases per lane per seed
#
# Exit code 0 iff every lane reports `disagreements=0`. Any disagreement is a
# hard failure: on the checker's side it is a latent WRONG-UNSAT.

set -euo pipefail

CASES="${1:-10000}"
SEED="${2:-20260721}"
SWEEP="${AY_SGF_SWEEP:-1}"

cd "$(dirname "$0")/../.."

echo "== building the harness (release: the lanes are compute-bound) =="
cargo build --release -p ay-proof --tests

status=0
for ((k = 0; k < SWEEP; k++)); do
  seed=$((SEED + k))
  echo
  echo "== seed=${seed} cases-per-lane=${CASES} =="
  if AY_SGF_SEED="${seed}" AY_SGF_CASES="${CASES}" \
    cargo test --release -p ay-proof --test string_ground_diff_fuzz -- \
      --nocapture --test-threads 3; then
    :
  else
    status=1
    echo "!! DISAGREEMENT at seed=${seed} (cases=${CASES})"
  fi
done

if [ "${status}" -eq 0 ]; then
  echo
  echo "OK: ${SWEEP} seed(s) x ${CASES} cases/lane x 3 lanes — 0 disagreements"
fi
exit "${status}"
