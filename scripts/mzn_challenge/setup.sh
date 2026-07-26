#!/usr/bin/env bash
# ay-script: mzn-setup
# Reconstitute the MiniZinc Challenge 2025 harness on a fresh machine:
#   1. verify minizinc + gtimeout (brew installs the MiniZinc toolchain)
#   2. register AY as a MiniZinc solver (org.ay.ay)
#   3. use the pinned `ay corpus` manifest entries to fetch the 2025 corpus and
#      official results.json
# The corpus lands in benchmarks/minizinc/challenge-2025/ (gitignored, ~large).
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
DATA="$REPO/benchmarks/minizinc/challenge-2025/mznc2025_probs"
RESULTS="$REPO/benchmarks/minizinc/challenge-2025/results-2025.json"
AY_BIN="$REPO/target/release/ay"
export PATH="/opt/homebrew/bin:$PATH"

command -v minizinc >/dev/null || { echo "installing minizinc..."; brew install minizinc; }
command -v gtimeout >/dev/null || { echo "installing coreutils (gtimeout)..."; brew install coreutils; }
command -v cargo >/dev/null || { echo "ERROR: cargo is required"; exit 1; }

# `ay corpus` performs pinned size/SHA verification and transactional install.
(cd "$REPO" && cargo build --release -p ay --features cli --bin ay)
(cd "$REPO" && "$AY_BIN" corpus download \
  minizinc-challenge-2025 minizinc-challenge-2025-results)
(cd "$REPO" && "$AY_BIN" corpus verify \
  minizinc-challenge-2025 minizinc-challenge-2025-results)

# Register AY solver: MZN_SOLVER_PATH must include the repo (holds ay.msc), and
# the fzn-exec wrapper resolves ./ay next to itself.
ln -sf "$AY_BIN" "$REPO/competition/minizinc/ay"
export MZN_SOLVER_PATH="$REPO"
minizinc --solvers | grep -q org.ay.ay && echo "AY registered OK" || {
  echo "ERROR: AY solver not registered (need MZN_SOLVER_PATH=$REPO)"; exit 1; }

echo "OK: $(find "$DATA" -mindepth 1 -maxdepth 1 -type d | wc -l | tr -d ' ') problems, results $(wc -c <"$RESULTS") bytes."
echo "Run:   python3 scripts/mzn_challenge/run.py 1200000 free 6"
echo "Score: python3 scripts/mzn_challenge/score_ay.py <run.json> free"
