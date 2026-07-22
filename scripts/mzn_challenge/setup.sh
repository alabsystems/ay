#!/usr/bin/env bash
# ay-script: mzn-setup
# Reconstitute the MiniZinc Challenge 2025 harness on a fresh machine:
#   1. verify minizinc + gtimeout (brew installs the MiniZinc toolchain)
#   2. register AY as a MiniZinc solver (org.ay.ay)
#   3. fetch the 2025 corpus (models+data) and the official results.json
# The corpus lands in benchmarks/minizinc/challenge-2025/ (gitignored, ~large).
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
DATA="$REPO/benchmarks/minizinc/challenge-2025"
export PATH="/opt/homebrew/bin:$PATH"

command -v minizinc >/dev/null || { echo "installing minizinc..."; brew install minizinc; }
command -v gtimeout >/dev/null || { echo "installing coreutils (gtimeout)..."; brew install coreutils; }

# Register AY solver: MZN_SOLVER_PATH must include the repo (holds ay.msc), and
# the fzn-exec wrapper resolves ./ay next to itself.
ln -sf "$REPO/target/release/ay" "$REPO/competition/minizinc/ay"
export MZN_SOLVER_PATH="$REPO"
minizinc --solvers | grep -q org.ay.ay && echo "AY registered OK" || {
  echo "ERROR: AY solver not registered (need MZN_SOLVER_PATH=$REPO)"; exit 1; }

mkdir -p "$DATA/data"
if [ ! -d "$DATA/data/atsp" ]; then
  echo "fetching mzn-challenge 2025 corpus..."
  tmp="$(mktemp -d)"; git clone --depth 1 https://github.com/MiniZinc/mzn-challenge.git "$tmp/mc"
  cp -R "$tmp/mc/2025/." "$DATA/data/"; rm -rf "$tmp"
fi
if [ ! -s "$DATA/results-2025.json" ]; then
  echo "fetching official results.json..."
  curl -fsSL "https://raw.githubusercontent.com/MiniZinc/minizinc.github.io/main/public/challenge/2025/results.json" \
    -o "$DATA/results-2025.json"
fi
echo "OK: $(ls "$DATA/data" | wc -l | tr -d ' ') problems, results $(wc -c <"$DATA/results-2025.json") bytes."
echo "Run:   python3 scripts/mzn_challenge/run.py 1200000 free 6"
echo "Score: python3 scripts/mzn_challenge/score_ay.py <run.json> free"
