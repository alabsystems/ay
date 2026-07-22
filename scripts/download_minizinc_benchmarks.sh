#!/usr/bin/env bash
# ay-script: mzn-fetch
# download_minizinc_benchmarks.sh — fetch + compile the MiniZinc Challenge 2024
# FlatZinc instances the ay-flatzinc tests resolve.
#
# Source: the MiniZinc Challenge 2024 models/data (github.com/MiniZinc/mzn-challenge,
# 2024/<problem>/). Each instance is flattened to FlatZinc with the bundled
# generic target (org.minizinc.mzn-fzn) and written to
# benchmarks/minizinc/compiled-fzn/2024/<problem>/<instance>.fzn — the path the
# tests resolve.
#
# Requires the `minizinc` CLI on PATH (e.g. `brew install minizinc`).
#
# Usage: scripts/download_minizinc_benchmarks.sh
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RAW="https://raw.githubusercontent.com/MiniZinc/mzn-challenge/master/2024"
DEST="$ROOT/benchmarks/minizinc/compiled-fzn/2024"

command -v curl     >/dev/null 2>&1 || { echo "error: curl not found" >&2; exit 1; }
command -v minizinc >/dev/null 2>&1 || { echo "error: minizinc not found (brew install minizinc)" >&2; exit 1; }

# problem-dir : model.mzn : data.dzn : output-name.fzn
instances=(
  "triangular:triangular.mzn:n9.dzn:n9.fzn"
  "neighbours:neighbours-rect.mzn:neightbours-new-2.dzn:neightbours-new-2.fzn"
  "monitor-placement-1id:monitor_1id.mzn:hop_counting_based_zoo_Forthnet.dzn:hop_counting_based_zoo_Forthnet.fzn"
)

TMP="$(mktemp -d "${TMPDIR:-/tmp}/mzn.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

for entry in "${instances[@]}"; do
  IFS=: read -r problem model data out <<<"$entry"
  mkdir -p "$DEST/$problem"
  outpath="$DEST/$problem/$out"
  if [ -s "$outpath" ]; then
    echo "minizinc[$problem/$out]: already present; skipping."
    continue
  fi
  echo "minizinc[$problem/$out]: fetching + compiling ..."
  curl -fsSL --max-time 120 "$RAW/$problem/$model" -o "$TMP/$model"
  curl -fsSL --max-time 120 "$RAW/$problem/$data"  -o "$TMP/$data"
  minizinc -c --solver org.minizinc.mzn-fzn "$TMP/$model" "$TMP/$data" --fzn "$outpath"
  echo "minizinc[$problem/$out]: wrote $(wc -l < "$outpath" | tr -d ' ') lines."
done
