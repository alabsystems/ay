#!/usr/bin/env bash
# ay-script: smtcomp-fixtures
# link_smtcomp_fixtures.sh — populate benchmarks/smtcomp/<LOGIC>/ from the
# already-downloaded SMT-LIB 2025 tree at benchmarks/smtlib-2025/.
#
# WHY THIS EXISTS
#
# ~38 regression tests reference fixtures under `benchmarks/smtcomp/...`, the
# flat layout produced by `download_smtcomp_benchmarks.sh`. On a checkout where
# that script has not been run, 36 of 38 are absent — and 10 of the call sites
# `panic!("benchmark not found")` rather than skipping, so the tests FAIL rather
# than being skipped. The affected tests are disproportionately release-only
# false-UNSAT guards (#6564, #6582, alia array-model soundness, auflia storeinv,
# lia jpg2gif): exactly the checks the release suite exists to run.
# See the development design notes
#
# Most of those files are ALREADY on disk under benchmarks/smtlib-2025/, just at
# their real SMT-LIB paths rather than the flat one. This links them into place
# — no download, no duplication (hard links where possible).
#
# Usage:  bash scripts/link_smtcomp_fixtures.sh [--dry-run]
#
# Idempotent. Reports anything it could not resolve; those genuinely need
# `scripts/download_smtcomp_benchmarks.sh <LOGIC>` (as of 2026-07-25: one QF_ABV,
# one QF_BV, two QF_LIA files).
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC="$REPO/benchmarks/smtlib-2025"
DRY=""
[ "${1:-}" = "--dry-run" ] && DRY=1

if [ ! -d "$SRC" ]; then
  echo "error: $SRC not present — fetch the SMT-LIB 2025 corpora first" >&2
  exit 1
fi

REFS=()
while IFS= read -r line; do REFS+=("$line"); done < <(grep -rho 'benchmarks/smtcomp/[A-Za-z_0-9/.-]*\.smt2' "$REPO/crates" 2>/dev/null | sort -u)
linked=0; already=0; unresolved=0
for ref in "${REFS[@]}"; do
  dest="$REPO/$ref"
  if [ -f "$dest" ]; then already=$((already+1)); continue; fi
  base="$(basename "$ref")"
  src="$(find "$SRC" -name "$base" -print -quit 2>/dev/null || true)"
  if [ -z "$src" ]; then
    echo "  UNRESOLVED (needs download): $ref"
    unresolved=$((unresolved+1)); continue
  fi
  if [ -n "$DRY" ]; then
    echo "  would link: $ref  <-  ${src#"$REPO/"}"
  else
    mkdir -p "$(dirname "$dest")"
    ln "$src" "$dest" 2>/dev/null || cp "$src" "$dest"
  fi
  linked=$((linked+1))
done

echo "fixtures: ${already} already present, ${linked} linked, ${unresolved} unresolved"
[ "$unresolved" -gt 0 ] && echo "note: unresolved files need scripts/download_smtcomp_benchmarks.sh for their logic"
exit 0
