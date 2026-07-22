#!/usr/bin/env bash
# ay-script: sat-soundness-gate
# SAT soundness gate (SAT-COMP campaign).
#
# Runs the `ay` binary on LABELED vendored CNFs and fails the build on:
#   - any WRONG verdict (SAT for a known-UNSAT instance, or vice versa), and
#   - any UNSAT whose emitted proof FAILS internal verification (a rejected
#     certificate — the SAT-COMP "no points / DQ" failure mode).
# A sound `s UNKNOWN` / timeout is tolerated (never a wrong answer) but reported,
# so solved-count regressions are visible. This is the "zero wrong answers"
# gate the audit found missing — what would have caught inc1/6/7 never landing,
# and what guards a future soundness regression on the core CDCL path.
#
# Verdict + proof are checked in ONE run via --verify-proof, which exits:
#   10 = SAT,  20 = UNSAT (+ proof internally verified),  1 = proof REJECTED,
#   other = UNKNOWN/timeout.
#
# Usage: scripts/ci/sat_soundness_gate.sh [ay-binary] [proof-format] [timeout-s]
set -u

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

BIN="${1:-}"
if [ -z "$BIN" ]; then
    if [ -x target/release/ay ]; then BIN=target/release/ay
    elif [ -x target/debug/ay ]; then BIN=target/debug/ay
    else echo "FATAL: no ay binary found (build with: cargo build -p ay --features cli)"; exit 2; fi
fi
FMT="${2:-drat}"     # drat (SAT-COMP Main canonical) or lrat
TIMEOUT="${3:-60}"

# Labeled instances: "<expected> <path>"; everything under sat/unsat/ is UNSAT.
declare -a CASES=(
    "SAT   benchmarks/sat/canary/tiny_sat.cnf"
    "UNSAT benchmarks/sat/canary/tiny_unsat.cnf"
)
while IFS= read -r f; do
    CASES+=("UNSAT $f")
done < <(find benchmarks/sat/unsat -name '*.cnf' 2>/dev/null | sort)

TO=""
if command -v timeout >/dev/null 2>&1; then TO="timeout ${TIMEOUT}s"
elif command -v gtimeout >/dev/null 2>&1; then TO="gtimeout ${TIMEOUT}s"; fi

PROOF_DIR="$(mktemp -d)"
trap 'rm -rf "$PROOF_DIR"' EXIT

wrong=0; rejected=0; solved=0; unknown=0; total=0
echo "SAT soundness gate: binary=$BIN format=$FMT timeout=${TIMEOUT}s"
echo "------------------------------------------------------------"
for case in "${CASES[@]}"; do
    expected="${case%% *}"; path="${case##* }"
    [ -f "$path" ] || { echo "SKIP  (missing) $path"; continue; }
    total=$((total + 1))
    proof="$PROOF_DIR/$(basename "$path").$FMT"
    $TO "$BIN" "$path" --proof "$proof" --proof-format "$FMT" --verify-proof >/dev/null 2>&1
    rc=$?
    case "$rc" in
        10) verdict=SAT ;;
        20) verdict=UNSAT ;;       # UNSAT + proof verified
        1)  verdict=PROOF_REJECTED ;;
        *)  verdict=UNKNOWN ;;
    esac
    rm -f "$proof"
    if [ "$verdict" = "PROOF_REJECTED" ]; then
        echo "REJECT proof failed verification  $path"; rejected=$((rejected + 1))
    elif [ "$verdict" = "UNKNOWN" ]; then
        echo "warn  UNKNOWN/timeout   ($expected) $path"; unknown=$((unknown + 1))
    elif [ "$verdict" = "$expected" ]; then
        echo "ok    $verdict (proof ok if UNSAT)  $path"; solved=$((solved + 1))
    else
        echo "WRONG got=$verdict expected=$expected  $path"; wrong=$((wrong + 1))
    fi
done
echo "------------------------------------------------------------"
echo "total=$total solved=$solved unknown=$unknown WRONG=$wrong PROOF_REJECTED=$rejected"
if [ "$wrong" -gt 0 ] || [ "$rejected" -gt 0 ]; then
    echo "FAIL: $wrong wrong verdict(s) + $rejected rejected proof(s) — soundness regression, blocking."
    exit 1
fi
echo "PASS: zero wrong answers, all UNSAT proofs verified."
exit 0
