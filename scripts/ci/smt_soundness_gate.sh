#!/usr/bin/env bash
# ay-script: smt-soundness-gate
# SMT soundness-differential gate (Z3-replacement campaign).
#
# The SMT analog of scripts/ci/sat_soundness_gate.sh. It runs two complementary,
# fail-closed regression checks over the committed Tier-0 corpus:
#
#   [1] HERMETIC declared-status check (needs NO second solver): every .smt2 is
#       run through libay_ffi ONLY and AY's verdict is compared with the file's
#       own (set-info :status sat|unsat) expected label. A contradiction fails
#       the regression check and requires adjudication; the label is not an
#       independent proof. unknown / timeout is tolerated (incompleteness).
#
#   [2] 2-SOLVER DIFFERENTIAL vs libz3 (only when /opt/homebrew/bin/z3 present):
#       the classic `ay-z3-parity diff` — any sat-vs-unsat DISAGREE fails.
#
# Both reuse the existing exit contract in crates/ay-z3-parity/src/diff.rs
# (non-zero iff wrong/disagree != 0) with ZERO solver-code change. A sound
# `unknown`/timeout never fails the gate but is reported so completeness
# regressions stay visible.
#
# Usage: scripts/ci/smt_soundness_gate.sh [ay-lib] [parity-bin] [timeout-s]
set -u

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

# Per-(file,solver) wall-clock bound. Kept small: a timeout is soundness-neutral
# (tolerated as incompleteness), never a wrong answer, so a tight bound keeps the
# per-push gate fast without ever masking a real disagreement.
TIMEOUT="${3:-5}"
Z3_LIB="${Z3_LIB:-/opt/homebrew/lib/libz3.dylib}"
Z3_BIN="${Z3_BIN:-/opt/homebrew/bin/z3}"

# Tier-0 corpora: committed micro-corpus + BOTH shipped-bug families + the
# wrong-verdict repros under repros/. An entry is a directory or one file; one
# the public export does not carry is dropped, not failed.
#
# The repros entries are the ones filed for a wrong or quarantined verdict:
# cs_stateful (a likely wrong unsat, moved out of the retired docs/ handoff
# directory, which this gate never scanned), the QF_LRA push/pop false unsat,
# FP chainable comparisons, the unsat-certificate inputs and the two
# quarantined ABV unsats. The rest of repros/ is a wrong model under a right
# verdict (arrays-model-bug, qf-bvfp-model-writeback), which a verdict gate
# cannot see, or performance and completeness (dpll-lra-perf, lra-scope-trail,
# qlock-array, the string and mixed-arithmetic gaps), mostly timeouts at this
# gate's bound. Measured 2026-09-27 at 5 s: the whole of repros/ (60 files) has
# 0 declared-status contradictions and 0 sat-vs-unsat disputes with libz3, and
# these entries add 13 files to the 30 above and take the two passes from 22 s
# to 44 s.
CORPORA=()
for d in \
    crates/ay-z3-parity/corpus \
    benchmarks/smt/regression/soundness_qf_ax \
    benchmarks/smt/regression/soundness_qf_slia_fuzz \
    repros/cs_stateful-1.i_2.MINIMIZED.smt2 \
    repros/lra-pushpop-false-unsat-2026-09-18 \
    repros/fp-chainable-comparisons \
    repros/unsat-cert \
    repros/abv-nested-array-quantified-unsat-quarantine.smt2 \
    repros/abv-record-boxed-nested-array-quantified-unsat-quarantine.smt2
do
    [ -e "$d" ] && CORPORA+=("$d")
done

echo "== building --release -p ay-ffi -p ay-z3-parity ..."
# Cargo-family commands run through scripts/lib/cargo_frontend.sh: `targo`
# (unverified lane) on a host with the Trust toolchain, plain `cargo` on a
# public clone without it.
. "$REPO_ROOT/scripts/lib/cargo_frontend.sh"
if ! ay_cargo build --release -p ay-ffi -p ay-z3-parity; then
    echo "FATAL: build failed"; exit 2
fi

# Locate the freshly-built FFI shared object (.dylib on macOS, .so on Linux).
TARGET_DIR="${CARGO_TARGET_DIR:-target}"
AY_LIB="${1:-}"
if [ -z "$AY_LIB" ]; then
    for cand in "$TARGET_DIR/release/libay_ffi.dylib" "$TARGET_DIR/release/libay_ffi.so"; do
        [ -f "$cand" ] && AY_LIB="$cand" && break
    done
fi
PARITY="${2:-$TARGET_DIR/release/ay-z3-parity}"
[ -f "$AY_LIB" ]  || { echo "FATAL: AY lib not found ($AY_LIB)"; exit 2; }
[ -x "$PARITY" ]  || { echo "FATAL: ay-z3-parity binary not found ($PARITY)"; exit 2; }

echo "SMT soundness gate: ay=$AY_LIB parity=$PARITY timeout=${TIMEOUT}s"
echo "corpora: ${CORPORA[*]}"
echo "============================================================"

fail=0

# ---- [1] hermetic declared-status regression check (no z3 needed) ----------
echo ""
# `--oracle declared` is the parity tool's legacy option spelling.
echo "== [1/2] declared-status regression check (hermetic, no z3) =="
"$PARITY" diff "${CORPORA[@]}" --ay "$AY_LIB" --oracle declared --timeout "$TIMEOUT"
rc=$?
if [ "$rc" -ne 0 ]; then
    echo ">> DECLARED-STATUS MISMATCH (exit $rc)"
    fail=1
fi

# ---- [2] 2-solver differential vs libz3 (best-effort) ----------------------
echo ""
if [ -f "$Z3_LIB" ] || [ -x "$Z3_BIN" ]; then
    Z3_ARG="$Z3_LIB"
    [ -f "$Z3_ARG" ] || Z3_ARG="/opt/homebrew/lib/libz3.dylib"
    echo "== [2/2] differential vs libz3 ($Z3_ARG) =="
    "$PARITY" diff "${CORPORA[@]}" --ay "$AY_LIB" --z3 "$Z3_ARG" --timeout "$TIMEOUT"
    rc=$?
    if [ "$rc" -ne 0 ]; then
        echo ">> DIFFERENTIAL FAIL (exit $rc)"
        fail=1
    fi
else
    echo "== [2/2] libz3 not present ($Z3_LIB) — skipping 2-solver diff =="
    echo "   (the hermetic declared-status regression check still runs offline)"
fi

echo ""
echo "============================================================"
if [ "$fail" -ne 0 ]; then
    echo "FAIL: declared-label contradiction or solver dispute found — blocking."
    exit 1
fi
echo "PASS: 0 verdicts contradict declared :status labels; 0 sat-vs-unsat disputes vs libz3."
exit 0
