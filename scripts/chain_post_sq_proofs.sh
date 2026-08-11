#!/bin/bash
# Verify the Alethe declaration-collector fix, the moment the SQ race frees the host.
#
# WHY QUEUED RATHER THAN RUN NOW: the clean SQ race is the measurement that settles
# the campaign's only defensibility-standard claim. Building and testing beside it
# depresses the competitor's wall-clock solve count (documented 15-47% swing on this
# host) and taints the margin that gets quoted. So this waits.
#
# WHAT IT CHECKS. `collect_auxiliary_proof_declarations` filtered its output through
# a six-prefix allowlist, so every internal symbol family outside it was dropped from
# the Alethe preamble and carcara died in the PARSER:
#     parser error: identifier 's_tmp___!left' is not defined (on line 4, column 25)
# The fix keeps only the real obligation: free in the proof, absent from the problem
# scope => must be declared.
#
# The bar this run must clear, in order:
#   1. ay-proof tests pass (including the new regression test).
#   2. The blocksworld proof PARSES — carcara's first error is no longer a parser
#      error. It may still be `invalid` on a rule; that is expected and is a
#      strictly better diagnostic position, not a failure of this fix.
#   3. check_proofs.sh does not regress: no proof that was `valid` becomes anything
#      else.
set -u
cd "$(dirname "$0")/.."
SP="${SP:-$(mktemp -d /tmp/ay-post-sq-proofs.XXXXXX)}"
CHAIN_PID="${1:-23514}"
BW=benchmarks/smtlib-2025/non-incremental/QF_DT/20230720-blocksworld/blocksworld_from_0_0_8_to_1_3_4_negated_goal_bmc_2.smt2

echo "[$(date)] waiting for the SQ race (pid $CHAIN_PID) to finish"
while kill -0 "$CHAIN_PID" 2>/dev/null; do sleep 120; done
echo "[$(date)] SQ race done — host is free"

# ---------------------------------------------------------------------------
# 1. Build and test.
#
# `--features cli` is REQUIRED: `cargo build -p ay` silently builds only the lib
# (the [[bin]] has required-features = ["cli"]) and leaves a STALE target/release/ay
# behind, which has already caused three measurements to be read as "this code path
# never executes".
echo "[$(date)] === 1. build + ay-proof tests ==="
cargo build --release -p ay --features cli 2>&1 | tail -5 || exit 1
cargo test -p ay-proof 2>&1 | tail -25
PROOF_TESTS=$?
echo "[$(date)] ay-proof test exit: $PROOF_TESTS"

# ---------------------------------------------------------------------------
# 2. The specific defect: does the blocksworld proof parse now?
echo "[$(date)] === 2. blocksworld proof under carcara ==="
CAR="$HOME/.cargo/bin/carcara"; [ -x "$CAR" ] || CAR=$(command -v carcara 2>/dev/null)
if [ -z "$CAR" ] || [ ! -x "$CAR" ]; then
    echo "  carcara not found — cannot verify the fix's actual effect"
else
    ./target/release/ay --z3-mode -T:60 --proof "$SP/bw_after.alethe" "$BW" 2>&1 | head -2
    echo "  preamble lines: $(grep -c '^(declare-fun' "$SP/bw_after.alethe" 2>/dev/null || echo 0)"
    echo "  field-split symbols declared: $(grep -c '^(declare-fun.*!' "$SP/bw_after.alethe" 2>/dev/null || echo 0)"
    OUT=$("$CAR" check --allow-int-real-subtyping "$SP/bw_after.alethe" "$BW" 2>&1)
    echo "$OUT" | head -8
    if echo "$OUT" | grep -q "parser error"; then
        echo "  VERDICT: STILL A PARSER ERROR — the collector fix did NOT close it."
    else
        echo "  VERDICT: parses. The parser error is closed; any remaining failure is a RULE."
    fi
fi

# ---------------------------------------------------------------------------
# 3. Whole-corpus regression: nothing that was `valid` may stop being valid.
echo "[$(date)] === 3. check_proofs.sh regression sweep ==="
if [ -x scripts/check_proofs.sh ]; then
    ./scripts/check_proofs.sh 2>&1 | tail -30
else
    echo "  scripts/check_proofs.sh missing or not executable"
fi
echo "[$(date)] POST-SQ PROOF VERIFICATION COMPLETE"
