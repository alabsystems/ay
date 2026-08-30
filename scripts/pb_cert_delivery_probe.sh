#!/bin/bash
# ay-script: pb-cert-delivery-probe
#
# THE DELIVERY/SEARCH-PROOF DISCRIMINATOR. For one instance that AY solves to
# OPTIMUM but does not certify, decide WHICH of the two things is true:
#
#   the derivation EXISTS and production merely failed to produce it in budget
#       -> DELIVERY. Fixable by scheduling, and this is the cheap half of the
#          roadmap.
#   the derivation is NOT produced even with a budget of its own
#       -> SEARCH-PROOF GAP / EXPRESSION. Needs new emitter work.
#
# HOW. Two steps, and the second is the one production cannot do:
#
#   1. `ay pb solve` WITHOUT --proof, to get AY's optimum and a full `v` model.
#      (In proof mode AY is fail-closed and prints neither.)
#   2. `certrefute` — the OPT-LIN refutation routes with a FRESH deadline of
#      their own — then the PINNED checker on whatever it emits.
#
# Step 2 is not reachable from the CLI. In `solve_optimization_with_proof` the
# native proof-logging CDCL gets the caller's WHOLE `timeout_dur` and the
# certificate fallback then runs against the SAME `start`/`timeout_dur`, so its
# `should_stop()` is already true and every `*_interruptible` helper returns
# `None` on its first check. The fallback's budget is `B - B = 0` for every `B`,
# which is why raising `--timeout` is not a test of this question and a probe
# with a separate deadline is.
#
# A VERIFIED here is a REAL certificate for the instance — the checker is the
# pinned one and the conclusion is compared to AY's own claimed optimum — it is
# simply one production did not manage to emit.
#
# Usage: pb_cert_delivery_probe.sh <ay-bin> <certrefute-bin> <veripb> <solve_ms> <cert_ms> <instance> [route]
# where [route] is all|compact|auxfree|pbnative (default all). Naming a single
# route gives it the whole budget; `all` reproduces production's SHARED deadline,
# under which the first route can starve the rest.
# Emits one TSV row:
#   path  optimum  solve_status  cert_route  proof_bytes  route_timings  checker_verdict  score
set -u

BIN=$1; REFUTE=$2; VERIPB=$3; SOLVE_MS=$4; CERT_MS=$5; F=$6; ROUTE_SEL=${7:-all}

. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib/veripb_verdict.sh"

work=$(mktemp -d "${TMPDIR:-/tmp}/ay-delivery-probe.XXXXXX")
trap 'rm -rf "$work"' EXIT

"$BIN" pb solve --timeout "$SOLVE_MS" "$F" >"$work/sol" 2>/dev/null
st=$(grep '^s ' "$work/sol" | tail -1 | sed 's/^s //')
obj=$(grep '^o ' "$work/sol" | tail -1 | sed 's/^o //')

if [ "$st" != "OPTIMUM FOUND" ] || [ -z "$obj" ]; then
    # No optimum, nothing to certify. Recorded, never guessed at.
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$F" "${obj:--}" "${st:-<no-s-line>}" "-" 0 "-" "-" "NO-OPTIMUM"
    exit 0
fi

# The `v` lines carry the model; certrefute re-verifies it is feasible and
# achieves `obj` before it will emit anything.
vline=$(grep '^v ' "$work/sol" | sed 's/^v //' | tr '\n' ' ')

pf="$work/probe.pbp"
out=$("$REFUTE" "$F" "$obj" "$vline" "$pf" "$CERT_MS" "$ROUTE_SEL" 2>"$work/err")
route=$(printf '%s' "$out" | cut -f5)
bytes=$(printf '%s' "$out" | cut -f6)
timings=$(printf '%s' "$out" | cut -f7)
[ -n "$route" ] || route="<certrefute-failed>"

verdict="-"; score="NO-PROOF"
if [ -s "$pf" ]; then
    want=$(veripb_bounds_conclusion "$obj")
    veripb_run "$VERIPB" --opb "$F" "$pf"
    verdict=${VERIPB_VERDICT:-<no-verdict-line>}
    if veripb_accepted && [ "$VERIPB_VERDICT" = "s VERIFIED $want" ]; then
        score="VERIFIED"
    elif veripb_accepted; then
        score="WRONG-CONCLUSION"
    else
        score="REJECT"
    fi
fi

printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$F" "$obj" "$st" "$route" "${bytes:-0}" "${timings:--}" "$verdict" "$score"
