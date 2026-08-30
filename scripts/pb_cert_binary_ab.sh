#!/bin/bash
# ay-script: pb-cert-binary-ab
#
# WHICH BINARY IS "AY"? An A/B of the two programs that both answer PB, run back
# to back on the same instance so they see the same machine.
#
#   A = `ay pb solve`   the shipped CLI            (crates/ay, src/cmd_pb.rs)
#   B = `ay-pb`         the competition binary     (crates/ay-pb, src/bin/ay.rs)
#
# WHY THIS IS A CENSUS QUESTION AND NOT A CURIOSITY. The four OPT-LIN FLOOR
# emitters -- `certify_opt_lin_trivial_zero_floor`,
# `certify_opt_lin_knapsack_cardinality`,
# `certify_opt_lin_direct_aggregation_floor` and
# `certify_opt_lin_lp_dual_floor` -- are named in exactly one production file,
# `crates/ay-pb/src/bin/ay.rs`. The shipped `ay` CLI's PB path never names them,
# and `certify_opt_lin_bounds_compact` does not delegate to them either, so the
# CLI's only optimality-certificate routes are the native proof-logging CDCL
# stream and the compact/aux-free refutation fallback.
#
# That matters because the LP-dual-floor ceiling this programme has been quoting
# -- 66/163 reachable, and the 46.6% that was built on top of it -- is a ceiling
# for `lp_dual_floor`, a route only ONE of these two binaries can run. A coverage
# figure that does not say which binary produced it is not a figure.
#
# Both arms are scored by the same pinned checker through the same shared
# verdict library, and each arm's proof is compared against the conclusion ITS
# OWN answer entails -- so an arm that reports a different optimum is checked
# against that optimum, not against the other arm's.
#
# Usage: pb_cert_binary_ab.sh <ay-cli> <ay-pb> <veripb> <budget_ms> <instance>
# Emits two TSV rows:
#   path  arm  budget_ms  status  objective  wall_ms  proof_bytes  route  verdict  score
set -u

CLI=$1; PBBIN=$2; VERIPB=$3; TMO=$4; F=$5

. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib/veripb_verdict.sh"

work=$(mktemp -d "${TMPDIR:-/tmp}/ay-pb-ab.XXXXXX")
trap 'rm -rf "$work"' EXIT

now_ms() { python3 -c 'import time;print(int(time.time()*1000))'; }

run_arm() {
    arm=$1; bin=$2; shift 2
    pf="$work/proof.pbp"; sf="$work/stdout"
    rm -f "$pf" "$sf"
    t0=$(now_ms)
    "$bin" "$@" --timeout "$TMO" --proof "$pf" "$F" >"$sf" 2>"$work/err"
    ex=$?
    t1=$(now_ms)
    st=$(grep '^s ' "$sf" | tail -1 | sed 's/^s //')
    obj=$(grep '^o ' "$sf" | tail -1 | sed 's/^o //')
    [ -n "$st" ] || st="<no-s-line:exit=$ex>"

    bytes=0; route="-"; verdict="-"; score="-"
    case "$st" in
        UNSATISFIABLE|SATISFIABLE|"OPTIMUM FOUND")
            if [ -s "$pf" ]; then
                bytes=$(wc -c <"$pf" | tr -d ' ')
                route=$(awk '{print $1}' "$pf" | sort | uniq -c | sort -rn \
                    | awk '{printf "%s:%s,", $2, $1}' | sed 's/,$//' | cut -c1-160)
                if want=$(veripb_entailed_conclusion "s $st" "$F" "$obj" 2>/dev/null); then
                    veripb_run "$VERIPB" --opb "$F" "$pf"
                    verdict=${VERIPB_VERDICT:-<no-verdict-line>}
                    if veripb_accepted && [ "$VERIPB_VERDICT" = "s VERIFIED $want" ]; then
                        score="VERIFIED"
                    elif veripb_accepted; then
                        score="WRONG-CONCLUSION"
                    else
                        score="REJECT"
                    fi
                else
                    score="REJECT"
                fi
            else
                score="NO-PROOF-EMITTED"
            fi
            ;;
    esac
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$F" "$arm" "$TMO" "$st" "${obj:--}" "$((t1 - t0))" \
        "$bytes" "$route" "$verdict" "$score"
    rm -f "$pf" "$sf"
}

run_arm cli   "$CLI" pb solve
run_arm ay-pb "$PBBIN" pb solve
