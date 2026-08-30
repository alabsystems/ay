#!/bin/bash
# ay-script: pb-cert-reserve-sweep
#
# THE POLICY SWEEP. Reserving budget for the certificate stage takes it from the
# search, so "how much to reserve" is a trade, not a free win, and the trade has
# to be MEASURED rather than guessed. This sweeps the native proof-logging
# slice on the competition binary through its existing `--cert-native-cap-ms`
# flag -- no rebuild per point, no new flag -- and records, for each setting,
# what the PINNED checker accepts.
#
# READ THE COLUMNS THIS WAY. In proof mode AY is fail-closed: `s OPTIMUM FOUND`
# is printed only when a certificate was assembled and committed. So in the
# proof arm "solved optima" and "certificates" are the SAME number, and the cost
# of an over-large reserve shows up as instances that certify at one setting and
# not at another -- which is why the sweep records the per-instance set, not
# just the count.
#
# All points for one instance run BACK TO BACK, so they see the same machine.
#
# Usage: pb_cert_reserve_sweep.sh <ay-pb-bin> <veripb> <budget_ms> <caps-csv> <instance>
# Emits one TSV row per cap:
#   path  cap_ms  budget_ms  status  objective  wall_ms  proof_bytes  route  verdict  score
set -u

BIN=$1; VERIPB=$2; TMO=$3; CAPS=$4; F=$5

. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib/veripb_verdict.sh"

work=$(mktemp -d "${TMPDIR:-/tmp}/ay-reserve-sweep.XXXXXX")
trap 'rm -rf "$work"' EXIT

now_ms() { python3 -c 'import time;print(int(time.time()*1000))'; }

IFS=',' read -ra CAPLIST <<< "$CAPS"
for cap in "${CAPLIST[@]}"; do
    pf="$work/proof.pbp"; sf="$work/stdout"
    rm -f "$pf" "$sf"
    t0=$(now_ms)
    if [ "$cap" = "default" ]; then
        "$BIN" pb solve --timeout "$TMO" --proof "$pf" "$F" >"$sf" 2>"$work/err"
    else
        "$BIN" pb solve --timeout "$TMO" --cert-native-cap-ms "$cap" --proof "$pf" "$F" \
            >"$sf" 2>"$work/err"
    fi
    ex=$?
    t1=$(now_ms)
    wall=$((t1 - t0))

    st=$(grep '^s ' "$sf" | tail -1 | sed 's/^s //')
    obj=$(grep '^o ' "$sf" | tail -1 | sed 's/^o //')
    [ -n "$st" ] || st="<no-s-line:exit=$ex>"

    bytes=0; route="-"; verdict="-"; score="-"
    case "$st" in
        UNSATISFIABLE|SATISFIABLE|"OPTIMUM FOUND")
            if [ -s "$pf" ]; then
                bytes=$(wc -c <"$pf" | tr -d ' ')
                route=$(awk '{print $1}' "$pf" | sort | uniq -c | sort -rn \
                    | awk '{printf "%s:%s,", $2, $1}' | sed 's/,$//' | cut -c1-120)
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
        "$F" "$cap" "$TMO" "$st" "${obj:--}" "$wall" "$bytes" "$route" "$verdict" "$score"
    rm -f "$pf" "$sf"
done
