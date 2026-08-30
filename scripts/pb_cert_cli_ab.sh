#!/bin/bash
# ay-script: pb-cert-cli-ab
#
# ONE INSTANCE, EVERY ARM, BACK TO BACK — the N-binary generalisation of
# `pb_cert_census.sh`, for the question "did wiring the OPT-LIN certificate
# chain into the shipped CLI close the gap to the competition binary?".
#
# That question needs THREE programs in the same measurement, not two:
#
#   cli0   the shipped CLI BEFORE the change   (2-route chain)
#   cli1   the shipped CLI AFTER the change    (8-route chain)
#   pb1    the competition binary              (the target to match)
#
# and `pb_cert_census.sh` hard-codes exactly two binary keys, so this worker
# takes a `key=path` map instead. Everything else is deliberately identical to
# that script — same arm-per-instance interleave (A,B,A,B: every arm sees the
# same machine within seconds, so the ratio survives a loaded box), same TSV
# columns, same scoring, and the same audited verdict library. The verdict logic
# is NOT re-implemented here: every hand-rolled `grep VERIFIED` in this repo's
# history has been unsound in at least one of four ways.
#
# Emits ONE tab-separated row PER ARM on stdout:
#
#   path  arm  budget_ms  status  objective  wall_ms  proof_bytes  proof_lines
#   proof_sha256  route  checker_exit  checker_verdict  want_verdict  score
#
# score is VERIFIED / REJECT / WRONG-CONCLUSION / NO-PROOF-EMITTED / OVERSIZE / -,
# with exactly the meanings `pb_cert_census.sh` documents.
#
# Usage:
#   pb_cert_cli_ab.sh <bin-map> <veripb-bin> <arm-spec> <instance>
#     bin-map    key=path[,key=path...]        e.g. cli0=./bin/ay0,pb1=./bin/ay-pb
#     arm-spec   key:mode:budget_ms[,...]      run in the order given
set -u

BINMAP=$1; VERIPB=$2; ARMS=$3; F=$4

: "${CENSUS_MAX_PROOF_BYTES:=1073741824}"

. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib/veripb_verdict.sh"

work=$(mktemp -d "${TMPDIR:-/tmp}/ay-pb-cliab.XXXXXX")
trap 'rm -rf "$work"' EXIT

now_ms() { python3 -c 'import time;print(int(time.time()*1000))'; }

resolve_bin() {
    _key=$1
    IFS=',' read -ra _pairs <<< "$BINMAP"
    for _p in "${_pairs[@]}"; do
        if [ "${_p%%=*}" = "$_key" ]; then printf '%s' "${_p#*=}"; return 0; fi
    done
    return 1
}

run_arm() {
    WHICH=$1; MODE=$2; TMO=$3
    if ! BIN=$(resolve_bin "$WHICH"); then
        echo "unknown binary key '$WHICH' (map: $BINMAP)" >&2
        return 1
    fi
    pf="$work/proof.pbp"
    sf="$work/stdout"
    rm -f "$pf" "$sf"

    t0=$(now_ms)
    if [ "$MODE" = proof ]; then
        "$BIN" pb solve --timeout "$TMO" --proof "$pf" "$F" >"$sf" 2>"$work/stderr"
    else
        "$BIN" pb solve --timeout "$TMO" "$F" >"$sf" 2>"$work/stderr"
    fi
    ay_exit=$?
    t1=$(now_ms)
    wall=$((t1 - t0))

    st=$(grep '^s ' "$sf" | tail -1 | sed 's/^s //')
    obj=$(grep '^o ' "$sf" | tail -1 | sed 's/^o //')
    # A run that printed no status line MEASURED NOTHING; record it as such with
    # the exit code inline, never silently folded into UNKNOWN.
    [ -n "$st" ] || st="<no-s-line:ay_exit=$ay_exit>"

    pbytes=0; plines=0; psha="-"; route="-"
    cexit="-"; cverdict="-"; want="-"; score="-"

    if [ "$MODE" = proof ]; then
        case "$st" in
            UNSATISFIABLE|SATISFIABLE|"OPTIMUM FOUND")
                if [ -s "$pf" ]; then
                    pbytes=$(wc -c <"$pf" | tr -d ' ')
                    plines=$(wc -l <"$pf" | tr -d ' ')
                    psha=$(sha256_file "$pf")
                    route=$(awk '{print $1}' "$pf" | sort | uniq -c | sort -rn \
                        | awk '{printf "%s:%s,", $2, $1}' | sed 's/,$//' | cut -c1-200)
                    if [ "$pbytes" -gt "$CENSUS_MAX_PROOF_BYTES" ]; then
                        score="OVERSIZE"
                    elif want=$(veripb_entailed_conclusion "s $st" "$F" "$obj" 2>/dev/null); then
                        veripb_run "$VERIPB" --opb "$F" "$pf"
                        cexit=$VERIPB_EXIT
                        cverdict=${VERIPB_VERDICT:-<no-verdict-line>}
                        if veripb_accepted && [ "$VERIPB_VERDICT" = "s VERIFIED $want" ]; then
                            score="VERIFIED"
                        elif veripb_accepted; then
                            score="WRONG-CONCLUSION"
                        else
                            score="REJECT"
                        fi
                    else
                        want="<undefined>"
                        score="REJECT"
                    fi
                else
                    score="NO-PROOF-EMITTED"
                fi
                ;;
        esac
    fi

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$F" "$WHICH-$MODE" "$TMO" "$st" "${obj:--}" "$wall" \
        "$pbytes" "$plines" "$psha" "${route:--}" \
        "$cexit" "$cverdict" "$want" "$score"
    rm -f "$pf" "$sf"
}

IFS=',' read -ra SPECS <<< "$ARMS"
for spec in "${SPECS[@]}"; do
    IFS=':' read -r a_bin a_mode a_tmo <<< "$spec"
    run_arm "$a_bin" "$a_mode" "$a_tmo"
done
