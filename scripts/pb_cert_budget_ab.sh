#!/bin/bash
# ay-script: pb-cert-budget-ab
#
# THE CERTIFICATE-BUDGET A/B. One instance, four arms, back to back, so BASE and
# HEAD see the same machine within seconds of each other:
#
#   1  base-noproof   the DENOMINATOR: optima AY reaches at this budget with
#                     proof logging OFF. It cannot come from a proof arm --
#                     `solve_optimization_with_proof` is fail-closed and
#                     downgrades an uncertifiable `s OPTIMUM FOUND` to
#                     `s SATISFIABLE`, so a proof arm scored against itself
#                     divides the certified count by itself.
#   2  base-proof     the NUMERATOR before the change
#   3  head-proof     the NUMERATOR after it
#   4  head-noproof   a CONTROL. The change touches only the proof path, so this
#                     arm must match arm 1. If it does not, the denominator
#                     moved and the coverage ratio is not comparable.
#
# The A,B,B,A order is deliberate: the two proof arms (the comparison that
# matters) are adjacent, and the two noproof arms bracket them, so a load ramp
# across the run shows up as a base/head noproof disagreement rather than
# hiding in the ratio.
#
# Both proof arms are scored by the PINNED checker through the shared verdict
# library (scripts/lib/veripb_verdict.sh) -- never a hand-rolled `grep VERIFIED`
# -- and each arm's proof is checked against the conclusion ITS OWN answer
# entails, so an arm reporting a different optimum is checked against that one.
#
# Budgets come from AY's own `--timeout`; no external killer is used (SIGALRM
# kills the process before it prints its answer and macOS has no `timeout`).
# `wall_ms` is recorded so budget overshoot is DATA, not an assumption.
#
# Usage: pb_cert_budget_ab.sh <base-bin> <head-bin> <veripb> <budget_ms> <label> <instance>
# Emits four TSV rows:
#   path  arm  budget_ms  status  objective  wall_ms  proof_bytes  proof_lines
#   proof_sha256  route  checker_exit  checker_verdict  want_verdict  score
set -u

BASE=$1; HEAD=$2; VERIPB=$3; TMO=$4; LABEL=$5; F=$6

. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib/veripb_verdict.sh"

work=$(mktemp -d "${TMPDIR:-/tmp}/ay-pb-budget-ab.XXXXXX")
trap 'rm -rf "$work"' EXIT

now_ms() { python3 -c 'import time;print(int(time.time()*1000))'; }

run_arm() {
    arm=$1; bin=$2; mode=$3
    pf="$work/proof.pbp"; sf="$work/stdout"
    rm -f "$pf" "$sf"

    t0=$(now_ms)
    if [ "$mode" = proof ]; then
        "$bin" pb solve --timeout "$TMO" --proof "$pf" "$F" >"$sf" 2>"$work/err"
    else
        "$bin" pb solve --timeout "$TMO" "$F" >"$sf" 2>"$work/err"
    fi
    ex=$?
    t1=$(now_ms)
    wall=$((t1 - t0))

    st=$(grep '^s ' "$sf" | tail -1 | sed 's/^s //')
    obj=$(grep '^o ' "$sf" | tail -1 | sed 's/^o //')
    # A run that printed no status line MEASURED NOTHING; record it as such,
    # with the exit code inline, never folded silently into UNKNOWN.
    [ -n "$st" ] || st="<no-s-line:exit=$ex>"

    pbytes=0; plines=0; psha="-"; route="-"
    cexit="-"; cverdict="-"; want="-"; score="-"

    if [ "$mode" = proof ]; then
        case "$st" in
            UNSATISFIABLE|SATISFIABLE|"OPTIMUM FOUND")
                if [ -s "$pf" ]; then
                    pbytes=$(wc -c <"$pf" | tr -d ' ')
                    plines=$(wc -l <"$pf" | tr -d ' ')
                    psha=$(sha256_file "$pf")
                    # Route fingerprint: the multiset of leading proof-rule
                    # tokens. Load-invariant, and it is what distinguishes the
                    # emitters from one another.
                    route=$(awk '{print $1}' "$pf" | sort | uniq -c | sort -rn \
                        | awk '{printf "%s:%s,", $2, $1}' | sed 's/,$//' | cut -c1-200)
                    if want=$(veripb_entailed_conclusion "s $st" "$F" "$obj" 2>/dev/null); then
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
        "$F" "$LABEL-$arm" "$TMO" "$st" "${obj:--}" "$wall" \
        "$pbytes" "$plines" "$psha" "${route:--}" \
        "$cexit" "$cverdict" "$want" "$score"
    rm -f "$pf" "$sf"
}

run_arm base-noproof "$BASE" noproof
run_arm base-proof   "$BASE" proof
run_arm head-proof   "$HEAD" proof
run_arm head-noproof "$HEAD" noproof
