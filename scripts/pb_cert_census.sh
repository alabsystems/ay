#!/bin/bash
# ay-script: pb-cert-census
#
# ONE INSTANCE, ALL FOUR ARMS, BACK TO BACK. The per-instance worker behind the
# PB certificate census. It is a WORKER, not a harness: it is invoked once per
# instance (by `xargs -P`) so instances never share a temp path.
#
# WHY ALL FOUR ARMS IN ONE WORKER — this is the measurement design, not a
# convenience. Coverage is a RATIO of two arms:
#
#   numerator    proof@B      certificates the PINNED checker accepts
#   denominator  noproof@B    optima AY reaches at the same budget with proof
#                             logging OFF
#
# and this box is shared (14 CPUs, observed 1-minute load 10-72). Running the
# arms as two separate sweeps would measure the numerator and the denominator
# under DIFFERENT loads and bias the ratio by an unknown amount in an unknown
# direction. Running them adjacently per instance is the A,B,A,B interleave:
# each instance's four numbers see the same machine within seconds of each
# other. Absolute counts still move with load; the ratio is protected.
#
# THE DENOMINATOR CANNOT COME FROM THE PROOF ARM. In proof mode AY is
# fail-closed: `solve_optimization_with_proof` (crates/ay/src/cmd_pb.rs)
# DISCARDS its proof and downgrades `s OPTIMUM FOUND` to `s SATISFIABLE` /
# `s UNKNOWN` whenever it cannot certify. Scoring the proof arm against itself
# would divide the certified count by itself and report ~100%.
#
# Emits ONE tab-separated row PER ARM on stdout:
#
#   path  mode  budget_ms  status  objective  wall_ms  proof_bytes  proof_lines
#   proof_sha256  route  checker_exit  checker_verdict  want_verdict  score
#
# where `score` is one of
#
#   VERIFIED           the checker confirmed EXACTLY the conclusion AY's own
#                      answer entails (`s VERIFIED BOUNDS v <= obj <= v` for
#                      `s OPTIMUM FOUND` with `o v`)
#   REJECT             a proof was emitted and the checker did NOT confirm it.
#                      A SOUNDNESS ALARM, never a coverage miss.
#   WRONG-CONCLUSION   the checker verified a DIFFERENT truth than AY claimed.
#                      The worst outcome on this list.
#   NO-PROOF-EMITTED   a certifiable verdict with no proof file
#   OVERSIZE           a proof too large to check under the census disk budget
#                      (recorded, never scored as coverage)
#   -                  not a certifiable verdict (nothing to check)
#
# WHY THE VERDICT LOGIC IS NOT LOCAL. It is `scripts/lib/veripb_verdict.sh`,
# the same implementation the certified gate uses, because every hand-rolled
# `grep VERIFIED` in this repo's history has been unsound in at least one of
# four ways (see that file's header). Do not re-implement it here.
#
# BUDGETS. AY is given its OWN budget via `--timeout`; no external killer is
# used, because SIGALRM kills the process before it prints its answer and macOS
# has no `timeout` binary. `wall_ms` is recorded for every arm precisely so that
# AY's honouring of its own budget is DATA rather than an assumption — in proof
# mode it is routinely violated, and the census says so. The CHECKER has no
# internal budget, so it is bounded by a proof-size gate instead: a proof larger
# than CENSUS_MAX_PROOF_BYTES is recorded OVERSIZE and not checked.
#
# TWO BINARIES, NOT ONE. `cli` is the shipped `ay pb solve`
# (crates/ay, src/cmd_pb.rs); `aypb` is the competition binary `ay-pb`
# (crates/ay-pb, src/bin/ay.rs). They are different programs with different
# certificate routes: the four OPT-LIN FLOOR emitters (trivial_zero,
# knapsack_cardinality, direct_aggregation, lp_dual_floor) are named in
# `crates/ay-pb/src/bin/ay.rs` and NOWHERE in the `ay` CLI's PB path, and
# `certify_opt_lin_bounds_compact` does not delegate to them. A coverage figure
# that does not say which binary produced it is not a figure, so the census
# measures both, back to back, on the same instance.
#
# Usage:
#   pb_cert_census.sh <ay-cli> <ay-pb> <veripb-bin> <arm-spec> <instance>
# where <arm-spec> is a comma-separated list of `bin:mode:budget_ms` run in
# order, e.g. `cli:noproof:5000,cli:proof:5000,aypb:noproof:5000,aypb:proof:5000`.
set -u

CLI=$1; PBBIN=$2; VERIPB=$3; ARMS=$4; F=$5

: "${CENSUS_MAX_PROOF_BYTES:=1073741824}"

. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib/veripb_verdict.sh"

work=$(mktemp -d "${TMPDIR:-/tmp}/ay-pb-census.XXXXXX")
trap 'rm -rf "$work"' EXIT

now_ms() { python3 -c 'import time;print(int(time.time()*1000))'; }

run_arm() {
    WHICH=$1; MODE=$2; TMO=$3
    case "$WHICH" in
        cli)  BIN=$CLI ;;
        aypb) BIN=$PBBIN ;;
        *) echo "unknown binary key '$WHICH'" >&2; return 1 ;;
    esac
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
    # A run that printed no status line MEASURED NOTHING. It is recorded as
    # such, with the exit code inline, never silently folded into UNKNOWN.
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
                    # Route fingerprint: the multiset of leading proof-rule
                    # tokens. Load-invariant, and it is what actually
                    # distinguishes the emitters from one another.
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
