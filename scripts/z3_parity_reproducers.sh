#!/bin/sh
# Run the campaign's landed-fix reproducers against a binary and print a table.
#
# Every fix merged for the Z3-replacement campaign names reproducers that must
# keep their verdict. This runs them all in one pass so a merge can be checked
# in a minute instead of hunting through eight commit messages. It is a
# smoke test, not evidence: it says "nothing obviously broke", never "this is
# faster" — the timings move by 3x with machine load. For evidence use
# scripts/z3_division_scan.py, which records solver provenance.
#
#   scripts/z3_parity_reproducers.sh [ay-binary] [timeout-seconds]
#
# Defaults to ~/ay-bench/target-main/release/ay and 60 s. Anything that misses is
# retried once at four times the deadline before being called a failure: several
# of these sit within 2x of any reasonable envelope, and at load 40+ a tight
# deadline reports noise as regression.

AY="${1:-$HOME/ay-bench/target-main/release/ay}"
TO="${2:-60}"
C="benchmarks/smtlib-all"

if [ ! -x "$AY" ]; then
    echo "no such binary: $AY" >&2
    exit 2
fi

echo "binary:  $AY"
"$AY" --version 2>/dev/null | head -1 | sed 's/^/version: /'
echo "timeout: ${TO}s"
echo "load:   $(uptime | sed 's/.*averages*: *//')"
echo

printf '%-9s %-9s %-52s %s\n' EXPECT GOT FILE FIX
fail=0

check() {
    expect="$1"; fix="$2"; file="$3"
    if [ ! -f "$file" ]; then
        printf '%-9s %-9s %-52s %s\n' "$expect" "MISSING" "$(basename "$file" | cut -c1-52)" "$fix"
        return
    fi
    got=$("$AY" --quiet -T:"$TO" "$file" 2>/dev/null | grep -E '^(sat|unsat|unknown)$' | tail -1)
    [ -z "$got" ] && got="none"
    mark=""
    if [ "$got" != "$expect" ]; then
        # Do not cry wolf. Run-to-run spread on a loaded host exceeds the effect
        # of most of these fixes, and several reproducers sit within 2x of any
        # reasonable envelope. Give it one much longer retry before reporting.
        got2=$("$AY" --quiet -T:$((TO * 4)) "$file" 2>/dev/null | grep -E '^(sat|unsat|unknown)$' | tail -1)
        if [ "$got2" = "$expect" ]; then
            got="$expect"
            mark="   (needed ${TO}s x4 under load)"
        else
            got="${got2:-none}"
            mark="   <<< expected $expect"
            fail=$((fail + 1))
        fi
    fi
    printf '%-9s %-9s %-52s %s%s\n' "$expect" "$got" "$(basename "$file" | cut -c1-52)" "$fix" "$mark"
}

# Difference-logic lane: unreachable in the default posture, BigRational
# weights, no implied-atom propagation. Merge aaa1f6e066.
check sat   "diff-logic"   "$C/QF_IDL/non-incremental__QF_IDL__job_shop__jobshop36-2-18-18-2-4-12.smt2"
check unsat "diff-logic"   "$C/QF_IDL/non-incremental__QF_IDL__parity__13.400.graph.smt2"

# LRA implied-bound propagation: the freshness gate dropped 100% of
# compound-atom propagations. Merge f93c7428c2.
check sat   "lra-prop"     "$C/QF_LRA/non-incremental__QF_LRA__sc__sc-20.induction3.cvc.smt2"

# Bool-element arrays returned an instant unknown. Merge b3618ad141.
check sat   "bool-array"   "benchmarks/smt/array_bv_simple.smt2"

# QF_AUFLIA skolemized-witness families: a correct model was repaired until the
# oracle rejected it. Merge 247a2e85b1. z3 answers sat on all 399.
# Pick a file the fix's own report verified as flipping, not merely one the
# diagnosis named: t3_pp_sf_ni_00030_006 appears in the diagnosis but was never
# among the 45 that converted, and using it made this check cry wolf on every
# run. This one goes unknown -> sat in well under a second.
check sat   "auflia-gate"  "$C/QF_AUFLIA/non-incremental__QF_AUFLIA__storecomm__storecomm_invalid_t1_pp_sf_ni_00030_005.cvc.smt2"

# DT + nonlinear Int was collapsed to an unsupported category. Merge 793c1c88b2.
check unsat "dt-routing"   "$C/AUFBVDTNIA/non-incremental__AUFBVDTNIA__20172804-Barrett__rec-fun-ijcar2016__wo__wo_fd_vcs__2.5-cvc4-SumAndMax.scala-10.smt2"

# UF+LRA / UF+NRA post-split UNSAT: the lane derived the refutation and the
# stale-clause guard discarded it, because it never opted into verification.
# Merge ff7a47c835.
check unsat "postsplit"    "$C/QF_UFLRA/non-incremental__QF_UFLRA__mathsat__RandomDecoupled__pb_real_30_75_45_81.smt2"
check unsat "postsplit"    "$C/QF_UFNRA/non-incremental__QF_UFNRA__FFT__smtlib.630867.smt2"

# Control: a division AY scores near-perfectly on. Losing anything here is a
# stop-and-report condition, not an acceptable trade.
check unsat "control"      "$C/QF_AX/non-incremental__QF_AX__swap__swap_t2_np_sf_ai_00009_003.cvc.smt2"

echo
if [ "$fail" -eq 0 ]; then
    echo "all reproducers hold"
else
    echo "$fail reproducer(s) off expectation"
    echo "Before calling any of them a regression, re-run at -T:120 several times:"
    echo "run-to-run spread on a loaded host exceeds the effect of most fixes."
fi
exit "$fail"
