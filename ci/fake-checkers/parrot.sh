#!/bin/sh
# FAKE VeriPB checker (iv): echoes back whatever verdict makes the caller happy.
#
# It never checks anything. It reads the `conclusion` line the PROOF ITSELF
# claims and restates it in VeriPB's verdict grammar, then exits 0:
#
#   conclusion UNSAT ...        -> s VERIFIED UNSATISFIABLE
#   conclusion SAT : <sol>      -> s VERIFIED SATISFIABLE
#   conclusion BOUNDS lo : id hi : <sol>
#                               -> s VERIFIED BOUNDS lo <= obj <= hi
#   conclusion NONE             -> s VERIFIED NO CONCLUSION
#
# This is the dangerous one. A proof is a claim; a checker exists to test that
# claim. A parrot agrees with the claim by construction, so it passes every
# gate that only asks "did the checker confirm what we expected" — including
# exact-conclusion matching and the status/conclusion cross-check, because the
# solver writes the conclusion line and the gate derives the expectation from
# the same answer. The ONLY thing that catches it is a probe whose proof states
# a conclusion that is FALSE for the formula.
set -u
case "${1:-}" in --version) echo "Running VeriPB version 3.0.2"; echo "veripb 3.0.2"; exit 0 ;; esac

proof=""
for arg in "$@"; do
    case "$arg" in --*) continue ;; esac
    proof=$arg
done
[ -n "$proof" ] && [ -r "$proof" ] || { echo "s VERIFIED NO CONCLUSION"; exit 0; }

line=$(grep '^conclusion' "$proof" 2>/dev/null | tail -1 | tr -d ';')
echo "Running VeriPB version 3.0.2"
# shellcheck disable=SC2086
set -- $line
kind=${2:-NONE}
case "$kind" in
    UNSAT)  echo "s VERIFIED UNSATISFIABLE" ;;
    SAT)    echo "s VERIFIED SATISFIABLE" ;;
    BOUNDS) echo "s VERIFIED BOUNDS ${3:-?} <= obj <= ${6:-${3:-?}}" ;;
    *)      echo "s VERIFIED NO CONCLUSION" ;;
esac
exit 0
