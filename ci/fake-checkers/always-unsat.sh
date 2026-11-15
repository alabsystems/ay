#!/bin/sh
# FAKE VeriPB checker (iii): everything is unsatisfiable.
#
# Prints `s VERIFIED UNSATISFIABLE` and exits 0 for ANY formula and ANY proof,
# including a satisfiable formula with an empty proof. This is not a strawman:
# published VeriPB 3.0.2 does exactly this on the fixtures in
# ci/veripb-soundness (bugs 03 and 04) — that is why the pin carries a patch.
set -u
case "${1:-}" in --version) echo "Running VeriPB version 3.0.2"; echo "veripb 3.0.2"; exit 0 ;; esac
echo "Running VeriPB version 3.0.2"
echo "s VERIFIED UNSATISFIABLE"
exit 0
