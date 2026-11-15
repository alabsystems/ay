#!/bin/sh
# FAKE VeriPB checker (v): REFUSES the proof, and says so in prose.
#
# Its verdict line is a refusal — `s NOT VERIFIED` — but the human-readable
# comment line above it contains the words `VERIFIED UNSATISFIABLE`. Every
# structural reader in this repo rejects it on the verdict line alone. Any
# reader that scans stdout for a SUBSTRING accepts it, and what it accepts is
# not a weak verdict or a vacuous one: it is a REFUSAL read as an acceptance.
#
# This is not a strawman. `crates/ay-pb-core/src/veripb_runner.rs` decided
# acceptance with `stdout.contains("VERIFIED UNSATISFIABLE")` until this fake
# was committed, and the hazard was already written down in
# `crates/ay/src/maxsat_cert.rs` as a live defect in another module. A comment
# line is only the cheapest carrier; `s NOT VERIFIED UNSATISFIABLE` contains
# the same substring on the verdict line itself.
set -u
case "${1:-}" in --version) echo "Running VeriPB version 3.0.2"; echo "veripb 3.0.2"; exit 0 ;; esac
echo "Running VeriPB version 3.0.2"
echo "c the proof under test is NOT VERIFIED UNSATISFIABLE; see the verdict below"
echo "s NOT VERIFIED"
exit 0
