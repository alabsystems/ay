#!/bin/bash
# ay-script: pb-cert-coverage
# PB certificate (VeriPB) coverage probe.
#
# For each instance: solve with `--proof`, and if the verdict is OPTIMUM/UNSAT and
# a proof was written, run the REAL VeriPB checker on it. Records per instance:
#   VERIFIED          - VeriPB accepted the emitted proof
#   REJECT/[msg]      - a proof was emitted but VeriPB rejected it (a real bug)
#   NO-PROOF-EMITTED  - solved OPTIMUM/UNSAT but wrote no proof
#   -                 - not a certifiable verdict (SAT/UNKNOWN: nothing to check)
#
# The gap set = instances that solve to OPTIMUM WITHOUT --proof (measure separately)
# but land on anything other than VERIFIED here.
#
# Usage:
#   scripts/pb_cert_coverage.sh <ay-pb-bin> <veripb-bin> <list-file> <out-file> [timeout_ms]
# where <list-file> is one .opb path per line. VeriPB must be the format-3.0 build
# (MIAOresearch Rust rewrite); the legacy python VeriPB only reads format <=1.x.
set -u
BIN=$1; VERIPB=$2; LIST=$3; OUT=$4; TMO=${5:-20000}
: > "$OUT"
while read -r f; do
  [ -z "$f" ] && continue
  name=$(basename "$f" | sed 's/normalized-//;s/.opb.*//' | cut -c1-44)
  pf="/tmp/pbcc_$$.pbp"
  rm -f "$pf"
  st=$("$BIN" pb solve --timeout "$TMO" --proof "$pf" "$f" 2>/dev/null | grep '^s ' | tail -1 | sed 's/^s //')
  vr="-"
  if [ -s "$pf" ] && { [ "$st" = "UNSATISFIABLE" ] || [ "$st" = "OPTIMUM FOUND" ]; }; then
    v=$("$VERIPB" "$f" "$pf" 2>&1 | grep -iE '^s |VERIFIED|invalid|error|fail' | tail -1)
    case "$v" in
      *VERIFIED*) vr="VERIFIED" ;;
      *) vr="REJECT/[$v]" ;;
    esac
  elif { [ "$st" = "UNSATISFIABLE" ] || [ "$st" = "OPTIMUM FOUND" ]; }; then
    vr="NO-PROOF-EMITTED"
  fi
  printf "%-46s | %-14s | %s\n" "$name" "$st" "$vr" >> "$OUT"
  rm -f "$pf"
done < "$LIST"
echo "CERT COVERAGE DONE" >> "$OUT"
