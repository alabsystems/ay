#!/bin/bash
# ay-script: pb-cert-coverage
# PB certificate (VeriPB) coverage probe.
#
# For each instance: solve with `--proof`, and if a proof was written for a
# certifiable verdict, run the REAL VeriPB checker on it and require the
# conclusion AY's OWN ANSWER entails. Records per instance:
#   VERIFIED          - VeriPB confirmed exactly the conclusion AY claimed
#   REJECT/[msg]      - a proof was emitted but VeriPB did not confirm it
#   WRONG-CONCLUSION/[...]
#                     - VeriPB verified something OTHER than AY's claim. This is
#                       the worst outcome on the list and is never a pass.
#   NO-PROOF-EMITTED  - solved SAT/UNSAT/OPTIMUM but wrote no proof
#   -                 - not a certifiable verdict (UNKNOWN: nothing to check)
#
# The gap set = instances that solve to OPTIMUM WITHOUT --proof (measure separately)
# but land on anything other than VERIFIED here.
#
# WHY THIS IS NOT A `grep VERIFIED`. It used to be:
#
#     case "$v" in *VERIFIED*) vr="VERIFIED" ;; *) vr="REJECT/[$v]" ;; esac
#
# which scored `s VERIFIED NO CONCLUSION` — a proof that proves nothing — as a
# verified certificate, would have scored `s VERIFIED SATISFIABLE` as a verified
# refutation, ignored the checker's exit code, and let the checker guess the
# formula parser from the file extension. Coverage numbers produced that way
# were an overcount of unknown size. The verdict contract now comes from the one
# shared implementation in scripts/lib/veripb_verdict.sh, and the checker must
# pass its self-test battery before a single row is scored.
#
# SAT rows are now scored too (they used to be skipped as "nothing to check"):
# a solution-only certificate is exactly the artefact a checker can validate
# cheaply, and an unchecked model is how a wrong `s SATISFIABLE` ships.
#
# Usage:
#   scripts/pb_cert_coverage.sh <ay-pb-bin> <veripb-bin> <list-file> <out-file> [timeout_ms]
# where <list-file> is one .opb path per line. VeriPB must be the format-3.0 build
# (MIAOresearch Rust rewrite); the legacy python VeriPB only reads format <=1.x.
set -u
BIN=$1; VERIPB=$2; LIST=$3; OUT=$4; TMO=${5:-20000}

. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib/veripb_verdict.sh"

# A coverage number is only as trustworthy as the checker that produced it.
veripb_require_self_test "$VERIPB"

: > "$OUT"
while read -r f; do
  [ -z "$f" ] && continue
  name=$(basename "$f" | sed 's/normalized-//;s/.opb.*//' | cut -c1-44)
  pf="/tmp/pbcc_$$.pbp"
  sf="/tmp/pbcc_$$.stdout"
  rm -f "$pf" "$sf"
  "$BIN" pb solve --timeout "$TMO" --proof "$pf" "$f" >"$sf" 2>/dev/null
  st=$(grep '^s ' "$sf" | tail -1 | sed 's/^s //')
  obj=$(grep '^o ' "$sf" | tail -1 | sed 's/^o //')
  vr="-"
  case "$st" in
    UNSATISFIABLE|SATISFIABLE|"OPTIMUM FOUND")
      if [ -s "$pf" ]; then
        if want=$(veripb_entailed_conclusion "s $st" "$f" "$obj" 2>/dev/null); then
          veripb_run "$VERIPB" --opb "$f" "$pf"
          if veripb_accepted && [ "$VERIPB_VERDICT" = "s VERIFIED $want" ]; then
            vr="VERIFIED"
          elif veripb_accepted; then
            # The checker verified a DIFFERENT truth than the one AY reported.
            vr="WRONG-CONCLUSION/[claimed 's VERIFIED $want', got '$VERIPB_VERDICT']"
          else
            vr="REJECT/[exit=$VERIPB_EXIT ${VERIPB_VERDICT:-<no verdict line>}]"
          fi
        else
          vr="REJECT/[no conclusion is defined for status '$st']"
        fi
      else
        vr="NO-PROOF-EMITTED"
      fi
      ;;
  esac
  printf "%-46s | %-14s | %s\n" "$name" "$st" "$vr" >> "$OUT"
  rm -f "$pf" "$sf"
done < "$LIST"
echo "CERT COVERAGE DONE" >> "$OUT"
