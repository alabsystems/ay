#!/usr/bin/env bash
# ay-script: lra-bmc-validate
# File-aligned soundness + coverage validation for QF_LRA .bmc files.
set -u
BIN="$1"; TMO="$2"; LABEL="$3"; shift 3
ENVPREFIX="$*"
# Benchmark dir; override with LRA_VAL_DIR.
DIR="${LRA_VAL_DIR:-$(cd "$(dirname "$0")/.." && pwd)/benchmarks/smtcomp-incremental/QF_LRA/incremental/QF_LRA/hybrid_networks}"
total_def=0; total_conf=0
for f in "$DIR"/*.bmc_k100.smt2; do
  b=$(basename "$f" .smt2)
  z3file=/tmp/lra_val/z3_$b.txt
  out=/tmp/lra_val/ay_${LABEL}_$b.txt
  env $ENVPREFIX gtimeout "$TMO" "$BIN" "$f" 2>/dev/null > "$out"
  def=$(grep -cE '^(sat|unsat)$' "$out")
  conf=0; cdetail=""; i=0
  while IFS= read -r ayline; do
    i=$((i+1)); z3line=$(sed -n "${i}p" "$z3file")
    if { [ "$ayline" = "sat" ] || [ "$ayline" = "unsat" ]; } && \
       { [ "$z3line" = "sat" ] || [ "$z3line" = "unsat" ]; } && \
       [ "$ayline" != "$z3line" ]; then
      conf=$((conf+1)); cdetail="$cdetail line$i:AY=$ayline,z3=$z3line"
    fi
  done < "$out"
  total_def=$((total_def+def)); total_conf=$((total_conf+conf))
  echo "$b | def=$def | conflicts=$conf $cdetail"
done
echo "TOTAL [$LABEL] definite=$total_def conflicts=$total_conf"
