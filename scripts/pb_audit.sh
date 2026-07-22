#!/bin/sh
# ay-script: pb-audit
# Soundness audit: run ay-pb on each instance, verify SAT/OPTIMUM models against
# the .opb with check_opb.py. Emits per-instance verdict + a final tally.
# Usage: pb_audit.sh BINARY TIMEOUT_S CORPUS_DIR OUTDIR
set -eu
BIN=$1; TLS=$2; DIR=$3; OUTDIR=$4
TLMS=$(( TLS * 1000 ))
mkdir -p "$OUTDIR"
PASS=0; FAIL=0; NA=0
for f in $(find "$DIR" -name '*.opb' | sort); do
    inst=$(basename "$f" .opb)
    o="$OUTDIR/$inst.out"
    "$BIN" pb solve --timeout "$TLMS" "$f" > "$o" 2>/dev/null || true
    s=$(grep -E '^s ' "$o" | tail -1 | sed 's/^s //')
    case "$s" in
        SATISFIABLE|"OPTIMUM FOUND")
            v=$(python3 /tmp/check_opb.py "$f" "$o" 2>/dev/null | tail -1)
            if echo "$v" | grep -q VALID; then PASS=$((PASS+1)); tag="SOUND"; else FAIL=$((FAIL+1)); tag="!!UNSOUND!!"; fi
            printf '%-55s %-14s %s\n' "$inst" "$s" "$tag" ;;
        *) NA=$((NA+1)); printf '%-55s %-14s\n' "$inst" "$s" ;;
    esac
done
echo "=== AUDIT: model-valid=$PASS unsound=$FAIL non-model=$NA ==="
