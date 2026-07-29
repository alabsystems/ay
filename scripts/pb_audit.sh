#!/bin/sh
# ay-script: pb-audit
# Soundness audit: run ay-pb on each instance, verify SAT/OPTIMUM models against
# the .opb with an external model checker. Emits per-instance verdict + a tally.
#
# THREE UNSOUND GATES WERE REMOVED HERE.
#
#   1. `if echo "$v" | grep -q VALID` — `VALID` is a substring of `INVALID`, so
#      a checker reporting `MODEL INVALID` was tallied as SOUND. The audit could
#      not report an unsound model even when it found one. The verdict token is
#      now compared exactly, and `INVALID` is matched FIRST and explicitly.
#   2. `python3 /tmp/check_opb.py ... 2>/dev/null` — the validator is not in
#      this repository. On any machine without that untracked file the command
#      failed silently, `$v` was empty, and every model was tallied as
#      `!!UNSOUND!!`: a tally computed by a program that never ran. A missing
#      validator is now a hard error before any instance is solved.
#   3. The validator was piped through `tail`, so the pipeline reported
#      `tail`'s success even when the validator itself failed after printing a
#      plausible verdict. A nonzero validator exit is now a checker error.
#
# Set MODEL_CHECKER to the validator. It must exit zero and print a last line
# containing exactly one whitespace-delimited token `VALID` or `INVALID`
# (e.g. `MODEL VALID`), given `<instance.opb> <solver-output>`.
#
# Usage: pb_audit.sh BINARY TIMEOUT_S CORPUS_DIR OUTDIR
# Env:   MODEL_CHECKER  path to the OPB model validator (required)
set -eu
BIN=$1; TLS=$2; DIR=$3; OUTDIR=$4
TLMS=$(( TLS * 1000 ))

CHECKER=${MODEL_CHECKER:-}
if [ -z "$CHECKER" ] || [ ! -f "$CHECKER" ]; then
    echo "ERROR: this audit needs an OPB model validator and has none." >&2
    echo "       Set MODEL_CHECKER=<path to check_opb.py>." >&2
    echo "       Refusing to print a soundness tally that no validator produced:" >&2
    echo "       the previous behaviour was to report every model '!!UNSOUND!!'" >&2
    echo "       when the validator was simply absent." >&2
    exit 2
fi

mkdir -p "$OUTDIR"
PASS=0; FAIL=0; NA=0; ERR=0
for f in $(find "$DIR" -name '*.opb' | sort); do
    inst=$(basename "$f" .opb)
    o="$OUTDIR/$inst.out"
    "$BIN" pb solve --timeout "$TLMS" "$f" > "$o" 2>/dev/null || true
    s=$(grep -E '^s ' "$o" | tail -1 | sed 's/^s //')
    case "$s" in
        SATISFIABLE|"OPTIMUM FOUND")
            checker_out="$OUTDIR/$inst.checker.out"
            checker_exit=0
            python3 "$CHECKER" "$f" "$o" >"$checker_out" \
                2>"$OUTDIR/$inst.checker.err" || checker_exit=$?
            v=$(tail -1 "$checker_out")
            verdict=$(printf '%s\n' "$v" | awk '
                {
                    for (i = 1; i <= NF; i++) {
                        if ($i == "INVALID") invalid = 1
                        if ($i == "VALID") valid = 1
                    }
                }
                END {
                    if (invalid && valid) print "AMBIGUOUS"
                    else if (invalid) print "INVALID"
                    else if (valid) print "VALID"
                }')
            if [ "$checker_exit" -ne 0 ]; then
                ERR=$((ERR+1))
                tag="CHECKER-ERROR[exit=$checker_exit ${v:-no output}]"
            else
                case "$verdict" in
                # INVALID is a distinct token now, not a substring match.
                INVALID) FAIL=$((FAIL+1)); tag="!!UNSOUND!!" ;;
                VALID)   PASS=$((PASS+1)); tag="SOUND" ;;
                # No usable verdict is not a pass and not a soundness failure —
                # it is an audit failure, and it is counted as its own thing so
                # it cannot hide inside either column.
                *)       ERR=$((ERR+1));  tag="CHECKER-ERROR[${v:-no output}]" ;;
                esac
            fi
            printf '%-55s %-14s %s\n' "$inst" "$s" "$tag" ;;
        *) NA=$((NA+1)); printf '%-55s %-14s\n' "$inst" "$s" ;;
    esac
done
echo "=== AUDIT: model-valid=$PASS unsound=$FAIL checker-error=$ERR non-model=$NA ==="
if [ "$FAIL" -ne 0 ] || [ "$ERR" -ne 0 ]; then
    exit 1
fi
