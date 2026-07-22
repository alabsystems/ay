#!/bin/sh
# ay-script: pb-bench
# Parallel PB benchmark runner for AY.
# Usage: pb_bench.sh BINARY TIMEOUT_S CORPUS_DIR OUTCSV [JOBS] [EXTRA_ARGS...]
# Emits CSV: category|instance|result|seconds|objective
set -eu

BIN=$1; TLS=$2; DIR=$3; OUT=$4; JOBS=${5:-8}
shift 5 2>/dev/null || shift 4
EXTRA="$*"
TLMS=$(( TLS * 1000 ))

# OOM guard (2026-06-19 / 2026-07-11 watchdog panics — scripts/_oom_guard.py):
# cap JOBS to a safe RAM budget and export a per-child MEMLIMIT (MiB) + NBCORE.
# MEMLIMIT is honored internally only by ay-pb-lineage binaries. Every child is
# therefore also wrapped by `_oom_guard.py run`, which applies the shared RSS
# watchdog to the whole process group. This is the enforced backstop for the
# main `ay pb` subcommand and external binaries that ignore MEMLIMIT.
# MEMLIMIT/NBCORE already set in the environment always win.
OOM_GUARD=$(dirname "$0")/_oom_guard.py
PLAN=$(python3 "$OOM_GUARD" plan --jobs "$JOBS" --label pb_bench.sh --warn-concurrent-build)
eval "$PLAN"
REQUESTED_JOBS=$JOBS
if [ "$JOBS" -gt "$PLAN_JOBS" ]; then JOBS=$PLAN_JOBS; fi
if [ "$PLAN_MEMLIMIT_MB" -gt 0 ] && [ -z "${MEMLIMIT:-}" ]; then
    MEMLIMIT=$PLAN_MEMLIMIT_MB; export MEMLIMIT
fi
if [ -z "${NBCORE:-}" ]; then NBCORE=$PLAN_NBCORE; export NBCORE; fi
WATCH_MB=${MEMLIMIT:-$PLAN_MEMLIMIT_MB}
case "$WATCH_MB" in ''|*[!0-9]*) echo "invalid MEMLIMIT: $WATCH_MB" >&2; exit 2;; esac
echo "=== oom-guard plan: requested_jobs=$REQUESTED_JOBS jobs=$JOBS MEMLIMIT=${MEMLIMIT:-unset} NBCORE=$NBCORE headroom=${PLAN_HEADROOM_MB}MB enforcement=rss_watchdog ===" >&2

: > "$OUT.tmp"
run_one() {
    f=$1
    cat=$(basename "$(dirname "$(dirname "$f")")")
    # category is the dir two up only for nested; fall back to parent
    case "$f" in
      *DEC-LIN*) cat=DEC-LIN;; *OPT-LIN*) cat=OPT-LIN;;
      *OPT-NLC*) cat=OPT-NLC;; *DEC-NLC*) cat=DEC-NLC;;
      *SOFT*) cat=SOFT-LIN;; *PARTIAL*) cat=PARTIAL-LIN;; *) cat=OTHER;;
    esac
    inst=$(basename "$f")
    start=$(perl -MTime::HiRes=time -e 'print time')
    # Whole-tree hard wall cap plus external RSS enforcement. The wrapper
    # preserves solver stdout for the normal PB result parser below.
    if out=$(python3 "$OOM_GUARD" run --limit-mb "$WATCH_MB" \
        --timeout-s "$((TLS + 15))" --label "pb_bench.sh[$inst]" -- \
        "$BIN" pb solve --timeout "$TLMS" $EXTRA "$f" 2>/dev/null); then
        rc=0
    else
        rc=$?
    fi
    end=$(perl -MTime::HiRes=time -e 'print time')
    secs=$(perl -e 'printf "%.2f", $ARGV[1]-$ARGV[0]' "$start" "$end")
    sline=$(printf '%s\n' "$out" | grep -E '^s ' | tail -1 | sed 's/^s //')
    obj=$(printf '%s\n' "$out" | grep -E '^o ' | tail -1 | sed 's/^o //')
    if [ "$rc" -eq 86 ]; then sline="MEMOUT"
    elif [ "$rc" -eq 124 ]; then sline="TIMEOUT"
    elif [ -z "$sline" ] && [ "$rc" -ne 0 ]; then sline="CRASH($rc)"
    elif [ -z "$sline" ]; then sline="NO-OUTPUT"
    fi
    printf '%s|%s|%s|%s|%s|%s|%s|%s|%s|%s|%s\n' \
      "$cat" "$inst" "$sline" "$secs" "$obj" "$REQUESTED_JOBS" "$JOBS" \
      "$WATCH_MB" "$NBCORE" "$PLAN_HEADROOM_MB" "rss_watchdog" >> "$OUT.tmp"
    printf '  %-50s %-16s %ss\n' "$inst" "$sline" "$secs" >&2
}

i=0
for f in $(find "$DIR" -name '*.opb' -o -name '*.wbo' | sort); do
    run_one "$f" &
    i=$((i+1))
    if [ $((i % JOBS)) -eq 0 ]; then wait; fi
done
wait

echo "category|instance|result|seconds|objective|resource_requested_jobs|resource_jobs|resource_memlimit_mb|resource_nbcore|resource_headroom_mb|resource_enforcement" > "$OUT"
sort "$OUT.tmp" >> "$OUT"
rm -f "$OUT.tmp"
echo "=== wrote $OUT ===" >&2
