#!/bin/zsh
# ay-script: prof-hotspots
# Profile AY on a benchmark with macOS `sample`, print top-of-stack self-time.
# Usage: prof_hotspots.sh <smt2> <sample_secs> <warmup_secs>
B=${AY_BIN:-target/release/ay}
F="$1"; SECS="${2:-15}"; WARM="${3:-2}"
OUT=/tmp/prof_$(basename "$F" .smt2).sample
"$B" solve "$F" >/dev/null 2>&1 &
WPID=$!
sleep "$WARM"
CHILD=$(pgrep -P $WPID 2>/dev/null | tail -1); [ -z "$CHILD" ] && CHILD=$WPID
# go one more level deep (wrapper re-execs)
GC=$(pgrep -P $CHILD 2>/dev/null | tail -1); [ -n "$GC" ] && CHILD=$GC
sample $CHILD "$SECS" -file "$OUT" >/dev/null 2>&1
kill -9 $WPID 2>/dev/null; pkill -9 -f "$(basename $F)" 2>/dev/null
echo "### $(basename $F)  (pid $CHILD)"
# Extract "Sort by top of stack" self-time section, skip kernel wait frames
awk '/Sort by top of stack/{f=1;next} f&&/^$/{exit} f{print}' "$OUT" \
  | grep -vE 'ulock_wait|semwait_signal|mach_msg|swtch|psynch|read_with_filename|kevent|workq' \
  | sed -E 's/\(in [^)]*\)//; s/::h[0-9a-f]+//; s/ \+ [0-9]+ +\[0x[0-9a-f]+\]//' \
  | head -14
echo ""
