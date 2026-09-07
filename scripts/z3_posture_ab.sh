#!/bin/sh
# Is QF_UFLRA verdict-dependent on posture, or just nondeterministic?
# Round 3 warned ~8% of files flip "in both directions", which would be a real
# cost of defaulting to the fast posture. Three repetitions per posture is the
# only way to separate the two.
AY=~/ay-bench/target-main/release/ay
C=benchmarks/smtlib-all/QF_UFLRA
FILES=$(ls $C/*.smt2 | awk 'NR % 137 == 3' | head -12)
printf '%-52s %-24s %s\n' FILE "default(3 runs)" "fast(3 runs)"
for f in $FILES; do
  d=""; s=""
  for i in 1 2 3; do
    d="$d$($AY --quiet -T:20 "$f" 2>/dev/null | grep -E '^(sat|unsat|unknown)$' | tail -1 | cut -c1-2),"
    s="$s$($AY --quiet --rigor fast -T:20 "$f" 2>/dev/null | grep -E '^(sat|unsat|unknown)$' | tail -1 | cut -c1-2),"
  done
  printf '%-52s %-24s %s\n' "$(basename $f | cut -c30-81)" "$d" "$s"
done
