#!/bin/bash
# Reap orphaned AY solver processes left behind by A/B harnesses.
#
# WHY THIS EXISTS. Twice now, agent-written A/B scripts have leaked solver
# processes that outlived their parent: 93 on 2026-08-15 (oldest 1d20h) and 207
# on 2026-08-18 (ay-diag 87, ay-before 60, ay-after 60). The second swarm drove
# load average to 310 and CPU-starved a scored division run — 26 of 139 rows
# came back with wall 1195s against cpu 48s, which reads exactly like a
# capability regression and is not one. The instance that "regressed" answers
# unsat in 649s on a quiet host.
#
# A scored run needs a QUIET HOST. That is not a nicety: it is one of the
# conditions that made the banked sq-dt-clean measurement defensible.
#
# Usage:
#   scripts/reap_orphan_solvers.sh            # report only
#   scripts/reap_orphan_solvers.sh --kill     # kill anything older than MAX_AGE
#
# An AY solve is bounded by its -T: budget (worst case ~20 min), so any solver
# older than an hour has lost its parent and is pure waste.
set -uo pipefail
MAX_AGE_SEC=${MAX_AGE_SEC:-3600}
KILL=0
[ "${1:-}" = "--kill" ] && KILL=1

age_seconds() {  # etime -> seconds; handles [[dd-]hh:]mm:ss
  local e=$1 d=0 h=0 m=0 s=0
  case "$e" in
    *-*) d=${e%%-*}; e=${e#*-} ;;
  esac
  case "$e" in
    *:*:*) h=${e%%:*}; e=${e#*:}; m=${e%%:*}; s=${e##*:} ;;
    *:*)   m=${e%%:*}; s=${e##*:} ;;
    *)     s=$e ;;
  esac
  echo $(( 10#$d*86400 + 10#$h*3600 + 10#$m*60 + 10#$s ))
}

found=0; killed=0
for pid in $(pgrep -f "scratchpad.*/ay[-/]|worktrees/.*/target/release/ay" 2>/dev/null); do
  et=$(ps -o etime= -p "$pid" 2>/dev/null | tr -d ' ')
  [ -z "$et" ] && continue
  secs=$(age_seconds "$et")
  [ "$secs" -lt "$MAX_AGE_SEC" ] && continue
  found=$((found+1))
  cmd=$(ps -o comm= -p "$pid" 2>/dev/null | tail -c 60)
  if [ "$KILL" = "1" ]; then
    kill -9 "$pid" 2>/dev/null && killed=$((killed+1))
    echo "reaped pid $pid age $et  $cmd"
  else
    echo "ORPHAN pid $pid age $et  $cmd"
  fi
done
echo "orphans older than ${MAX_AGE_SEC}s: $found (killed: $killed)"
[ "$KILL" = "0" ] && [ "$found" -gt 0 ] && echo "re-run with --kill to reap them"
exit 0
