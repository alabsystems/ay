#!/bin/sh
# ay-script: sat-portfolio-driver
# ay_portfolio.sh — competition portfolio driver (SAT parallel/cloud track).
#
# Races several FULL `ay solve --competition` configurations as independent
# worker processes and emits the first worker to report a verdict. Each worker
# is a complete single-solver competition solve with every soundness gate
# intact (SAT models validated against the ORIGINAL CNF; UNSAT proofs emittable
# per worker via --proof), so any verdict this driver prints is as sound as the
# sequential binary — the portfolio can only ADD solves.
#
# WHY a driver instead of the built-in `--parallel`: the built-in portfolio's
# arms use a reduced config path (portfolio_default_features, with
# bve/congruence/decompose OFF for diversity) that does not reproduce the
# competition-config flips. Racing full --competition configs does. Demonstrated
# 2026-07-19 on a 6-core box at 120s: captures 3ef7fa06 UNSAT@72s, 4c3001f8
# SAT@70s, b3d3680b SAT@102s (arm B) while the default arm still solves the easy
# floor (df813fe7 UNSAT@26s).
#
# Arms are the campaign's verified per-instance-good levers — each net-negative
# as a single sequential default (twin-wall) but strictly additive as an
# independent portfolio arm:
#   A  default competition
#   B  equiticks + progress gate    (AY_AB_MODE_EQUITICKS=1 AY_AB_EQT_PROGRESS=1)
#   C  learned true-tail relocation  (opt-in AY_PF_ARM_C=1; needs >= ~4 real cores
#      or the heavy arms saturate memory bandwidth and starve each other)
#
# Usage: ay_portfolio.sh <cnf> [timeout_ms] [ay_binary]

CNF=$1
TMO_MS=${2:-120000}
AY=${3:-$(dirname "$0")/../target/release/ay}
if [ -z "$CNF" ]; then echo "usage: ay_portfolio.sh <cnf> [timeout_ms] [ay_binary]" >&2; exit 2; fi
WORK=$(mktemp -d "${TMPDIR:-/tmp}/ay_pf.XXXXXX")

PIDS=""
start_arm() {  # name env-assignments...
  name=$1; shift
  ( env "$@" "$AY" solve "$CNF" --competition -t "$TMO_MS" >"$WORK/out.$name" 2>"$WORK/err.$name"
    if grep -qiE '^s (SATISFIABLE|UNSATISFIABLE)' "$WORK/out.$name"; then : >"$WORK/win.$name"; fi ) &
  PIDS="$PIDS $!"
}

start_arm A
start_arm B AY_AB_MODE_EQUITICKS=1 AY_AB_EQT_PROGRESS=1
ARM_LIST="A B"
if [ "${AY_PF_ARM_C:-0}" = "1" ]; then
  start_arm C AY_SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION=1 AY_SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION=1
  ARM_LIST="A B C"
fi

deadline=$(( $(date +%s) + TMO_MS / 1000 + 10 ))
result=""
while [ "$(date +%s)" -lt "$deadline" ]; do
  for a in $ARM_LIST; do
    if [ -f "$WORK/win.$a" ]; then result="$WORK/out.$a"; break; fi
  done
  [ -n "$result" ] && break
  # stop early if every worker has exited without a verdict
  alive=0
  for p in $PIDS; do if kill -0 "$p" 2>/dev/null; then alive=1; fi; done
  [ "$alive" -eq 0 ] && break
  sleep 1
done

for p in $PIDS; do kill "$p" 2>/dev/null; done
if [ -n "$result" ]; then cat "$result"; else echo "s UNKNOWN"; fi
rm -rf "$WORK"
exit 0
