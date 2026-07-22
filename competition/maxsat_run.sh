#!/bin/sh
# ay-script: maxsat-driver
# maxsat_run.sh — competition driver for the weighted/unweighted MaxSAT track.
#
# WHY THIS EXISTS: `ay maxsat solve` defaults its two optional lanes OFF — the
# native MILP-race lane (#maxsat-milp-race) and the BCE preprocessing lane
# (#maxsat-bce-preprocess). They are default-off ONLY because at `bench --jobs N`
# (N>1) the extra threads oversubscribe the box and cost more borderline solves
# than they win. The actual competition runs ONE instance per machine, where the
# second thread is free and BCE's hard-clause reduction is a pure win. Measured
# same-hardware, 60s, model+optimum verified, ZERO wrong:
#   default (lanes off):   322 / 571   ← what a bare `ay maxsat solve` scores
#   all-lanes (this):      331 / 571   ← +9 (MILP flips warehouses/auctions,
#                                          BCE flips metro x3, full-core flips
#                                          rna/synplicate/mpe/causal/drmx/max)
# So a submission MUST run through this wrapper (or set the two env vars) or it
# silently leaves 9 solves on the table. This is the config the campaign's
# competition-protocol number (331, #3 behind cgss2 >=343, uwrmaxsat >=359) was
# measured with — see memory/maxsat-weighted-win-handoff.md.
#
# Every lane is fail-closed and independently re-verified (the MILP lane's win
# is cross-checked against the OLL lane's state; the harness re-verifies the
# reported model + optimum), so this wrapper is exactly as sound as the bare
# binary — it can only ADD solves, never change an answer.
#
# Usage: maxsat_run.sh <wcnf> [timeout_s] [ay_binary]
#   Emits DIMACS MaxSAT competition output on stdout (o / s / v lines).

WCNF=$1
TMO_S=${2:-60}
AY=${3:-$(dirname "$0")/../target/release/ay}
if [ -z "$WCNF" ]; then
  echo "usage: maxsat_run.sh <wcnf> [timeout_s] [ay_binary]" >&2
  exit 2
fi

# The verified competition config: OLL engine + native MILP race + BCE lane.
# One instance per machine ⇒ the race thread and BCE pass are free here.
exec env \
  AY_AB_MAXSAT_MILP_RACE=1 \
  AY_AB_MAXSAT_BCE=1 \
  "$AY" maxsat solve "$WCNF" --timeout "$TMO_S"
