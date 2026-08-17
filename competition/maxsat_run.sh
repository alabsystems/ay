#!/bin/sh
# ay-script: maxsat-driver
# maxsat_run.sh — competition driver for the weighted/unweighted MaxSAT track.
#
# WHY THIS EXISTS: `ay maxsat solve` keeps the native MILP-race lane
# (#maxsat-milp-race) ON by default, while the BCE preprocessing lane
# (#maxsat-bce-preprocess) remains opt-in. At `bench --jobs N` (N>1), the
# harness opts out of the extra race thread to avoid oversubscription. The
# actual competition runs ONE instance per machine, where the default race
# thread is free and the campaign config also arms BCE. See
# the development design notes for the configuration rationale.
# Use this wrapper (or pass `--maxsat-bce`) to reproduce the configuration.
# The wrapper only selects it and forwards AY's competition output; it is not
# itself an independent checker.
#
# Usage: maxsat_run.sh <wcnf> [timeout_s=3600] [ay_binary]
#   Emits DIMACS MaxSAT competition output on stdout (o / s / v lines).

WCNF=$1
TMO_S=${2:-3600}
AY=${3:-$(dirname "$0")/../target/release/ay}
if [ -z "$WCNF" ]; then
  echo "usage: maxsat_run.sh <wcnf> [timeout_s=3600] [ay_binary]" >&2
  exit 2
fi

# The verified competition config: OLL engine + default native MILP race +
# explicit BCE lane. One instance per machine makes both lanes appropriate.
exec "$AY" maxsat solve "$WCNF" --timeout "$TMO_S" --maxsat-bce
