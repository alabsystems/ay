#!/bin/zsh
# Nightly wrapper for scripts/corpus_guard.py.
#
# Builds the solver at the current HEAD, re-measures the corpus against the
# committed baseline, and leaves a dated report. Non-zero exit means a shipped
# default has drifted -- see the development design notes for what it drifted
# FROM, and the development design notes for the whole series.
#
# The point of running this on a clock rather than on a commit hook: the
# regressions that actually happened here were not introduced by one commit.
# gt2's 208x node explosion arrived inside a 22,339-line structure-routing merge
# and sat undetected for four days; dcmulti's headline decayed gradually under
# 34 upstream commits. Per-commit gating would not have caught either, because
# nobody runs a 6-minute corpus sweep on every push -- but a nightly does.
#
# It runs TWO gates, because they answer different questions (see the header of
# scripts/corpus_guard.py): the broad banded guard, and the exact node ratchet at
# --tier all. The ratchet also runs pre-push; running it again here is not
# redundant, it is the only lane that sees a merge nobody pushed through the hook.
set -u
REPO="${AY_REPO:-$HOME/ay}"
# The canonical corpus (scripts/milp_gate_corpus.py owns it, .milp_gate_corpus.tsv
# pins it). This used to default to $HOME/ay-corpus, which has never existed on
# this machine -- so the nightly's own SETUP-FAILURE branch below was the only
# thing it could ever have printed.
CORPUS="${AY_CORPUS:-$HOME/ay-bench/milp-gate/instances}"
OUT="$REPO/reports/nightly"
STAMP=$(date -u +%Y-%m-%d)
mkdir -p "$OUT"
LOG="$OUT/$STAMP.log"

{
  print "=== ay-milp nightly corpus guard: $(date -u +%Y-%m-%dT%H:%M:%SZ) ==="
  cd "$REPO" || exit 2
  print "HEAD: $(git rev-parse --short HEAD)  ($(git log -1 --format=%s | cut -c1-72))"

  if [[ ! -d "$CORPUS" ]]; then
    print "SETUP FAILURE: corpus missing at $CORPUS -- guard did not run."
    print "  rebuild it: python3 $REPO/scripts/milp_gate_corpus.py --build"
    exit 2
  fi

  print "\n--- build ---"
  if ! cargo build --release -p ay-milp --example mps_solve 2>&1 | tail -3; then
    print "BUILD FAILED -- guard did not run."
    exit 2
  fi

  print "\n--- corpus manifest ---"
  # sha256 the models BEFORE measuring them. A corpus that has quietly changed
  # under the gate produces numbers that look like a solver regression and are
  # not one; that is a whole night wasted, and it is cheap to exclude.
  python3 "$REPO/scripts/milp_gate_corpus.py" --verify --corpus "$CORPUS"
  mrc=$?

  print "\n--- node ratchet (exact, --tier all) ---"
  python3 "$REPO/scripts/milp_node_gate.py" --check --tier all --corpus "$CORPUS"
  nrc=$?

  print "\n--- corpus guard (banded) ---"
  python3 "$REPO/scripts/corpus_guard.py" --check \
      --corpus "$CORPUS" --limit 120 --short-limit 3 \
      --json "$OUT/$STAMP.json"
  rc=$?

  print "\n--- verdict ---"
  print "corpus manifest: $mrc   node ratchet: $nrc   corpus guard: $rc"
  # WORST WINS, and 2 is worse than 1. A run that could not measure is UNKNOWN,
  # and reporting unknown as either clean or as a regression is how a gate stops
  # being believed.
  worst=0
  for x in $mrc $nrc $rc; do
    if [[ $x -eq 2 ]]; then worst=2; elif [[ $x -eq 1 && $worst -ne 2 ]]; then worst=1; fi
  done
  case $worst in
    0) print "CLEAN -- no shipped default drifted." ;;
    1) print "REGRESSION -- a shipped default drifted. This is the failure mode that"
       print "cost this project four days on gt2 and left rout mislabelled as its"
       print "worst instance while it was beating Gurobi." ;;
    2) print "HARNESS PROBLEM -- a gate could not measure. Treat as unknown, not clean:"
       print "a measurement that silently returns nothing already happened here once." ;;
  esac
  exit $worst
} 2>&1 | tee "$LOG"

exit ${pipestatus[1]}
