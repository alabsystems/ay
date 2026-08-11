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
set -u
REPO="${AY_REPO:-$HOME/ay}"
CORPUS="${AY_CORPUS:-$HOME/ay-corpus}"
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
    exit 2
  fi

  print "\n--- build ---"
  if ! cargo build --release -p ay-milp --example mps_solve 2>&1 | tail -3; then
    print "BUILD FAILED -- guard did not run."
    exit 2
  fi

  print "\n--- corpus guard ---"
  python3 "$REPO/scripts/corpus_guard.py" --check \
      --corpus "$CORPUS" --limit 120 --short-limit 3 \
      --json "$OUT/$STAMP.json"
  rc=$?

  print "\n--- verdict ---"
  case $rc in
    0) print "CLEAN -- no shipped default drifted." ;;
    1) print "REGRESSION -- a shipped default drifted. This is the failure mode that"
       print "cost this project four days on gt2 and left rout mislabelled as its"
       print "worst instance while it was beating Gurobi." ;;
    2) print "HARNESS PROBLEM -- the guard could not measure. Treat as unknown, not clean:"
       print "a measurement that silently returns nothing already happened here once." ;;
  esac
  exit $rc
} 2>&1 | tee "$LOG"

exit ${pipestatus[1]}
