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
# It runs THREE gates, because they answer different questions (see the header of
# scripts/corpus_guard.py): the broad banded guard, the exact node ratchet at
# --tier all, and the exact-rim ratchet. The node ratchet also runs pre-push;
# running it again here is not redundant, it is the only lane that sees a merge
# nobody pushed through the hook.
#
# WHY THE RIM RATCHET IS HERE AND NOT IN THE PRE-PUSH HOOK. The first two gates
# BOTH pass, clean, on a change measured at 4.9x on dcmulti and 3.45x on qnet1,
# because both drive the float-first MILP lane and that lane enters `exact::`
# about once per 1.36M nodes -- so until the Rust `milp_rim_gate` existed,
# nothing under crates/ay-milp/src/exact/ was watched at all. It is nightly-only
# for a cost reason and states it plainly: it measures through the #[cfg(test)]
# probe, so it needs a `cargo test --no-run` build of the ay-milp lib (minutes
# cold) on top of the example build the other two share. `--tier fast` (17s, 10
# instances) is affordable pre-push if that build is already warm; --tier all
# (105s, adds qiu) belongs here.
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
  if ! cargo build --release -p ay-milp \
      --example mps_solve --example milp_rim_gate 2>&1 | tail -3; then
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

  print "\n--- exact-rim ratchet (switch point / pivots / exact optimum, --tier all) ---"
  # The probe is #[cfg(test)], so this needs the lib TEST binary rather than the
  # example the two gates above share. Built here, not inside the gate, for the
  # same reason the example is: a gate that cannot build is UNKNOWN (2), never
  # clean, and the compile's own load average must not be the thing that makes
  # the quiet-box precondition refuse.
  # NOT `if ! cargo ... | tail -3`: a pipeline's status is its LAST command's, so
  # that form is always tail's 0 and the failure branch below could never run --
  # a build-failure branch that cannot fire is the dead gate this file argues
  # against. zsh's $pipestatus keeps the compiler's own status.
  cargo test -p ay-milp --release --lib --no-run 2>&1 | tail -3
  if [[ ${pipestatus[1]} -ne 0 ]]; then
    print "RIM PROBE BUILD FAILED -- the rim ratchet did not run."
    rrc=2
  else
    # Cargo may place artifacts outside the repository, but this is still an
    # exact path rather than a target/ glob: CARGO_TARGET_DIR is Cargo's own
    # selected root and the example target name is fixed in the manifest.
    RIM_TARGET="${CARGO_TARGET_DIR:-$REPO/target}"
    if [[ "$RIM_TARGET" != /* ]]; then RIM_TARGET="$REPO/$RIM_TARGET"; fi
    "$RIM_TARGET/release/examples/milp_rim_gate" \
        --check --tier all --corpus "$CORPUS"
    rrc=$?
  fi

  print "\n--- verdict ---"
  print "corpus manifest: $mrc   node ratchet: $nrc   corpus guard: $rc   rim ratchet: $rrc"
  # WORST WINS, and 2 is worse than 1. A run that could not measure is UNKNOWN,
  # and reporting unknown as either clean or as a regression is how a gate stops
  # being believed.
  worst=0
  for x in $mrc $nrc $rc $rrc; do
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
