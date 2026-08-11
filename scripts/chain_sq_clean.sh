#!/bin/bash
# The clean SQ QF_Datatypes race — the measurement that actually settles the
# campaign's only defensibility-standard claim.
#
# WHY A SECOND RUN IS NEEDED. `sq-dt-samemetal` finished AY 395 vs cvc5 385, and it
# does NOT settle anything:
#   1. the harness REFUSES to score it ("corpus variants=2");
#   2. that tag holds only 106 AY rows — AY's 395 comes from
#      win-evidence/sq-ay-fullbudget.jsonl, dated Jul 15, two weeks and many commits
#      before the Jul 29 cvc5 arm;
#   3. AY's evidence records NO run conditions (answer/expected/instance/wall_sec
#      only) — no timeout, memlimit, binary hash or run identity;
#   4. cvc5's arm ran under concurrent local load, so 385 is a LOWER bound, and a
#      +10 margin is 1.8% of 552 — inside this host's documented 15-47% swing.
#
# THE FIX, and the only thing that settles it: BOTH solvers in ONE invocation, one
# tag, one quiet machine, the CURRENT binary. Then identical load, identical corpus
# snapshot, and harness provenance on every row — which is what makes `score` accept
# the comparison at all.
#
# Waits for the UC/CLEARSY chain to finish first: nothing else may run beside a
# scored race, which is the mistake that invalidated the last one.
set -u
cd "$(dirname "$0")/.."
LOCK=/tmp/ay-oom-guard-$(id -u).lock

echo "[$(date)] waiting for the UC chain to release the machine"
free=0
while :; do
    if pgrep -f chain_uc_lia.sh >/dev/null 2>&1; then
        free=0
    elif lsof "$LOCK" >/dev/null 2>&1; then
        free=0
    else
        free=$((free+1))
        # Three consecutive clear polls (~6 min): the harness drops and retakes the
        # lease between phases, and a transient gap must not start a race beside it.
        [ "$free" -ge 3 ] && break
    fi
    sleep 120
done
echo "[$(date)] machine is quiet — starting the clean SQ race"

# Freeze the binary so a later `cargo build` cannot change arms mid-run, and so the
# tag records one binary hash for both solvers' comparability check.
AY_FROZEN=/tmp/ay_sq_clean_$$
cp target/release/ay "$AY_FROZEN" || exit 1
export AY_BIN="$AY_FROZEN"
echo "[$(date)] AY_BIN frozen: $AY_FROZEN ($(md5 -q "$AY_FROZEN" 2>/dev/null || echo '?'))"

python3 scripts/smtcomp_harness.py run --track sq --division QF_Datatypes \
    --solvers ay,cvc5 --timeout 1200 --jobs 3 --tag sq-dt-clean --overwrite
echo "[$(date)] scoring — this must SUCCEED, unlike sq-dt-samemetal"
python3 scripts/smtcomp_harness.py score --track sq --division QF_Datatypes \
    --tag sq-dt-clean 2>&1 | tail -25

echo "[$(date)] re-auditing every claim against the new evidence"
python3 scripts/audit_claims.py
rm -f "$AY_FROZEN"
echo "[$(date)] CLEAN SQ RACE COMPLETE"
