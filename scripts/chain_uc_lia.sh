#!/bin/bash
# Hand off the host lease from the SQ QF_Datatypes race to the UC QF_LinearIntArith
# dominant-family race, with no idle gap.
#
# WHY: only one harness run may hold /tmp/ay-oom-guard-$(id -u).lock. The SQ race
# validates AY's only defensible division and must not be preempted. This watcher
# waits for it to FINISH — not merely to release the lock — then starts the race the
# ledger ranks next.
#
# SAFETY: launches ONLY if the SQ race reached all 552 rows. If it died early the
# lock frees too, and starting a 20-hour run on top of a crashed measurement would
# waste the machine and hide the crash. In that case this exits loudly instead.
set -u
cd "$(dirname "$0")/.."
SP="${SP:-$(mktemp -d /tmp/ay-chain-uc-lia.XXXXXX)}"
SQ=evals/results/smtcomp-2025/sq/QF_Datatypes/sq-dt-samemetal/cvc5.jsonl
LOCK=/tmp/ay-oom-guard-$(id -u).lock
DOM="RwMutex-PT-r0010w2000|RwMutex-PT-r0010w1000|RwMutex-PT-r2000w0010|SharedMemory-PT-000100|pb2010"

free=0
echo "[$(date)] watching SQ race: $(wc -l < $SQ)/552"
while :; do
    rows=$(wc -l < "$SQ" 2>/dev/null || echo 0)
    held=$(lsof "$LOCK" >/dev/null 2>&1 && echo yes || echo no)
    if [ "$held" = "no" ]; then
        free=$((free+1))
        # The harness may drop and retake the lease between phases. Require it
        # free on 3 consecutive polls (~4 min) before acting, so a transient
        # release cannot trigger the abort below and lose the automation.
        if [ "$free" -ge 3 ]; then
            echo "[$(date)] lease free on 3 consecutive polls at $rows/552 rows"
            break
        fi
    else
        free=0
    fi
    sleep 120
done

rows=$(wc -l < "$SQ" 2>/dev/null || echo 0)
if [ "$rows" -lt 552 ]; then
    echo "[$(date)] ABORT: SQ race stopped at $rows/552 — it did NOT complete."
    echo "  Not starting UC LIA. Diagnose the SQ run first; it is the more valuable"
    echo "  measurement and a partial result must not be silently replaced."
    exit 1
fi

echo "[$(date)] SQ race COMPLETE (552/552). Scoring it before handing over:"
python3 scripts/smtcomp_harness.py score --track sq --division QF_Datatypes \
    --tag sq-dt-samemetal 2>&1 | tail -20

# PRIORITY 1 (found 2026-07-29): AY's own 61 dominant-family cores are UNVALIDATED.
# `score` reports "validated 0 / unvalidated 61 ... unvalidated cores score 0", so
# AY's dominant-family contribution is currently ZERO, not 2,344,044 — the claimed
# 4,267,796 is unbacked on 67.2% of its mass. Validating AY matters MORE than racing
# yices2: without it AY scores 0 whatever yices2 does.
echo "[$(date)] PRIORITY 1: validating AY's 61 dominant-family cores"
python3 scripts/smtcomp_harness.py validate-uc --division QF_LinearIntArith \
    --tag uc-lia-ay-full1200
python3 scripts/smtcomp_harness.py score --track uc --division QF_LinearIntArith \
    --tag uc-lia-ay-full1200 2>&1 | tail -12

echo "[$(date)] starting UC QF_LinearIntArith dominant-family race (yices2)"
echo "  67 instances = 67.2% of the division score; AY arm already on disk"
echo "  (uc-lia-ay-full1200). yices2 = $(/opt/homebrew/bin/yices-smt2 --version | head -1)"
python3 scripts/smtcomp_harness.py run --track uc --division QF_LinearIntArith \
    --solvers yices2 --timeout 1200 --jobs 3 --only "$DOM" --tag uc-lia-yices-dominant
python3 scripts/smtcomp_harness.py validate-uc --division QF_LinearIntArith \
    --tag uc-lia-yices-dominant
python3 scripts/smtcomp_harness.py score --track uc --division QF_LinearIntArith \
    --tag uc-lia-yices-dominant
echo "[$(date)] UC LIA dominant-family race DONE"

# ---------------------------------------------------------------------------
# PHASE 3: the CLEARSY differential that gates AY_EUF_BOOL_ARG_REPAIR.
#
# Deferred to here ON PURPOSE: it must run on a QUIET machine. Running it beside
# a scored race depresses the competitor's wall-clock solve count and biases the
# race (see SQ_QF_DATATYPES_NEEDS_THE_RACE.md, contention caveat).
#
# The corpus is now on disk (Zenodo 15493096, incremental QF_UF), 491 CLEARSY
# instances are in the official Inc QF_Equality selection.
echo "[$(date)] PHASE 3: CLEARSY differential for AY_EUF_BOOL_ARG_REPAIR"
AY="${AY:-$SP/ay_repair}"
ROOT="$(pwd)/benchmarks/smt-lib-incremental"
SEL="${SEL:-$SP/clearsy_sel.txt}"
off_unk=0; on_unk=0; off_sat=0; on_sat=0; off_uns=0; on_uns=0; n=0; contra=0
while read rel; do
    f="$ROOT/$rel"; [ -f "$f" ] || continue; n=$((n+1))
    # ONE invocation per arm. (Counting each verdict with its own run cost 6
    # invocations per file — ~16 h over 491 files instead of ~5 h.)
    OA=$("$AY" --z3-mode --incremental -T:20 "$f" 2>/dev/null)
    OB=$(AY_EUF_BOOL_ARG_REPAIR=1 "$AY" --z3-mode --incremental -T:20 "$f" 2>/dev/null)
    a=$(printf '%s\n' "$OA" | grep -cE '^unknown$'); as=$(printf '%s\n' "$OA" | grep -cE '^sat$'); au=$(printf '%s\n' "$OA" | grep -cE '^unsat$')
    b=$(printf '%s\n' "$OB" | grep -cE '^unknown$'); bs=$(printf '%s\n' "$OB" | grep -cE '^sat$'); bu=$(printf '%s\n' "$OB" | grep -cE '^unsat$')
    off_unk=$((off_unk+a)); on_unk=$((on_unk+b))
    off_sat=$((off_sat+as)); on_sat=$((on_sat+bs))
    off_uns=$((off_uns+au)); on_uns=$((on_uns+bu))
    # A sat<->unsat swing on the same file is a soundness alarm, not a win.
    # ANY unsat-count change is the alarm on its own — requiring sat to change
    # too would hide the exact case that matters.
    if [ "$au" -ne "$bu" ]; then
        contra=$((contra+1)); echo "  !! CHECK $rel off(s=$as,u=$au) on(s=$bs,u=$bu)"
    fi
done < "$SEL"
echo "[$(date)] CLEARSY differential over $n files"
echo "  unknown : OFF=$off_unk  ON=$on_unk   (delta $((on_unk-off_unk)); NEGATIVE = repair helps)"
echo "  sat     : OFF=$off_sat  ON=$on_sat"
echo "  unsat   : OFF=$off_uns  ON=$on_uns   (must be equal — any change is a SOUNDNESS alarm)"
echo "  suspicious files: $contra"
echo "  DECISION: flip the default ON only if unknown DROPS, unsat is UNCHANGED,"
echo "            and no completeness collapse (the naive lemma went 121 -> ~50)."

# ---------------------------------------------------------------------------
# PHASE 4: regenerate UC QF_Datatypes from MAIN.
#
# audit_claims.py reports "NO AY EVIDENCE ON DISK" for this division — the
# results tree holds only cvc5 tags. The committed win-evidence says regeneration
# needs the `uc-wiring-package` branch binary, but that is STALE: 7748875f8
# (the merge of that branch) is an ancestor of HEAD, so main already contains the
# wiring. Regenerating from main is therefore both possible AND better — it
# verifies the code that actually ships, not a side branch.
#
# This is the campaign's strongest claim by substance (4,550,583 VALIDATED
# reduction, 3.54x cvc5, 0 invalidated, z3 cross-checked) and the only one with
# no on-disk evidence at all. Making it reproducible is worth more than any
# engine tweak currently available.
echo "[$(date)] PHASE 4: regenerate UC QF_Datatypes from main (400 instances)"
python3 scripts/smtcomp_harness.py run --track uc --division QF_Datatypes \
    --solvers ay --timeout 1200 --jobs 3 --tag uc-dt-frommain
python3 scripts/smtcomp_harness.py validate-uc --division QF_Datatypes \
    --tag uc-dt-frommain
python3 scripts/smtcomp_harness.py score --track uc --division QF_Datatypes \
    --tag uc-dt-frommain 2>&1 | tail -15

echo "[$(date)] FINAL: re-running the claim audit against everything produced"
python3 scripts/audit_claims.py
echo "[$(date)] CHAIN COMPLETE"
