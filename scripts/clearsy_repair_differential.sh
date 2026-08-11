#!/bin/bash
# CORRECTED CLEARSY differential for AY_EUF_BOOL_ARG_REPAIR.
#
# The first attempt (chain_uc_lia.sh phase 3) was INVALID: it passed the file as an
# ARGUMENT alongside --incremental. AY rejects that combination outright —
#   "Error: a FILE argument cannot be combined with --stdin or --incremental"
# — exiting rc=1 with no verdicts, so 490 files "completed" in 9 seconds and every
# counter read 0. That looked exactly like "the repair changes nothing". It measured
# nothing. --incremental READS FROM STDIN; the file must be redirected.
#
# Spot-check with the correct invocation, on the first selected file:
#     OFF: 41 sat / 34 unsat / 1 unknown
#     ON : 42 sat / 34 unsat / 0 unknown
# i.e. one unknown converted to sat with unsat UNCHANGED — the repair works.
#
# Waits for the machine, because a benchmark beside a scored race is what
# invalidated the SQ race earlier.
set -u
cd "$(dirname "$0")/.."
SP="${SP:-$(mktemp -d /tmp/ay-clearsy-repair.XXXXXX)}"
LOCK=/tmp/ay-oom-guard-$(id -u).lock
AY=./target/release/ay
ROOT=benchmarks/smt-lib-incremental
SEL=$SP/clearsy_sel.txt

echo "[$(date)] waiting for the machine (chains + lease)"
free=0
while :; do
    if pgrep -f "chain_uc_lia.sh|chain_sq_clean.sh" >/dev/null 2>&1 || lsof "$LOCK" >/dev/null 2>&1; then
        free=0
    else
        free=$((free+1)); [ "$free" -ge 3 ] && break
    fi
    sleep 120
done
echo "[$(date)] machine quiet — running the CORRECTED differential"

off_u=0; on_u=0; off_s=0; on_s=0; off_n=0; on_n=0; n=0; alarm=0
while read -r rel; do
    f="$ROOT/$rel"; [ -f "$f" ] || continue; n=$((n+1))
    OA=$("$AY" --z3-mode --incremental -T:20 < "$f" 2>/dev/null)
    OB=$(AY_EUF_BOOL_ARG_REPAIR=1 "$AY" --z3-mode --incremental -T:20 < "$f" 2>/dev/null)
    au=$(printf '%s\n' "$OA" | grep -cE '^unsat$'); as=$(printf '%s\n' "$OA" | grep -cE '^sat$'); an=$(printf '%s\n' "$OA" | grep -cE '^unknown$')
    bu=$(printf '%s\n' "$OB" | grep -cE '^unsat$'); bs=$(printf '%s\n' "$OB" | grep -cE '^sat$'); bn=$(printf '%s\n' "$OB" | grep -cE '^unknown$')
    off_u=$((off_u+au)); on_u=$((on_u+bu)); off_s=$((off_s+as)); on_s=$((on_s+bs)); off_n=$((off_n+an)); on_n=$((on_n+bn))
    # ANY unsat-count change is a soundness alarm on its own.
    if [ "$au" -ne "$bu" ]; then alarm=$((alarm+1)); echo "  !! UNSAT CHANGED $rel  off=$au on=$bu"; fi
    [ $((n % 50)) -eq 0 ] && echo "  $n files: unknown OFF=$off_n ON=$on_n"
done < "$SEL"

echo "[$(date)] CORRECTED CLEARSY differential over $n files"
echo "  unknown : OFF=$off_n  ON=$on_n   (delta $((on_n-off_n)); NEGATIVE = repair helps)"
echo "  sat     : OFF=$off_s  ON=$on_s"
echo "  unsat   : OFF=$off_u  ON=$on_u   (MUST be equal)"
echo "  soundness alarms (unsat count changed): $alarm"
if [ "$alarm" -eq 0 ] && [ "$on_n" -lt "$off_n" ] && [ "$off_u" -eq "$on_u" ]; then
    echo "  VERDICT: repair HELPS with unsat unchanged — flip AY_EUF_BOOL_ARG_REPAIR default ON"
else
    echo "  VERDICT: do NOT flip (no gain, or an unsat count moved)"
fi
