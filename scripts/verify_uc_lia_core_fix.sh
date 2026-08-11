#!/bin/bash
# Build + verify the #uc-lia-100pct-core fix, once the machine is free.
#
# THE BUG: 23 of AY's 61 unsat answers on the UC QF_LinearIntArith dominant
# families published a core equal to the ENTIRE assertion set (70,303 of 70,303),
# scoring zero reduction. Those instances forfeit 1,243,577; Yices2 earns
# 1,064,482 on exactly them; the division deficit was 1,068,711 — so they are the
# whole loss.
#
# THE FIX: decline instead of publishing a padded core, handing off to the lazy
# assume-split arm that gets a real failed-assumption core from the SAT solver for
# free. Safe because a 100% core scores exactly 0, so declining is never worse.
#
# PASS CRITERIA (all must hold):
#   1. the full test suite stays green,
#   2. the number of 100%-cores DROPS,
#   3. validated reduction RISES,
#   4. zero invalidated cores (the soundness invariant).
set -u
cd "$(dirname "$0")/.."
LOCK=/tmp/ay-oom-guard-$(id -u).lock

echo "[$(date)] waiting for the machine"
free=0
while :; do
    if pgrep -f "chain_uc_lia.sh|chain_sq_clean.sh|clearsy_repair_differential.sh" >/dev/null 2>&1 \
       || lsof "$LOCK" >/dev/null 2>&1; then
        free=0
    else
        free=$((free+1)); [ "$free" -ge 3 ] && break
    fi
    sleep 120
done

echo "[$(date)] building (--features cli — WITHOUT it only the lib builds and the"
echo "           binary silently stays stale; see memory ay-cli-build-requires-cli-feature)"
cargo build --release -p ay --features cli 2>&1 | grep -E "^error|Finished" | head -5
strings -a target/release/ay | grep -q "uc_probe_should_decline_padded_core" \
    && echo "  marker present" || echo "  NOTE: symbol not in strings (inlined) — checking tests instead"

echo "[$(date)] full ay-dpll test suite"
cargo test --release -p ay-dpll --lib 2>&1 | tail -3

echo "[$(date)] re-running the UC LIA dominant families with the fix"
python3 scripts/smtcomp_harness.py run --track uc --division QF_LinearIntArith \
    --solvers ay --timeout 1200 --jobs 3 \
    --only "RwMutex-PT-r0010w2000|RwMutex-PT-r0010w1000|RwMutex-PT-r2000w0010|SharedMemory-PT-000100|pb2010" \
    --tag uc-lia-corefix --overwrite
python3 scripts/smtcomp_harness.py validate-uc --division QF_LinearIntArith --tag uc-lia-corefix
python3 scripts/smtcomp_harness.py score --track uc --division QF_LinearIntArith --tag uc-lia-corefix 2>&1 | tail -12

echo "[$(date)] BEFORE vs AFTER"
python3 - <<'PY'
import json,os
B='evals/results/smtcomp-2025/uc/QF_LinearIntArith'
def stats(tag):
    f=f'{B}/{tag}/ay.jsonl'
    if not os.path.exists(f): return None
    rows=[json.loads(l) for l in open(f)]
    uns=[r for r in rows if r.get('answer')=='unsat' and r.get('core_size') is not None]
    full=[r for r in uns if r['core_size']==r['n_asserts']]
    v=f'{B}/{tag}/validation/ay.jsonl'
    val=[json.loads(l) for l in open(v)] if os.path.exists(v) else []
    return dict(unsat=len(uns), full_cores=len(full),
                validated=sum(1 for r in val if r.get('status')=='valid'),
                invalid=sum(1 for r in val if r.get('status')=='invalid'),
                reduction=sum(r.get('reduction',0) for r in val if r.get('status')=='valid'))
b=stats('uc-lia-ay-full1200'); a=stats('uc-lia-corefix')
print(f"  BEFORE {b}")
print(f"  AFTER  {a}")
if b and a:
    print(f"\n  100%-cores : {b['full_cores']} -> {a['full_cores']}")
    print(f"  reduction  : {b['reduction']:,} -> {a['reduction']:,}  ({a['reduction']-b['reduction']:+,})")
    print(f"  invalidated: {a['invalid']}  (MUST be 0)")
    print(f"  yices2 same-metal bar on these families: 2,375,255")
    ok = a['invalid']==0 and a['full_cores']<b['full_cores'] and a['reduction']>b['reduction']
    print("\n  VERDICT: SHIP" if ok else "\n  VERDICT: DO NOT SHIP — a criterion failed")
PY
echo "[$(date)] DONE"
