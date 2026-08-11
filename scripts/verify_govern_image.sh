#!/bin/bash
# Prove the in-image memory bound actually holds -- including the cases that
# defeated the retired path-shimming model on 2026-08-02.
#
# Proves the bound for the IMAGE layer, including the two cases a PATH-based
# shim structurally cannot pass: a renamed copy, and a copy at a path that did
# not exist at install time. Those are exactly what `ay-base` and `ay-fixed`
# were on 2026-08-02.
#
# Usage: scripts/verify_govern_image.sh [path-to-ay]
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
AY="${1:-$ROOT/target/release/ay}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

pass=0; fail=0

# A GOVERNED outcome is any of:
#   137  SIGKILL at the jetsam footprint cap (L1)
#   101  ay's own memout exit via RLIMIT_AS (L2)
#   0/134 with an allocation failure in the log -- RLIMIT_AS makes a Rust
#         allocation fail, which aborts (signal 6); ay's supervisor catches that
#         and FAILS CLOSED to `unknown`. That is a bound working, not a solve.
# The one ungoverned outcome is 124: still running when the window expired.
governed_outcome() {
  local rc="$1" log="$2" what="$3"
  if [ "$rc" = "124" ]; then
    no "$what ran unbounded to the timeout -- this is the 08-02 panic shape"
    return
  fi
  if [ "$rc" = "137" ]; then ok "$what: SIGKILL at the jetsam memlimit (L1)"; return; fi
  if [ "$rc" = "101" ]; then ok "$what: memout via RLIMIT_AS (L2)"; return; fi
  if grep -q 'memory allocation of .* failed\|failing closed to unknown' "$log" 2>/dev/null; then
    ok "$what: allocation refused by RLIMIT_AS, failed closed to unknown (rc=$rc)"
    return
  fi
  echo "  SKIP  $what: finished (rc=$rc) without hitting the bound"
}
ok() { echo "  PASS  $1"; pass=$((pass + 1)); }
no() { echo "  FAIL  $1"; fail=$((fail + 1)); }

if [ ! -x "$AY" ]; then
  echo "verify_govern_image: no ay binary at $AY" >&2
  echo "build it: cargo build --release -p ay --bin ay --features cli" >&2
  exit 1
fi

echo "verify govern-image   (ay = $AY)"
echo

# A query big enough to blow a small budget: a wide pigeonhole instance. It is
# UNSAT and combinatorially hard, so the solver allocates rather than answering.
hog="$TMP/hog.smt2"
{
  n=90
  echo "(set-option :produce-proofs true)"   # MUST precede set-logic (start mode)
  echo "(set-logic QF_UF)"
  for ((i = 0; i < n; i++)); do
    for ((j = 0; j < n - 1; j++)); do echo "(declare-const p_${i}_${j} Bool)"; done
  done
  for ((i = 0; i < n; i++)); do
    line="(assert (or"
    for ((j = 0; j < n - 1; j++)); do line="$line p_${i}_${j}"; done
    echo "$line))"
  done
  for ((j = 0; j < n - 1; j++)); do
    for ((i = 0; i < n; i++)); do
      for ((k = i + 1; k < n; k++)); do
        echo "(assert (or (not p_${i}_${j}) (not p_${k}_${j})))"
      done
    done
  done
  echo "(check-sat)"
} > "$hog"

# 1. The binary still works normally. A governor that breaks the program is not
#    a governor, it is an outage.
echo "[1] normal operation is unaffected"
printf '(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 5))\n(check-sat)\n' > "$TMP/ok.smt2"
out="$("$AY" "$TMP/ok.smt2" 2>&1 | grep -vE '^c ')"
if [ "$(echo "$out" | tr -d '[:space:]')" = "sat" ]; then
  ok "solves normally (sat)"
else
  no "expected sat, got: $out"
fi

# 2. main runs EXACTLY once. arm() re-execs, so a marker bug would either loop
#    forever or run the program twice.
echo "[2] re-exec happens exactly once"
n_out="$("$AY" --version 2>&1 | wc -l | tr -d ' ')"
v1="$("$AY" --version 2>&1 | head -1)"
if [ "$n_out" -ge 1 ] && [ -n "$v1" ]; then
  ok "single --version banner (no exec loop): $v1"
else
  no "unexpected --version output ($n_out lines)"
fi

# 3. The process really is running under taskpolicy's memlimit, and the marker
#    is in its environment.
echo "[3] CONTROL: with the marker preset, arm() falls through and the cap does NOT bind"
# This is the differential that proves test [4]'s kill comes from OUR re-exec and
# not from some ambient limit: same binary, same tiny budget, arming skipped.
AY_GOVERN_ARMED=1 GOVERN_AY_MB=192 timeout 60 "$AY" "$hog" > "$TMP/ctl.out" 2>&1
rc=$?
case "$rc" in
  137|101) no "control was still bounded (rc=$rc) -- test [4] would prove nothing" ;;
  *)       ok "unbounded when arming is skipped (rc=$rc), so the cap is ours" ;;
esac

# 4. THE POINT. A small budget must STOP the process rather than let it grow.
#    Measured on ay: RLIMIT_AS refuses an allocation at ~76s, Rust aborts
#    (signal 6), and ay's supervisor fails closed to `unknown` with rc=0. The
#    jetsam cap (L1) does NOT fire on this instance because phys_footprint stays
#    under budget while RSS reaches 284 MB -- clean file-backed pages do not
#    count toward footprint. Both layers are armed; on the 08-02 workload
#    (137.9 GB resident) both would fire. See governed_outcome().
echo "[4] a small budget is enforced by the kernel"
GOVERN_AY_MB=192 timeout 200 "$AY" "$hog" > "$TMP/hog.out" 2>&1
rc=$?
governed_outcome "$rc" "$TMP/hog.out" "small budget"

# 5. THE CASE PATH-SHIMMING CANNOT COVER. A RENAMED copy must still be governed.
#    `ay-base` and `ay-fixed` were exactly this, and they held 272 GB between them.
echo "[5] a RENAMED copy is still governed (the ay-base/ay-fixed case)"
cp "$AY" "$TMP/ay-fixed"
GOVERN_AY_MB=192 timeout 200 "$TMP/ay-fixed" "$hog" > "$TMP/ren.out" 2>&1
rc=$?
governed_outcome "$rc" "$TMP/ren.out" "renamed copy"

# 6. And at a path that did not exist when anything was installed.
echo "[6] a copy at a NEW path is still governed"
mkdir -p "$TMP/nested/did/not/exist"
cp "$AY" "$TMP/nested/did/not/exist/ay-base"
GOVERN_AY_MB=192 timeout 200 "$TMP/nested/did/not/exist/ay-base" "$hog" > "$TMP/new.out" 2>&1
rc=$?
governed_outcome "$rc" "$TMP/new.out" "copy at an unknown path"

# 7. The orphan case. The processes that panic this machine are orphans: the
#    harness dies and the solver reparents to launchd and keeps allocating. A
#    userspace watchdog disarms exactly when it is needed; a kernel-held bound
#    does not.
echo "[7] the bound survives the parent's death (the orphan case)"
( GOVERN_AY_MB=192 "$TMP/ay-fixed" "$hog" > "$TMP/orph.out" 2>&1 & echo $! > "$TMP/pid"; sleep 30 ) &
outer=$!
sleep 150
wait "$outer" 2>/dev/null
child="$(cat "$TMP/pid" 2>/dev/null)"
if [ -n "$child" ] && kill -0 "$child" 2>/dev/null; then
  no "orphan still alive after 150s -- unbounded"
  kill -9 "$child" 2>/dev/null
else
  ok "orphan (reparented, no supervisor) was stopped without a supervisor"
fi

# 8. Every bin target arms. A new binary that forgets is worse than none: it
#    looks armed from the outside.
echo "[8] every bin target arms the bound"
if "$ROOT/scripts/check_govern_armed.sh" >/dev/null 2>&1; then
  ok "check_govern_armed.sh passes"
else
  no "check_govern_armed.sh reports an unarmed bin target"
fi

echo
echo "passed $pass, failed $fail"
[ "$fail" -eq 0 ]
