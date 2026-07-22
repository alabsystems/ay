#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates
#
# Firewall self-cert smoke check.
#
# Proves, end-to-end, that `ay --verify-firewall` is a real verified self-cert
# gate: for one UNSAT per firewall-covered theory, AY reconstructs a per-theory
# "firewall" Lean proof and kernel-checks it with the real Lean toolchain
# (`lake env lean` inside verification/lean, grounded in the machine-verified
# AySoundness.firewall_combined_unsat theorem). It also proves the checker has
# teeth: a corrupted firewall is REJECTED by the Lean kernel (so a bad proof
# could never be silently accepted -> the gate downgrades unsat to unknown).
#
# Usage:
#   ./scripts/firewall-selfcert-check.sh
#
# Exit codes:
#   0  all theories self-certified AND a corrupted firewall was rejected
#   0  SKIP: the Lean toolchain (`lake`) is unavailable (no-op in CI without Lean)
#   1  a theory failed to self-certify, or a corrupt firewall was accepted

set -o pipefail
set -o nounset

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd -P)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." >/dev/null 2>&1 && pwd -P)"
AY_BIN="${AY_BIN:-$REPO_ROOT/target/release/ay}"
LEAN_PROJECT="$REPO_ROOT/verification/lean"

# Locate lake the same way the ay binary does (PATH, then elan shim).
LAKE="lake"
if ! command -v "$LAKE" >/dev/null 2>&1; then
  if [[ -x "$HOME/.elan/bin/lake" ]]; then
    LAKE="$HOME/.elan/bin/lake"
  else
    echo "firewall-selfcert-check: SKIP — 'lake' (Lean toolchain) not found" >&2
    exit 0
  fi
fi

if [[ ! -x "$AY_BIN" ]]; then
  echo "firewall-selfcert-check: building ay (release) ..." >&2
  ( cd "$REPO_ROOT" && cargo build --release --bin ay --features cli ) || exit 1
fi

WORK="$(mktemp -d "${TMPDIR:-/tmp}/ay-firewall-smoke.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

fail=0

# --- One UNSAT per firewall-covered theory ------------------------------------
# Each of these produces at least one kernel-checkable firewall lemma.

emit_case() {
  # $1 = name, $2 = smt2 body (stdin heredoc via caller)
  cat > "$WORK/$1.smt2"
}

cat > "$WORK/datatype.smt2" <<'EOF'
(set-logic QF_DT)
(declare-datatype Color ((red) (green) (blue)))
(declare-const c Color)
(assert (= c red))
(assert (= c green))
(check-sat)
EOF

cat > "$WORK/lia.smt2" <<'EOF'
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 5))
(assert (< x 3))
(check-sat)
EOF

cat > "$WORK/euf.smt2" <<'EOF'
(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(assert (= a b))
(assert (= b c))
(assert (not (= a c)))
(check-sat)
EOF

cat > "$WORK/congruence.smt2" <<'EOF'
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const a U)
(declare-const b U)
(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)
EOF

cat > "$WORK/array_row2.smt2" <<'EOF'
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const v Int)
(assert (not (= i j)))
(assert (not (= (select (store a i v) j) (select a j))))
(check-sat)
EOF

for name in datatype lia euf congruence array_row2; do
  out="$("$AY_BIN" "$WORK/$name.smt2" --verify-firewall 2>"$WORK/$name.err" | grep -vE '^c ')"
  verdict="$(echo "$out" | tr -d '[:space:]')"
  if [[ "$verdict" == "unsat" ]] && grep -q "self-cert PASS" "$WORK/$name.err"; then
    echo "firewall-selfcert-check: $name  PASS (unsat, kernel-checked)"
  else
    echo "firewall-selfcert-check: $name  FAIL — verdict='$verdict'" >&2
    sed 's/^/    /' "$WORK/$name.err" >&2
    fail=1
  fi
done

# --- The checker has teeth: a corrupted firewall must be REJECTED -------------
# Emit a real datatype firewall, corrupt its RUP proof, and confirm the Lean
# kernel rejects it. (This is exactly what makes the runtime FAIL->unknown
# downgrade meaningful — a bad proof cannot slip through.)
mkdir -p "$WORK/lean"
"$AY_BIN" "$WORK/datatype.smt2" --proof "$WORK/dt.alethe" \
  --emit-firewall-lean "$WORK/lean" >/dev/null 2>&1
FW="$WORK/lean/firewall_0.lean"
if [[ ! -f "$FW" ]]; then
  echo "firewall-selfcert-check: corruption-test FAIL — no firewall was emitted" >&2
  fail=1
else
  # Drop a clause id from the RUP proof antecedents so lratCheck no longer closes.
  sed 's/\[1, 2, 3\]/[1, 2]/' "$FW" > "$WORK/lean/corrupt.lean"
  if ( cd "$LEAN_PROJECT" && "$LAKE" env lean "$WORK/lean/corrupt.lean" ) >/dev/null 2>&1; then
    echo "firewall-selfcert-check: corruption-test FAIL — Lean ACCEPTED a corrupt firewall" >&2
    fail=1
  else
    echo "firewall-selfcert-check: corruption-test PASS (Lean rejected the corrupt firewall)"
  fi
fi

if [[ "$fail" -eq 0 ]]; then
  echo "firewall-selfcert-check: ALL PASS"
else
  echo "firewall-selfcert-check: FAILURES present" >&2
fi
exit "$fail"
