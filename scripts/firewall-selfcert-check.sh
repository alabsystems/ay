#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates
#
# Firewall diagnostic smoke check.
#
# Exercises, end-to-end, the diagnostic side of `ay --verify-firewall`: for one
# internally-UNSAT case per covered theory, AY reconstructs a local firewall
# artifact and kernel-checks it with the real Lean toolchain. These artifacts are
# not independently bound to the complete frontend query, so the required public
# verdict is `unknown` even when every local artifact passes. The corruption test
# separately confirms that Lean rejects a damaged local artifact.
#
# Usage:
#   ./scripts/firewall-selfcert-check.sh
#
# Exit codes:
#   0  all local diagnostics passed, every verdict stayed unknown, and a
#      corrupted local artifact was rejected (this does NOT certify any query)
#   0  SKIP: the Lean toolchain (`lake`) is unavailable (no-op in CI without Lean)
#   1  a local diagnostic failed, a verdict escaped as sat/unsat, or a corrupt
#      artifact was accepted

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

if ! ( cd "$LEAN_PROJECT" && "$LAKE" build +AySoundness.Firewall ); then
  echo "firewall-selfcert-check: FAIL — Lean verifier modules did not build" >&2
  exit 1
fi

WORK="$(mktemp -d "${TMPDIR:-/tmp}/ay-firewall-smoke.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

fail=0

diagnostics_all_passed() {
  local error_file="$1"
  local counts passed total
  counts="$(sed -nE \
    's/.*firewall diagnostic complete — ([0-9]+)\/([0-9]+) artifact.*/\1 \2/p' \
    "$error_file" | tail -n 1)"
  [[ -n "$counts" ]] || return 1
  read -r passed total <<<"$counts"
  [[ "$total" -gt 0 && "$passed" == "$total" ]] \
    && ! grep -Eq 'firewall diagnostic #[0-9]+ FAIL' "$error_file"
}

# --- One internally-UNSAT case per firewall-covered theory --------------------
# Each produces at least one kernel-checkable local diagnostic artifact. Because
# no artifact binds itself to the whole query, `--verify-firewall` must publish
# `unknown`, never the solver's internal `unsat`.

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

cat > "$WORK/array_nested.smt2" <<'EOF'
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const r Int)
(declare-const i Int)
(declare-const j Int)
(declare-const v1 Int)
(declare-const v2 Int)
(assert (not (= r i)))
(assert (not (= r j)))
(assert (not (= (select (store (store a i v1) j v2) r) (select a r))))
(check-sat)
EOF

for name in datatype lia euf congruence array_row2 array_nested; do
  out="$("$AY_BIN" "$WORK/$name.smt2" --verify-firewall 2>"$WORK/$name.err" | grep -vE '^c ')"
  verdict="$(echo "$out" | tr -d '[:space:]')"
  if [[ "$verdict" == "unknown" ]] \
    && grep -Eq "firewall diagnostic #[0-9]+ PASS" "$WORK/$name.err" \
    && diagnostics_all_passed "$WORK/$name.err" \
    && grep -q "artifacts do not certify the query; reporting unknown" "$WORK/$name.err"; then
    echo "firewall-selfcert-check: $name  PASS (local artifact checked; query remained unknown)"
  else
    echo "firewall-selfcert-check: $name  FAIL — verdict='$verdict'" >&2
    sed 's/^/    /' "$WORK/$name.err" >&2
    fail=1
  fi
done

# Prove that the new multi-store case produced its intended ArrNested artifact,
# then kernel-check that exact emitted source (not merely some earlier artifact
# from the same refutation).
"$AY_BIN" "$WORK/array_nested.smt2" --proof "$WORK/array_nested.alethe" \
  --emit-firewall-lean "$WORK/array-nested-lean" >/dev/null 2>&1
NESTED_FW="$(grep -El \
  'namespace AySoundness\.Emitted\.ArrNested_' \
  "$WORK"/array-nested-lean/firewall_*.lean 2>/dev/null | head -n 1 || true)"
if [[ -n "$NESTED_FW" ]] \
  && ( cd "$LEAN_PROJECT" && "$LAKE" env lean -j1 -s8192 "$NESTED_FW" ) >/dev/null 2>&1; then
  echo "firewall-selfcert-check: array_nested-source PASS (ArrNested artifact kernel-checked)"
else
  echo "firewall-selfcert-check: array_nested-source FAIL — ArrNested artifact missing or rejected" >&2
  fail=1
fi

# --- The local checker has teeth: a corrupted artifact must be REJECTED --------
# Emit a datatype diagnostic, corrupt its RUP proof, and confirm the Lean kernel
# rejects that local theorem. This says nothing about a query-level certificate.
"$AY_BIN" "$WORK/datatype.smt2" --proof "$WORK/dt.alethe" \
  --emit-firewall-lean "$WORK/lean" >/dev/null 2>&1
FW="$WORK/lean/firewall_0.lean"
if [[ ! -f "$FW" ]]; then
  echo "firewall-selfcert-check: corruption-test FAIL — no firewall was emitted" >&2
  fail=1
else
  # Drop a clause id from the RUP proof antecedents so lratCheck no longer closes.
  sed 's/\[1, 2, 3\]/[1, 2]/' "$FW" > "$WORK/lean/corrupt.lean"
  if ( cd "$LEAN_PROJECT" && "$LAKE" env lean -j1 -s8192 "$WORK/lean/corrupt.lean" ) >/dev/null 2>&1; then
    echo "firewall-selfcert-check: corruption-test FAIL — Lean ACCEPTED a corrupt firewall" >&2
    fail=1
  else
    echo "firewall-selfcert-check: corruption-test PASS (Lean rejected the corrupt firewall)"
  fi
fi

if [[ "$fail" -eq 0 ]]; then
  echo "firewall-selfcert-check: ALL DIAGNOSTICS PASS (no query was certified)"
else
  echo "firewall-selfcert-check: FAILURES present" >&2
fi
exit "$fail"
