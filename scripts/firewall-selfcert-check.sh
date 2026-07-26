#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates
#
# Firewall diagnostic smoke check.
#
# Exercises, end-to-end, the diagnostic side of `ay --verify-firewall`: for one
# internally-UNSAT case per covered theory, AY reconstructs a local firewall
# artifact and kernel-checks it with the real Lean toolchain. The six harvested
# QF_AX store-commutativity / ROW-conflict regressions are also replayed from
# their checked-in inputs, with the intended emitted source selected and checked
# directly by Lean. These artifacts are not independently bound to the complete
# frontend query, so the required public verdict is `unknown` even when every
# local artifact passes. Negative tests confirm both recognizer decline and Lean
# rejection of a damaged artifact.
#
# Usage:
#   ./scripts/firewall-selfcert-check.sh
#
# Exit codes:
#   0  all available local diagnostics passed, every verdict stayed unknown,
#      and a corrupted local artifact was rejected (this does NOT certify any
#      query). On a host without safe child-process containment, runtime checks
#      are reported as SKIP while the exact emitted sources are still checked.
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
runtime_skips=0

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

# Replay one checked-in QF_AX regression through BOTH public diagnostic
# verification and explicit source emission. The first path checks that the
# query verdict remains conservative (`unknown`) and that the runtime verifier's
# axiom audit passes. The second selects the intended recognizer artifact,
# enforces the one-artifact contract, and sends that exact source to Lean.
QFAX_3IDX_FW=""
check_qfax_firewall() {
  local name="$1"
  local namespace="$2"
  local input="$REPO_ROOT/benchmarks/smt/QF_AX/$name.smt2"
  local err="$WORK/qfax-$name.verify.err"
  local out verdict emit_dir proof_path emit_err artifact candidate verify_mode
  local artifact_count expected_count module audit_source axiom_report axioms audit_remainder

  out="$("$AY_BIN" "$input" --proof "$WORK/qfax-$name.verify.alethe" \
    --verify-firewall 2>"$err" | grep -vE '^c ')"
  verdict="$(echo "$out" | tr -d '[:space:]')"
  verify_mode="runtime-checked"
  if [[ "$verdict" == "unknown" ]] \
    && grep -Eq 'firewall diagnostic #[0-9]+ PASS' "$err" \
    && diagnostics_all_passed "$err" \
    && grep -q 'axiom audit passed' "$err" \
    && grep -q 'artifacts do not certify the query; reporting unknown' "$err"; then
    :
  elif [[ "$verdict" == "unknown" ]] \
    && grep -q 'firewall-diagnostic-process-containment-unavailable' "$err" \
    && grep -q 'firewall diagnostic incomplete — no query-bound certificate; reporting unknown' "$err"; then
    # macOS and other unsupported hosts must remain fail-closed. The explicit
    # bounded Lean check + axiom audit below still validates the emitted source.
    verify_mode="runtime-containment-unavailable"
    runtime_skips=$((runtime_skips + 1))
  else
    echo "firewall-selfcert-check: qfax-$name FAIL — verify verdict='$verdict'" >&2
    sed 's/^/    /' "$err" >&2
    fail=1
    return
  fi

  emit_dir="$WORK/qfax-$name-lean"
  proof_path="$WORK/qfax-$name.alethe"
  emit_err="$WORK/qfax-$name.emit.err"
  if ! "$AY_BIN" "$input" --proof "$proof_path" \
    --emit-firewall-lean "$emit_dir" >"$WORK/qfax-$name.emit.out" 2>"$emit_err"; then
    echo "firewall-selfcert-check: qfax-$name FAIL — explicit emission failed" >&2
    sed 's/^/    /' "$emit_err" >&2
    fail=1
    return
  fi

  artifact=""
  artifact_count=0
  expected_count=0
  for candidate in "$emit_dir"/firewall_*.lean; do
    [[ -f "$candidate" ]] || continue
    artifact_count=$((artifact_count + 1))
    if grep -Fq "namespace AySoundness.Emitted.${namespace}_" "$candidate"; then
      artifact="$candidate"
      expected_count=$((expected_count + 1))
    fi
  done
  if [[ "$artifact_count" -ne 1 || "$expected_count" -ne 1 || -z "$artifact" ]]; then
    echo "firewall-selfcert-check: qfax-$name FAIL — expected exactly one ${namespace} artifact; total=$artifact_count matching=$expected_count" >&2
    sed 's/^/    /' "$emit_err" >&2
    fail=1
    return
  fi

  if [[ "$name" == "storecomm_sf_3idx" ]] \
    && ! grep -Fq 'def lemmas   : List (Cid × Clause) := [(5, [1, 2, 3, 4])]' "$artifact"; then
    echo "firewall-selfcert-check: qfax-$name FAIL — three-index guard clause missing" >&2
    fail=1
    return
  fi

  module="$(sed -nE 's/^namespace (AySoundness[.]Emitted[.][^[:space:]]+)$/\1/p' "$artifact" | tail -n 1)"
  if [[ -z "$module" ]]; then
    echo "firewall-selfcert-check: qfax-$name FAIL — emitted namespace could not be audited" >&2
    fail=1
    return
  fi
  audit_source="$emit_dir/firewall_axiom_audit.lean"
  cp "$artifact" "$audit_source"
  printf '\n#print axioms %s.no_model\n' "$module" >> "$audit_source"
  if ! ( cd "$LEAN_PROJECT" && "$LAKE" env lean -j1 -s8192 "$audit_source" ) \
    >"$WORK/qfax-$name.lean.out" 2>"$WORK/qfax-$name.lean.err"; then
    echo "firewall-selfcert-check: qfax-$name FAIL — emitted ${namespace} source rejected by Lean" >&2
    sed 's/^/    /' "$WORK/qfax-$name.lean.err" >&2
    fail=1
    return
  fi
  if grep -q 'sorryAx' "$WORK/qfax-$name.lean.out" "$WORK/qfax-$name.lean.err"; then
    echo "firewall-selfcert-check: qfax-$name FAIL — emitted theorem depends on sorryAx" >&2
    fail=1
    return
  fi
  # Lean line-wraps a long qualified theorem name and three-axiom footprint.
  # Normalize the complete report before extracting the bracketed allowlist.
  axiom_report="$(
    tr '\n' ' ' < "$WORK/qfax-$name.lean.out"
    tr '\n' ' ' < "$WORK/qfax-$name.lean.err"
  )"
  axioms="$(printf '%s' "$axiom_report" \
    | sed -nE 's/.*depends on axioms: \[([^]]*)\].*/\1/p')"
  if [[ -z "$axioms" ]] \
    && [[ "$axiom_report" != *"does not depend on any axioms"* ]]; then
    echo "firewall-selfcert-check: qfax-$name FAIL — #print axioms output missing" >&2
    fail=1
    return
  fi
  audit_remainder="$(printf '%s' "$axioms" \
    | sed -e 's/propext//g' -e 's/Classical[.]choice//g' -e 's/Quot[.]sound//g' \
    | tr -d '[:space:],')"
  if [[ -n "$audit_remainder" ]]; then
    echo "firewall-selfcert-check: qfax-$name FAIL — unexpected axioms: $axioms" >&2
    fail=1
    return
  fi

  if [[ "$name" == "storecomm_sf_3idx" ]]; then
    QFAX_3IDX_FW="$artifact"
  fi
  echo "firewall-selfcert-check: qfax-$name PASS (${namespace} emitted once, axiom-audited, kernel-checked; $verify_mode)"
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
  elif [[ "$verdict" == "unknown" ]] \
    && grep -q 'firewall-diagnostic-process-containment-unavailable' "$WORK/$name.err" \
    && grep -q 'firewall diagnostic incomplete — no query-bound certificate; reporting unknown' "$WORK/$name.err"; then
    echo "firewall-selfcert-check: $name  SKIP (runtime containment unavailable; query remained unknown)"
    runtime_skips=$((runtime_skips + 1))
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

# --- Harvested QF_AX store / ROW conflicts ------------------------------------
# These are the six concrete regressions closed by the store-commutativity,
# conflicting-stores, and diamond-conflict recognizers. Keep the file-level
# replay explicit: two inputs intentionally share the same logical direct-store
# shape, and both must remain covered as checked-in release regressions.
check_qfax_firewall storecomm_minimal ArrStoreComm
check_qfax_firewall storecomm_array_diseq ArrStoreComm
check_qfax_firewall storecomm_sf_minimal ArrStoreComm
check_qfax_firewall storecomm_sf_3idx ArrStoreComm
check_qfax_firewall conflicting_stores ArrConflStores
check_qfax_firewall diamond_conflict ArrDiamond

# Near miss: when the two write indices coincide and the values differ, opposite
# store orderings can denote different arrays. The query is SAT, and the guarded
# store-commutativity recognizer must not emit an ArrStoreComm artifact.
cat > "$WORK/storecomm_near_miss.smt2" <<'EOF'
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Elem 0)
(declare-fun a () (Array Index Elem))
(declare-fun i () Index)
(declare-fun j () Index)
(declare-fun v () Elem)
(declare-fun w () Elem)
(assert (= i j))
(assert (not (= v w)))
(assert (not (= (store (store a i v) j w) (store (store a j w) i v))))
(check-sat)
EOF
NEAR_DIR="$WORK/storecomm-near-miss-lean"
"$AY_BIN" "$WORK/storecomm_near_miss.smt2" --proof "$WORK/storecomm-near-miss.alethe" \
  --emit-firewall-lean "$NEAR_DIR" >"$WORK/storecomm-near-miss.out" \
  2>"$WORK/storecomm-near-miss.err"
NEAR_RC=$?
NEAR_VERDICT="$(grep -vE '^c ' "$WORK/storecomm-near-miss.out" | tr -d '[:space:]')"
NEAR_FW="$(grep -El 'namespace AySoundness\.Emitted\.ArrStoreComm_' \
  "$NEAR_DIR"/firewall_*.lean 2>/dev/null | head -n 1 || true)"
if [[ "$NEAR_RC" -eq 0 && "$NEAR_VERDICT" == "sat" && -z "$NEAR_FW" ]]; then
  echo "firewall-selfcert-check: qfax-storecomm-near-miss PASS (SAT; recognizer declined)"
else
  echo "firewall-selfcert-check: qfax-storecomm-near-miss FAIL — rc=$NEAR_RC verdict='$NEAR_VERDICT' artifact='$NEAR_FW'" >&2
  sed 's/^/    /' "$WORK/storecomm-near-miss.err" >&2
  fail=1
fi

# Mutate the three-index certificate itself: remove the learned guarded ROW
# clause from the final RUP antecedents. The emitted source must change, and Lean
# must reject the now-invalid `no_model` theorem.
if [[ -z "$QFAX_3IDX_FW" || ! -f "$QFAX_3IDX_FW" ]]; then
  echo "firewall-selfcert-check: qfax-storecomm-corruption FAIL — no three-index source" >&2
  fail=1
else
  QFAX_CORRUPT="$WORK/qfax-storecomm-3idx-corrupt.lean"
  sed 's/\[1, 2, 3, 4, 5\]/[1, 2, 3, 4]/' "$QFAX_3IDX_FW" > "$QFAX_CORRUPT"
  if cmp -s "$QFAX_3IDX_FW" "$QFAX_CORRUPT"; then
    echo "firewall-selfcert-check: qfax-storecomm-corruption FAIL — mutation did not match" >&2
    fail=1
  elif ( cd "$LEAN_PROJECT" && "$LAKE" env lean -j1 -s8192 "$QFAX_CORRUPT" ) \
    >"$WORK/qfax-storecomm-corrupt.out" 2>"$WORK/qfax-storecomm-corrupt.err"; then
    echo "firewall-selfcert-check: qfax-storecomm-corruption FAIL — Lean ACCEPTED damaged proof" >&2
    fail=1
  else
    echo "firewall-selfcert-check: qfax-storecomm-corruption PASS (Lean rejected damaged proof)"
  fi
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

if [[ "$fail" -eq 0 && "$runtime_skips" -eq 0 ]]; then
  echo "firewall-selfcert-check: ALL DIAGNOSTICS PASS (no query was certified)"
elif [[ "$fail" -eq 0 ]]; then
  echo "firewall-selfcert-check: ALL AVAILABLE CHECKS PASS ($runtime_skips runtime check(s) skipped; exact source checks passed; no query was certified)"
else
  echo "firewall-selfcert-check: FAILURES present" >&2
fi
exit "$fail"
