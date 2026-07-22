// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! BV<->LIA bridge: SAT-promotion for a backward `int2bv` pin with NO free
//! BitVec variable (G1-int2bv-backward-congruence).
//!
//! A BV-constant pin on `int2bv(w, k)` — `(= ((_ int2bv 8) k) (_ bv200 8))` —
//! forces the Int source `k ≡ 200 (mod 256)`. The `#bv2nat-const-pin` +
//! definitional-residue clauses already teach AUFLIA this congruence, so the
//! arithmetic side returns SAT with a concrete `k`. The gap was in the
//! SAT-PROMOTION guard: `all_bitvec_vars_are_bridge_only` rejects the query
//! (a BitVec `=` is a non-bridge op) and there is no free BitVec leaf to
//! materialize, so a validated AUFLIA model was discarded and the solve
//! degraded to `unknown (incomplete)`.
//!
//! FIX: when `collect_bv_leaf_vars` is empty (no free BitVec variable — a
//! declared BV const is a `Var`), every BitVec term is a DETERMINED function of
//! the Int model, so `validate_model` over the original roots is a definitive
//! arbiter and its pass promotes the AUFLIA SAT to a real SAT.
//!
//! SOUNDNESS: promotion is gated by `validate_model` over the ORIGINAL roots;
//! with no free BV var every BV atom is concretely re-evaluated, so a wrong
//! assignment yields a Violated atom and is rejected (kept `unknown`). The
//! `*_unsat` cases are the gate: a residue that cannot hold under the range must
//! still be `unsat`, never a false SAT.

use ntest::timeout;

fn verdict(smt: &str) -> String {
    let outputs = crate::common::solve_vec(smt);
    outputs
        .into_iter()
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "<none>".to_string())
}

/// G1 repro: `int2bv(8, k) = bv200` with `0 <= k < 256` uniquely forces
/// `k = 200` ⇒ SAT. Base revision returned `unknown (incomplete)`.
#[test]
#[timeout(60_000)]
fn test_int2bv_backward_pin_unique_range_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun k () Int)
        (assert (= ((_ int2bv 8) k) (_ bv200 8)))
        (assert (>= k 0))
        (assert (< k 256))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "sat",
        "int2bv(8,k)=bv200 with 0<=k<256 forces k=200 ⇒ SAT"
    );
}

/// No range bound: still SAT (any `k ≡ 200 (mod 256)` witnesses it).
#[test]
#[timeout(60_000)]
fn test_int2bv_backward_pin_no_range_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun k () Int)
        (assert (= ((_ int2bv 8) k) (_ bv200 8)))
        (check-sat)
    "#;
    assert_eq!(verdict(smt), "sat");
}

/// A width where the residue wraps: `int2bv(4, k) = bv3` with `16 <= k < 32`
/// forces `k = 19` (19 mod 16 = 3) ⇒ SAT.
#[test]
#[timeout(60_000)]
fn test_int2bv_backward_pin_overflow_width_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun k () Int)
        (assert (= ((_ int2bv 4) k) (_ bv3 4)))
        (assert (>= k 16))
        (assert (< k 32))
        (check-sat)
    "#;
    assert_eq!(verdict(smt), "sat", "int2bv(4,k)=bv3 with 16<=k<32 ⇒ k=19");
}

/// SOUNDNESS: `int2bv(8, k) = bv200` with `k = 5` is inconsistent
/// (5 mod 256 = 5 ≠ 200) — must be `unsat`, never a false SAT.
#[test]
#[timeout(60_000)]
fn test_int2bv_backward_pin_wrong_value_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun k () Int)
        (assert (= ((_ int2bv 8) k) (_ bv200 8)))
        (assert (= k 5))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "5 mod 256 = 5 ≠ 200 ⇒ UNSAT (never a false SAT)"
    );
}

/// SOUNDNESS: `int2bv(8, k) = bv200` with `0 <= k < 100` excludes every residue
/// (the smallest nonneg witness is 200) — must be `unsat`.
#[test]
#[timeout(60_000)]
fn test_int2bv_backward_pin_range_excludes_residue_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun k () Int)
        (assert (= ((_ int2bv 8) k) (_ bv200 8)))
        (assert (>= k 0))
        (assert (< k 100))
        (check-sat)
    "#;
    assert_eq!(verdict(smt), "unsat");
}
