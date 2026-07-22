// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_LIA soundness gate tests (Packet 1).

use ntest::timeout;

use super::helpers::{
    assert_sat_validates, assert_scope_results, assert_unsat_with_proof, assert_verdict_not_sat,
    assert_verdict_not_unsat, ProofExpectation,
};

// --- 1. SAT with model validation ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_lia_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x 4))
        (assert (= y (+ x 2)))
        (assert (> y 0))
        (check-sat)
    "#,
    );
}

// --- 2. UNSAT with proof envelope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_lia_unsat_proof_envelope() {
    // Multi-variable sum: x+y >= 10 with x <= 3 and y <= 3 is UNSAT.
    // Ported from lia_incremental_push_pop.rs:306-343.
    assert_unsat_with_proof(
        r#"
        (set-logic QF_LIA)
        (set-option :produce-proofs true)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= (+ x y) 10))
        (assert (<= x 3))
        (assert (<= y 3))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::InternalChecked,
    );
}

// --- 3. Edge case: negative/zero constants ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_lia_edge_case() {
    // Involves negative constants and multiplication by -1 (unary minus).
    // x <= -5 AND x >= 0 is UNSAT.
    assert_unsat_with_proof(
        r#"
        (set-logic QF_LIA)
        (set-option :produce-proofs true)
        (declare-const x Int)
        (assert (<= x (- 5)))
        (assert (>= x 0))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::InternalChecked,
    );
}

// --- 4. Incremental push/pop scope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_lia_incremental_scope() {
    // Ported from lia_incremental_push_pop.rs:30-56.
    // Scoped assertions must not leak after pop.
    assert_scope_results(
        r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= (+ x y) 10))
        (check-sat)
        (push 1)
        (assert (>= x 100))
        (assert (>= y 100))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        &["sat", "unsat", "sat"],
    );
}

// --- 5. classA_residual_halfbounded: half-bounded negated existential must
//        preserve the X-free residual (was a wrong-UNSAT). ---
//
// `(not (exists X. (and (<= X 4) p)))` is SAT (set p = false): `(exists X. X<=4)`
// is trivially true, so the formula reduces to `(not p)`. AY previously dropped
// the residual `p` along the half-bounded-existential CEGQI path and answered a
// spurious UNSAT. The fix folds the trivially-true half-bounded existential to
// `true` (and miniscopes `exists`-over-`and` so an X-free conjunct survives),
// recovering the sound SAT. z3 = cvc5 = sat.

#[test]
#[timeout(10_000)]
fn test_gate_lia_class_a_residual_halfbounded_sat() {
    // The reverted bug: AY answered UNSAT. Must be SAT (p = false).
    assert_verdict_not_unsat(
        r#"
        (set-logic LIA)
        (declare-const p Bool)
        (assert (not (exists ((X0 Int)) (and (<= X0 4) p))))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_lia_class_a_residual_variants_sat() {
    // The residual is X-free of any shape (arith `q >= 10`, UF predicate
    // `(P y)`); all must stay SAT (set the residual false).
    assert_verdict_not_unsat(
        r#"
        (set-logic LIA)
        (declare-const q Int)
        (assert (not (exists ((X0 Int)) (and (<= X0 4) (>= q 10)))))
        (check-sat)
    "#,
    );
    assert_verdict_not_unsat(
        r#"
        (set-logic UFLIA)
        (declare-const y Int)
        (declare-fun P (Int) Bool)
        (assert (not (exists ((X0 Int)) (and (<= X0 4) (P y)))))
        (check-sat)
    "#,
    );
}

// --- ADVERSARIAL CONTROLS for the classA fix ---
//
// The reverted attempt added an UNSOUND forall-over-OR miniscope that flipped
// these SAT formulas to spurious UNSAT. The current fix must keep them SAT.

#[test]
#[timeout(10_000)]
fn test_gate_lia_class_a_control_forall_over_or_stays_sat() {
    // `(forall X. (or (> X 4) p))` is SAT (p = true). forall does NOT distribute
    // over OR; the fix must not touch this (or-bodied) quantifier.
    assert_verdict_not_unsat(
        r#"
        (set-logic LIA)
        (declare-const p Bool)
        (assert (forall ((X0 Int)) (or (> X0 4) p)))
        (check-sat)
    "#,
    );
    // Three-operand OR variant.
    assert_verdict_not_unsat(
        r#"
        (set-logic LIA)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (forall ((X0 Int)) (or (> X0 4) p q)))
        (check-sat)
    "#,
    );
    // Same forall-over-OR plus a separate `(assert p)`: still SAT.
    assert_verdict_not_unsat(
        r#"
        (set-logic LIA)
        (declare-const p Bool)
        (assert (forall ((X0 Int)) (or (> X0 4) p)))
        (assert p)
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_lia_class_a_control_free_var_disjunction_stays_sat() {
    // Quantifier-free `(or (< X 0) p)` and `(>= X 5) ∧ p` over free `X`: SAT.
    assert_verdict_not_unsat(
        r#"
        (set-logic LIA)
        (declare-const p Bool)
        (declare-const X0 Int)
        (assert (or (< X0 0) p))
        (check-sat)
    "#,
    );
    assert_verdict_not_unsat(
        r#"
        (set-logic LIA)
        (declare-const p Bool)
        (declare-const X0 Int)
        (assert (>= X0 5))
        (assert p)
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_lia_class_a_control_no_residual_unsat() {
    // No residual: `(not (exists X. (<= X 4)))` ≡ `(not true)` = UNSAT. The fold
    // must still close this (it must not over-preserve a nonexistent residual).
    assert_verdict_not_sat(
        r#"
        (set-logic LIA)
        (assert (not (exists ((X0 Int)) (<= X0 4))))
        (check-sat)
    "#,
    );
    // Reflexive degenerate atom `(< X X)` is UNSATISFIABLE and must NOT be folded
    // to true: `(exists X. (< X X))` is UNSAT.
    assert_verdict_not_sat(
        r#"
        (set-logic LIA)
        (assert (exists ((X0 Int)) (< X0 X0)))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_lia_class_a_control_residual_true_unsat() {
    // The residual forced TRUE: `(not (exists X. (and (<= X 4) p)))` with
    // `(assert p)` is UNSAT (the existential becomes true, its negation false).
    assert_verdict_not_sat(
        r#"
        (set-logic LIA)
        (declare-const p Bool)
        (assert (not (exists ((X0 Int)) (and (<= X0 4) p))))
        (assert p)
        (check-sat)
    "#,
    );
    // Empty range must stay SAT (negated unsatisfiable existential), never folded.
    assert_verdict_not_unsat(
        r#"
        (set-logic LIA)
        (assert (not (exists ((X0 Int)) (and (<= X0 4) (>= X0 10)))))
        (check-sat)
    "#,
    );
}
