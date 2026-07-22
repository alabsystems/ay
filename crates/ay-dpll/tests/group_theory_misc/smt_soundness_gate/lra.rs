// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_LRA soundness gate tests (Packet 1).

use ntest::timeout;

use super::helpers::{
    assert_sat_validates, assert_scope_results, assert_unsat_with_proof, ProofExpectation,
};

// --- 1. SAT with model validation ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_lra_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= x 3.5))
        (assert (= y (+ x 1.5)))
        (assert (> y 0.0))
        (check-sat)
    "#,
    );
}

// --- 2. UNSAT with proof envelope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_lra_unsat_proof_envelope() {
    // Strict inequality contradiction: x > 1 AND x < 0.
    // Ported from lra_incremental_push_pop.rs:164-193.
    assert_unsat_with_proof(
        r#"
        (set-logic QF_LRA)
        (set-option :produce-proofs true)
        (declare-const x Real)
        (assert (> x 1.0))
        (assert (< x 0.0))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::InternalChecked,
    );
}

// --- 3. Edge case: mixed strict/non-strict bounds ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_lra_edge_case() {
    // x >= 5.0 AND x <= 5.0 AND x != 5.0 is UNSAT.
    // Tests the interaction of strict and non-strict bounds.
    assert_unsat_with_proof(
        r#"
        (set-logic QF_LRA)
        (set-option :produce-proofs true)
        (declare-const x Real)
        (assert (>= x 5.0))
        (assert (<= x 5.0))
        (assert (not (= x 5.0)))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::InternalChecked,
    );
}

// --- 4. Incremental push/pop scope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_lra_incremental_scope() {
    // Ported from lra_incremental_push_pop.rs:27-49.
    assert_scope_results(
        r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= (+ x y) 10.0))
        (check-sat)
        (push 1)
        (assert (>= x 100.0))
        (assert (>= y 100.0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        &["sat", "unsat", "sat"],
    );
}
