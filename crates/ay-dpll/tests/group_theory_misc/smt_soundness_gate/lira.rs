// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_LIRA soundness gate tests.
//!
//! Consumers: neural-verification-consumer and model-checker consumer rely on mixed Int/Real reasoning through
//! `to_real` equalities and Big-M encodings. This gate keeps those mixed
//! arithmetic paths under the shared soundness harness.

use ntest::timeout;

use super::helpers::{
    assert_not_sat_with_optional_proof, assert_sat_validates, assert_scope_results,
    ProofExpectation,
};

// --- 1. SAT with model validation ---

#[test]
#[timeout(30_000)]
fn test_gate_qf_lira_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_LIRA)
        (declare-const x Int)
        (declare-const y Real)
        (assert (= x 2))
        (assert (= y (+ (to_real x) 0.5)))
        (assert (> y 2.0))
        (check-sat)
    "#,
    );
}

// --- 2. UNSAT with proof envelope ---

#[test]
#[timeout(30_000)]
fn test_gate_qf_lira_unsat_proof_envelope() {
    assert_not_sat_with_optional_proof(
        r#"
        (set-logic QF_LIRA)
        (set-option :produce-proofs true)
        (declare-const x Int)
        (declare-const y Real)
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (= y (to_real x)))
        (assert (> y 1.5))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::InternalChecked,
    );
}

// --- 3. Edge case: Big-M phase gating must stay sound ---

#[test]
#[timeout(30_000)]
fn test_gate_qf_lira_big_m_edge_case_5947() {
    assert_not_sat_with_optional_proof(
        r#"
        (set-logic QF_LIRA)
        (set-option :produce-proofs true)
        (declare-const relu Real)
        (declare-const phase Int)
        (assert (>= phase 0))
        (assert (<= phase 0))
        (assert (>= relu 0.0))
        (assert (<= relu (* 100.0 (to_real phase))))
        (assert (>= relu 1.0))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

// --- 4. Incremental push/pop scope ---

#[test]
#[timeout(30_000)]
fn test_gate_qf_lira_incremental_scope() {
    assert_scope_results(
        r#"
        (set-logic QF_LIRA)
        (declare-const phase Int)
        (declare-const y Real)
        (assert (>= phase 0))
        (assert (<= phase 1))
        (assert (= y (to_real phase)))
        (assert (> y 0.5))
        (check-sat)
        (push 1)
        (assert (< y 0.0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        &["sat", "unsat", "sat"],
    );
}
