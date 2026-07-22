// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_AUFLIRA soundness gate tests.
//!
//! Consumer-facing mixed-theory route: arrays + mixed Int/Real arithmetic.
//! This module keeps the committed AUFLIRA cross-sort and ROW2 shapes under the
//! shared SMT gate so future solver changes cannot regress them silently.

use ntest::timeout;

use super::helpers::{
    assert_sat_validates, assert_scope_results, assert_unsat_with_proof, ProofExpectation,
};

// --- 1. SAT with model validation ---

#[test]
#[timeout(30_000)]
fn test_gate_qf_auflira_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_AUFLIRA)
        (declare-const a (Array Int Int))
        (declare-const phase Int)
        (declare-const y Real)
        (assert (>= phase 0))
        (assert (<= phase 1))
        (assert (= (select (store a 0 phase) 0) phase))
        (assert (>= (to_real (select (store a 0 phase) 0)) 0.5))
        (assert (= y (+ (to_real phase) 0.5)))
        (assert (> y 1.0))
        (check-sat)
    "#,
    );
}

// --- 2. UNSAT with proof envelope ---

#[test]
#[timeout(30_000)]
fn test_gate_qf_auflira_unsat_proof_envelope() {
    assert_unsat_with_proof(
        r#"
        (set-logic QF_AUFLIRA)
        (set-option :produce-proofs true)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (= j (+ i 1)))
        (assert (= (select (store a i 42) j) 42))
        (assert (not (= (select a j) 42)))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

// --- 3. Edge case: cross-sort propagation must stay sound ---

#[test]
#[timeout(30_000)]
fn test_gate_qf_auflira_cross_sort_edge_case_6198() {
    assert_unsat_with_proof(
        r#"
        (set-logic QF_AUFLIRA)
        (set-option :produce-proofs true)
        (declare-fun h (Real) Real)
        (declare-const x Int)
        (declare-const r Real)
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (= r (to_real x)))
        (assert (> r 1.5))
        (assert (= (h r) r))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

// --- 4. Incremental push/pop scope ---

#[test]
#[timeout(30_000)]
fn test_gate_qf_auflira_incremental_scope() {
    assert_scope_results(
        r#"
        (set-logic QF_AUFLIRA)
        (declare-const a (Array Int Real))
        (declare-const i Int)
        (declare-const y Real)
        (assert (= i 2))
        (assert (= y (+ (to_real i) 1.5)))
        (assert (= (select (store a i y) i) 3.5))
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
