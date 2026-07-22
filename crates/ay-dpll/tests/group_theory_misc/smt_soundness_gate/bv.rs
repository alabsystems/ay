// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_BV soundness gate tests (Packet 1).

use ntest::timeout;

use super::helpers::{
    assert_sat_validates, assert_scope_results, assert_unsat_with_proof, ProofExpectation,
};

// --- 1. SAT with model validation ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_bv_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x #x0A))
        (assert (= y (bvadd x #x05)))
        (check-sat)
    "#,
    );
}

// --- 2. UNSAT with proof envelope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_bv_unsat_proof_envelope() {
    // Direct contradiction: x = #x0A AND x = #xFF.
    assert_unsat_with_proof(
        r#"
        (set-logic QF_BV)
        (set-option :produce-proofs true)
        (declare-const x (_ BitVec 8))
        (assert (= x #x0A))
        (assert (= x #xFF))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

// --- 3. Edge case: non-trivial BV operators ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_bv_edge_case() {
    // Uses bvand and bvule to exercise non-trivial BV reasoning.
    // (bvand x #x0F) = #x0F means lower nibble is all 1s.
    // (bvule x #x0E) means x <= 14. But if lower nibble is #x0F,
    // x is at least #x0F = 15. Contradiction.
    assert_unsat_with_proof(
        r#"
        (set-logic QF_BV)
        (set-option :produce-proofs true)
        (declare-const x (_ BitVec 8))
        (assert (= (bvand x #x0F) #x0F))
        (assert (bvule x #x0E))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

// --- 4. Incremental push/pop scope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_bv_incremental_scope() {
    // Ported from bv_incremental_push_pop.rs:27-48.
    assert_scope_results(
        r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x #x0A))
        (check-sat)
        (push 1)
        (assert (= x #xFF))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        &["sat", "unsat", "sat"],
    );
}
