// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_ABV soundness gate tests.
//!
//! Consumer: a downstream proof consumer uses QF_ABV incrementally for proof obligation discharge.
//! This gate covers the BV+Array combined solver path.

use ntest::timeout;

use super::helpers::{
    assert_sat_validates, assert_scope_results, assert_unsat_with_proof, ProofExpectation,
};

// --- 1. SAT with model validation ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_abv_sat_validates_model() {
    // BV array: store a 32-bit value and select it back.
    assert_sat_validates(
        r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-const i (_ BitVec 32))
        (declare-const v (_ BitVec 32))
        (assert (= i #x0000000A))
        (assert (= v #x0000002A))
        (assert (= (select (store a i v) i) v))
        (check-sat)
    "#,
    );
}

// --- 2. UNSAT with proof envelope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_abv_unsat_proof_envelope() {
    // Store v at index i, then assert select at same index != v. Contradiction.
    assert_unsat_with_proof(
        r#"
        (set-logic QF_ABV)
        (set-option :produce-proofs true)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (not (= (select (store a i v) i) v)))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

// --- 3. Edge case: BV arithmetic over array indices ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_abv_bv_index_arithmetic() {
    // Store at index (bvadd i #x01), select at (bvadd i #x01) — should be equal.
    // Store at index i, select at (bvadd i #x01) — should be independent.
    assert_sat_validates(
        r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (assert (= i #x05))
        (assert (= (select (store a (bvadd i #x01) #xFF) (bvadd i #x01)) #xFF))
        (assert (not (= (select (store a i #x00) (bvadd i #x01)) #x00)))
        (check-sat)
    "#,
    );
}

// --- 4. Incremental push/pop scope (incremental proof-obligation pattern) ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_abv_incremental_scope() {
    // incremental proof-obligation pattern: push, add proof obligation, check-sat, pop, repeat.
    assert_scope_results(
        r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 32) (_ BitVec 32)))
        (assert (= (select a #x00000001) #x0000002A))
        (check-sat)
        (push 1)
        (assert (not (= (select a #x00000001) #x0000002A)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        &["sat", "unsat", "sat"],
    );
}
