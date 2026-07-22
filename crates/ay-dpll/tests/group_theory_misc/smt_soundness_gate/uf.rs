// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_UF soundness gate tests (Packet 1).

use ntest::timeout;

use super::helpers::{
    assert_sat_validates, assert_scope_results, assert_unsat_with_proof, ProofExpectation,
};

// --- 1. SAT with model validation ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_uf_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-const a S)
        (declare-const b S)
        (declare-fun f (S) S)
        (assert (= (f a) b))
        (assert (not (= a b)))
        (check-sat)
    "#,
    );
}

// --- 2. UNSAT with proof envelope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_uf_unsat_proof_envelope() {
    // Congruence contradiction: a = b AND f(a) != f(b).
    // Ported from euf_incremental_push_pop.rs:198-225.
    assert_unsat_with_proof(
        r#"
        (set-logic QF_UF)
        (set-option :produce-proofs true)
        (declare-sort S 0)
        (declare-fun f (S) S)
        (declare-const a S)
        (declare-const b S)
        (assert (= a b))
        (assert (not (= (f a) (f b))))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::InternalChecked,
    );
}

// --- 3. Edge case: transitivity chain ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_uf_edge_case() {
    // Transitivity: a = b, b = c, c = d, but f(a) != f(d).
    // The congruence closure must propagate through the chain.
    assert_unsat_with_proof(
        r#"
        (set-logic QF_UF)
        (set-option :produce-proofs true)
        (declare-sort S 0)
        (declare-fun f (S) S)
        (declare-const a S)
        (declare-const b S)
        (declare-const c S)
        (declare-const d S)
        (assert (= a b))
        (assert (= b c))
        (assert (= c d))
        (assert (not (= (f a) (f d))))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::InternalChecked,
    );
}

// --- 4. Incremental push/pop scope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_uf_incremental_scope() {
    // Ported from euf_incremental_push_pop.rs:27-48.
    assert_scope_results(
        r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-const a S)
        (declare-const b S)
        (assert (not (= a b)))
        (check-sat)
        (push 1)
        (assert (= a b))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        &["sat", "unsat", "sat"],
    );
}
