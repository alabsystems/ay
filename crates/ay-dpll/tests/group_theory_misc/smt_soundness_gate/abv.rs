// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_ABV soundness gate tests.
//!
//! Consumer: a downstream proof consumer uses QF_ABV incrementally for proof obligation discharge.
//! This gate covers the BV+Array combined solver path.

use ntest::timeout;

use super::helpers::{
    assert_sat_validates, assert_scope_results, assert_unsat_with_proof, execute_script,
    ProofExpectation,
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

// --- 5. Finite extensionality runs after store-flat substitution ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_abv_finite_ext_defers_store_flat_aliases_until_after_preprocess() {
    // Each store-flat definition is an eligible BV4 array equality before
    // preprocessing. Expanding all of them there is wasted work: scalar/array
    // substitution removes the aliases before the QF_ABV route needs finite
    // extensionality. Keep one non-definitional equality alive so this test also
    // proves that the post-preprocess pass really emits its exact 16-point axiom.
    let (exec, outputs) = execute_script(
        r#"
        (set-logic QF_ABV)
        (declare-const a0 (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-const a1 (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-const a2 (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-const a3 (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-const a4 (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-const a5 (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-const a6 (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-const a7 (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-const a8 (Array (_ BitVec 4) (_ BitVec 8)))
        (assert (= a1 (store a0 #x0 #x10)))
        (assert (= a2 (store a1 #x1 #x11)))
        (assert (= a3 (store a2 #x2 #x12)))
        (assert (= a4 (store a3 #x3 #x13)))
        (assert (= a5 (store a4 #x4 #x14)))
        (assert (= a6 (store a5 #x5 #x15)))
        (assert (= a7 (store a6 #x6 #x16)))
        (assert (= a8 (store a7 #x7 #x17)))

        (declare-const p (Array (_ BitVec 4) (_ BitVec 8)))
        (assert (= (select p #x0) #x02))
        (assert (= (store p #x0 #x01) (store p #x1 #x02)))
        (check-sat)
    "#,
    );

    assert_eq!(outputs, vec!["unsat"]);

    let stats = exec.statistics();
    for (key, expected) in [
        ("smt.array.finite_ext.route_deferrals", 1),
        ("smt.array.finite_ext.budget_deferred_equalities", 0),
        ("smt.array.finite_ext.budget_deferred_selects", 0),
        ("smt.array.finite_ext.candidate_scan_truncated", 0),
    ] {
        assert_eq!(
            stats.get_int(key),
            Some(expected),
            "unexpected {key} statistic: {stats:?}"
        );
    }
    assert!(
        stats
            .get_int("smt.array.finite_ext.emitted_equalities")
            .is_some_and(|emitted| emitted > 0),
        "the route must emit exact finite-array coverage for its live post-fixpoint surface"
    );
}

// --- 6. Aggregate finite-array budget is fail-closed on SAT ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_abv_finite_ext_budget_sat_becomes_unknown() {
    let (exec, outputs) = execute_script(
        r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 1024)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 1024)))
        (assert (not (= a b)))
        (check-sat)
    "#,
    );

    assert_eq!(outputs, vec!["unknown"]);
    assert_eq!(
        exec.statistics()
            .get_int("smt.array.finite_ext.budget_deferred_equalities"),
        Some(1)
    );
    assert_eq!(
        exec.statistics()
            .get_int("smt.array.finite_ext.emitted_equalities"),
        Some(0)
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_abv_finite_ext_budget_check_sat_assuming_becomes_unknown() {
    let (exec, outputs) = execute_script(
        r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 1024)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 1024)))
        (check-sat-assuming ((not (= a b))))
    "#,
    );

    assert_eq!(outputs, vec!["unknown"]);
    assert_eq!(
        exec.statistics()
            .get_int("smt.array.finite_ext.budget_deferred_equalities"),
        Some(1)
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_abv_finite_ext_budget_keeps_independent_unsat() {
    let (exec, outputs) = execute_script(
        r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 1024)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 1024)))
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (not (= a b)))
        (assert (or p q))
        (assert (or p (not q)))
        (assert (or (not p) q))
        (assert (or (not p) (not q)))
        (check-sat)
    "#,
    );

    assert_eq!(outputs, vec!["unsat"]);
    assert_eq!(
        exec.statistics()
            .get_int("smt.array.finite_ext.budget_deferred_equalities"),
        Some(1),
        "the UNSAT must be preserved from a solve that actually deferred the independent array equality"
    );
}

// --- 7. Nested finite arrays reach closure in one route invocation ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_abv_nested_finite_array_extensionality_unsat() {
    let (exec, outputs) = execute_script(
        r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 1) (Array (_ BitVec 1) (_ BitVec 1))))
        (declare-const b (Array (_ BitVec 1) (Array (_ BitVec 1) (_ BitVec 1))))
        (assert (not (= a b)))
        (assert (= (select (select a #b0) #b0) (select (select b #b0) #b0)))
        (assert (= (select (select a #b0) #b1) (select (select b #b0) #b1)))
        (assert (= (select (select a #b1) #b0) (select (select b #b1) #b0)))
        (assert (= (select (select a #b1) #b1) (select (select b #b1) #b1)))
        (check-sat)
    "#,
    );

    assert_eq!(outputs, vec!["unsat"]);
    assert_eq!(
        exec.statistics()
            .get_int("smt.array.finite_ext.emitted_equalities"),
        Some(3),
        "one outer plus two generated inner equalities must be closed"
    );
    assert_eq!(
        exec.statistics()
            .get_int("smt.array.finite_ext.budget_deferred_equalities"),
        Some(0)
    );
}

// --- 8. The route closes equalities synthesized by its legacy fixpoint ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_abv_closes_finite_cell_equality_after_array_fixpoint() {
    let (exec, outputs) = execute_script(
        r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 16) (Array (_ BitVec 1) (_ BitVec 1))))
        (declare-const b (Array (_ BitVec 16) (Array (_ BitVec 1) (_ BitVec 1))))
        (declare-const i (_ BitVec 16))
        (declare-const p Bool)
        (assert (or (= a b) p))
        (assert (not p))
        (assert (not (= (select (select a i) #b0)
                        (select (select b i) #b0))))
        (check-sat)
    "#,
    );

    assert_eq!(outputs, vec!["unsat"]);
    let stats = exec.statistics();
    for (key, expected) in [
        ("smt.array.finite_ext.route_deferrals", 1),
        ("smt.array.finite_ext.candidate_equalities", 1),
        ("smt.array.finite_ext.emitted_equalities", 1),
        ("smt.array.finite_ext.emitted_index_points", 2),
        ("smt.array.finite_ext.budget_deferred_equalities", 0),
    ] {
        assert_eq!(
            stats.get_int(key),
            Some(expected),
            "unexpected {key} statistic: {stats:?}"
        );
    }
}

// --- 9. Non-vacuous indirect-index ROW2 regression (#8510) ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_abv_indirect_index_row2_unsat_8510() {
    let (exec, outputs) = execute_script(
        r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 16) (_ BitVec 8)))
        (declare-const i (_ BitVec 16))
        (declare-const j (_ BitVec 16))
        (assert (bvule i j))
        (assert (bvule j i))
        (assert (= (select (store mem i #xAA) j) #xBB))
        (check-sat)
    "#,
    );

    assert_eq!(outputs, vec!["unsat"]);
    let stats = exec.statistics();
    for (key, expected) in [
        ("smt.array.finite_ext.candidate_equalities", 0),
        ("smt.array.finite_ext.emitted_equalities", 0),
        ("smt.array.finite_ext.budget_deferred_equalities", 0),
        ("smt.abv.array_fixpoint.complex_selects", 1),
        ("smt.abv.array_fixpoint.runs", 1),
        ("smt.abv.array_fixpoint.skips", 0),
        ("smt.abv.array_fc_cegar.refinement_rounds", 0),
    ] {
        assert_eq!(
            stats.get_int(key),
            Some(expected),
            "unexpected {key} statistic: {stats:?}"
        );
    }
}
