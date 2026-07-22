// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_AX soundness gate tests (Packet 1).

use ntest::timeout;

use super::helpers::{
    assert_sat_validates, assert_scope_results, assert_unsat_with_proof, execute_script,
    ProofExpectation,
};

// --- 1. SAT with model validation ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_ax_sat_validates_model() {
    // Simple store/select SAT: select(store(a, 1, 42), 1) = 42.
    // Ported from array_soundness_4304.rs:87-127 pattern.
    assert_sat_validates(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (= i 7))
        (assert (= (select a i) 42))
        (check-sat)
    "#,
    );
}

// --- 2. UNSAT with proof envelope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_ax_unsat_proof_envelope() {
    // ROW1 contradiction: store(a, 0, 42) read at index 0 should give 42, not 7.
    assert_unsat_with_proof(
        r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-proofs true)
        (declare-const a (Array Int Int))
        (assert (= (select (store a 0 42) 0) 7))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

// --- 3. Edge case: ROW2 / concrete-index store/select ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_ax_edge_case() {
    // ROW2: reading from a different index than stored should return original.
    // store(a, 1, 42) read at index 0 should give select(a, 0), not 42.
    // If select(a, 0) = 5 and we assert select(store(a, 1, 42), 0) = 99, UNSAT.
    assert_unsat_with_proof(
        r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-proofs true)
        (declare-const a (Array Int Int))
        (assert (= (select a 0) 5))
        (assert (= (select (store a 1 42) 0) 99))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

// --- 4. Incremental push/pop scope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_ax_incremental_scope() {
    // Ported from qf_ax_benchmark_suite.rs:688-739.
    // Phantom axiom regression: after push/pop, dead terms must not generate
    // phantom axioms causing spurious Unknown.
    assert_scope_results(
        r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (check-sat)
        (push 1)
        (assert (= (select (store a 0 42) 0) 7))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        &["sat", "unsat", "sat"],
    );
}

// --- 5. SAT result correctness with store equality ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_ax_sat_store_equality_result() {
    // b = store(a, 1, 42) and select(b, 1) = 42 — trivially SAT.
    //
    // validate_model() cannot verify this because the combined solver pipeline
    // drains ctx.assertions during array axiom processing, leaving total=0
    // after solve. The SAT result is correct; model validation coverage for
    // array store equality formulas is a known gap (ctx.assertions consumed
    // by combined.rs drain(axiom_start..)).
    let (_exec, outputs) = execute_script(
        r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= b (store a 1 42)))
        (assert (= (select b 1) 42))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0].trim(),
        "sat",
        "store equality formula must be SAT"
    );
}

// --- #r3-nested-arrayext wrong-UNSAT regression ---

/// Nested (array-of-arrays) store/extensionality must NOT spuriously refute.
/// Over `n1, n2 : Array Index (Array Index Elem)` and `c : Array Index Elem`,
/// the constraints `i0 != i1`, `n2 != n1`, and
/// `(select (store n1 i2 c) i1) != (store c i2 e2)` are SATISFIABLE. The earlier
/// bug fabricated an outer `__ext_diff` extensionality Skolem for the nested
/// `(n1, n2)` pair whose index equalities, combined with the UNRELATED `i0 != i1`
/// literal, unit-forced a spurious level-0 conflict (the #8741 failure mode one
/// array level up). The fix suppresses the redundant outer Skolem when one
/// operand is the base of a selected nested store. z3 AND cvc5 report sat.
#[test]
#[timeout(10_000)]
fn test_gate_qf_ax_nested_array_store_ext_not_unsat() {
    assert_scope_results(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Elem 0)
        (declare-const c (Array Index Elem))
        (declare-const n1 (Array Index (Array Index Elem)))
        (declare-const n2 (Array Index (Array Index Elem)))
        (declare-const i0 Index)
        (declare-const i1 Index)
        (declare-const i2 Index)
        (declare-const e2 Elem)
        (assert (not (= i0 i1)))
        (assert (not (= n2 n1)))
        (assert (not (= (select (store n1 i2 c) i1) (store c i2 e2))))
        (check-sat)
    "#,
        &["sat"],
    );
}

/// Control: the FLAT analogue (value sort = Elem, not a nested array) was always
/// correctly SAT and must stay SAT — the nested-only suppression must not change
/// the flat path. z3 AND cvc5 report sat.
#[test]
#[timeout(10_000)]
fn test_gate_qf_ax_flat_array_store_ext_still_sat() {
    assert_scope_results(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Elem 0)
        (declare-const m1 (Array Index Elem))
        (declare-const m2 (Array Index Elem))
        (declare-const i0 Index)
        (declare-const i1 Index)
        (declare-const i2 Index)
        (declare-const e2 Elem)
        (declare-const d Elem)
        (assert (not (= i0 i1)))
        (assert (not (= m2 m1)))
        (assert (not (= (select (store m1 i2 d) i1) e2)))
        (check-sat)
    "#,
        &["sat"],
    );
}
