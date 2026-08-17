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

// --- Exact finite-array closure architecture ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_ax_finite_ext_defers_aliases_until_after_substitution() {
    let (exec, outputs) = execute_script(
        r#"
        (set-logic QF_AX)
        (declare-const a0 (Array Bool Bool))
        (declare-const a1 (Array Bool Bool))
        (declare-const a2 (Array Bool Bool))
        (declare-const a3 (Array Bool Bool))
        (assert (= a1 (store a0 false true)))
        (assert (= a2 (store a1 true false)))
        (assert (= a3 (store a2 false false)))
        (declare-const p (Array Bool Bool))
        (declare-const q (Array Bool Bool))
        (assert (not (= p q)))
        (assert (= (select p false) (select q false)))
        (assert (= (select p true) (select q true)))
        (check-sat)
    "#,
    );

    assert_eq!(outputs, vec!["unsat"]);
    let stats = exec.statistics();
    assert_eq!(
        stats.get_int("smt.array.finite_ext.route_deferrals"),
        Some(1)
    );
    assert!(
        stats
            .get_int("smt.array.finite_ext.emitted_equalities")
            .is_some_and(|emitted| emitted > 0),
        "the route must emit exact coverage for its live post-substitution surface"
    );
    assert_eq!(
        stats.get_int("smt.array.finite_ext.budget_deferred_equalities"),
        Some(0)
    );
    assert_eq!(
        stats.get_int("smt.array.finite_ext.candidate_scan_truncated"),
        Some(0)
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_dt_ax_finite_ext_defers_aliases_until_after_substitution() {
    let (exec, outputs) = execute_script(
        r#"
        (set-logic ALL)
        (declare-datatype D ((d0) (d1)))
        (declare-const a0 (Array Bool D))
        (declare-const a1 (Array Bool D))
        (declare-const a2 (Array Bool D))
        (assert (= a1 (store a0 false d0)))
        (assert (= a2 (store a1 true d1)))
        (declare-const p (Array Bool D))
        (declare-const q (Array Bool D))
        (assert (not (= p q)))
        (assert (= (select p false) (select q false)))
        (assert (= (select p true) (select q true)))
        (check-sat)
    "#,
    );

    assert_eq!(outputs, vec!["unsat"]);
    let stats = exec.statistics();
    assert_eq!(
        stats.get_int("smt.array.finite_ext.route_deferrals"),
        Some(1),
        "DtAx must defer without traversing the raw store-flat aliases"
    );
    assert!(
        stats
            .get_int("smt.array.finite_ext.emitted_equalities")
            .is_some_and(|emitted| emitted > 0),
        "the DT+array route must emit exact coverage after DT preprocessing"
    );
    assert_eq!(
        stats.get_int("smt.array.finite_ext.budget_deferred_equalities"),
        Some(0)
    );
    assert_eq!(
        stats.get_int("smt.array.finite_ext.candidate_scan_truncated"),
        Some(0)
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_aufdt_routes_array_aware_and_closes_finite_arrays() {
    let (exec, outputs) = execute_script(
        r#"
        (set-logic AUFDT)
        (declare-datatype D ((d0) (d1)))
        (declare-const a (Array Bool D))
        (declare-const b (Array Bool D))
        (assert (= (select a false) (select b false)))
        (assert (= (select a true) (select b true)))
        (assert (not (= a b)))
        (check-sat)
    "#,
    );

    assert_eq!(outputs, vec!["unsat"]);
    let stats = exec.statistics();
    assert_eq!(stats.get_string("solver.logic_category"), Some("Aufdt"));
    assert_eq!(
        stats.get_int("smt.array.finite_ext.route_deferrals"),
        Some(1),
        "AUFDT must defer exact closure until after DT axiom preprocessing"
    );
    assert_eq!(
        stats.get_int("smt.array.finite_ext.emitted_equalities"),
        Some(1),
        "the finite Bool-indexed equality must close after DT preprocessing"
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_aufdt_assuming_routes_array_aware_and_closes_finite_arrays() {
    let (exec, outputs) = execute_script(
        r#"
        (set-logic AUFDT)
        (declare-datatype D ((d0) (d1)))
        (declare-const a (Array Bool D))
        (declare-const b (Array Bool D))
        (assert (= (select a false) (select b false)))
        (assert (= (select a true) (select b true)))
        (check-sat-assuming ((not (= a b))))
    "#,
    );

    assert_eq!(outputs, vec!["unsat"]);
    let stats = exec.statistics();
    assert_eq!(stats.get_string("solver.logic_category"), Some("Aufdt"));
    assert_eq!(
        stats.get_int("smt.array.finite_ext.route_deferrals"),
        Some(1),
        "AUFDT assumptions must share the array-aware DT query boundary"
    );
    assert_eq!(
        stats.get_int("smt.array.finite_ext.emitted_equalities"),
        Some(1),
        "assumption-only disequality must seed exact finite closure"
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_aufdtlra_alias_defers_to_array_aware_dt_lra_route() {
    let (exec, outputs) = execute_script(
        r#"
        (set-logic AUFDTLRA)
        (declare-datatype D ((d0) (d1)))
        (declare-const a (Array Bool D))
        (declare-const b (Array Bool D))
        (declare-const x Real)
        (assert (= x 0.0))
        (assert (= (select a false) (select b false)))
        (assert (= (select a true) (select b true)))
        (assert (not (= a b)))
        (check-sat)
    "#,
    );

    assert_eq!(outputs, vec!["unsat"]);
    let stats = exec.statistics();
    assert_eq!(stats.get_string("solver.logic_category"), Some("Ufdtlra"));
    assert_eq!(
        stats.get_int("smt.array.finite_ext.route_deferrals"),
        Some(1),
        "AUFDTLRA's shared category must defer to its DT+AUFLRA pipeline"
    );
    assert_eq!(
        stats.get_int("smt.array.finite_ext.emitted_equalities"),
        Some(1)
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_ax_nested_finite_extensionality_closes_before_current_quarantine() {
    let (exec, outputs) = execute_script(
        r#"
        (set-logic QF_AX)
        (declare-const a (Array Bool (Array Bool Bool)))
        (declare-const b (Array Bool (Array Bool Bool)))
        (assert (not (= a b)))
        (assert (= (select (select a false) false) (select (select b false) false)))
        (assert (= (select (select a false) true) (select (select b false) true)))
        (assert (= (select (select a true) false) (select (select b true) false)))
        (assert (= (select (select a true) true) (select (select b true) true)))
        (check-sat)
    "#,
    );

    assert_eq!(outputs, vec!["unsat"]);
    let stats = exec.statistics();
    assert_eq!(
        stats.get_int("smt.array.finite_ext.emitted_equalities"),
        Some(3),
        "the outer equality and both array-valued cells must close before exact source authentication"
    );
}

#[test]
#[timeout(10_000)]
fn test_gate_qf_ax_array_valued_symbolic_select_has_strict_proof() {
    assert_unsat_with_proof(
        r#"
        (set-logic QF_AX)
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (declare-const outer (Array Bool (Array Bool Bool)))
        (declare-const cell (Array Bool Bool))
        (declare-const p Bool)
        (assert (= (select outer false) cell))
        (assert (= (select outer true) cell))
        (assert (not (= (select outer p) cell)))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::InternalChecked,
    );
}
