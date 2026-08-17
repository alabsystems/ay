// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `array_as_array_default_8534` to preserve test FQNs.

// === default axioms ===

/// default(const-array(v)) = v is a tautology.
#[test]
#[timeout(10_000)]
fn default_const_array_equals_value_unsat() {
    let result = crate::common::solve_vec(
        r#"
        (assert (not (= (default ((as const (Array Int Int)) 42)) 42)))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "default(const-array(42)) = 42 must hold"
    );
}

/// default(const-array(v)) = v in a satisfiable context.
#[test]
#[timeout(10_000)]
fn default_const_array_sat() {
    let result = crate::common::solve_vec(
        r#"
        (declare-const x Int)
        (assert (= (default ((as const (Array Int Int)) x)) x))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "sat",
        "default(const-array(x)) = x is satisfiable"
    );
}

/// Z3 5.0.0 leaves the default of a binder-dependent lambda opaque.  In
/// particular it is not the raw body with AY's syntactic binder exposed as a
/// free epsilon: it may differ from every value that the lambda returns.
#[test]
#[timeout(10_000)]
fn dependent_lambda_default_is_independent_of_body_values() {
    let result = crate::common::solve_vec(
        r#"
        (define-fun a () (Array Bool Int)
          (lambda ((x Bool)) (ite x 1 0)))
        (assert (distinct (default a) 0))
        (assert (distinct (default a) 1))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "sat",
        "a dependent lambda default is an independent scalar in Z3 5.0.0"
    );
}

/// default(store(a, i, v)) = default(a) tautology.
#[test]
#[timeout(10_000)]
fn default_store_equals_default_base_unsat() {
    let result = crate::common::solve_vec(
        r#"
        (assert (not (= (default (store ((as const (Array Int Int)) 7) 0 99)) 7)))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "default(store(const(7), 0, 99)) = 7 must hold"
    );
}

/// A Bool store chain can cover the complete carrier.  Its default is then a
/// selected array value, not the default of the pre-store constant array.
#[test]
#[timeout(10_000)]
fn default_bool_full_carrier_store_is_true() {
    let result = crate::common::solve_vec(
        r#"
        (define-fun a () (Array Bool Bool)
          (store (store ((as const (Array Bool Bool)) false) false true) true true))
        (assert (not (default a)))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "unsat", "both Bool cells force a true default");
}

/// BitVec(1) is the same two-element finite carrier as Bool for the default
/// store rule.
#[test]
#[timeout(10_000)]
fn default_bv1_full_carrier_store_is_true() {
    let result = crate::common::solve_vec(
        r#"
        (define-fun a () (Array (_ BitVec 1) Bool)
          (store (store ((as const (Array (_ BitVec 1) Bool)) false)
                        #b0 true)
                 #b1 true))
        (assert (not (default a)))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "unsat", "both BV1 cells force a true default");
}

/// Z3 shares one epsilon by index sort, including between distinct arrays.
/// The first default can be 1 only at epsilon=false; the second can be 2 only
/// at epsilon=true, so the conjunction is impossible.
#[test]
#[timeout(10_000)]
fn default_bool_epsilon_is_shared_across_arrays() {
    let result = crate::common::solve_vec(
        r#"
        (define-fun a () (Array Bool Int)
          (store ((as const (Array Bool Int)) 0) false 1))
        (define-fun b () (Array Bool Int)
          (store ((as const (Array Bool Int)) 0) true 2))
        (assert (= (default a) 1))
        (assert (= (default b) 2))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "unsat", "finite defaults must share epsilon");
}

/// Z3's exact cutoff is 2^14 inhabitants: BV13 uses epsilon/select and can
/// choose the stored cell, while BV14 is classified as large and preserves the
/// base default.
#[test]
#[timeout(10_000)]
fn default_store_matches_z3_bv13_bv14_cutoff() {
    let small = crate::common::solve_vec(
        r#"
        (define-fun a () (Array (_ BitVec 13) Int)
          (store ((as const (Array (_ BitVec 13) Int)) 0) (_ bv0 13) 1))
        (assert (= (default a) 1))
        (check-sat)
    "#,
    );
    assert_eq!(small[0], "sat", "BV13 uses the finite epsilon rule");

    let large = crate::common::solve_vec(
        r#"
        (define-fun a () (Array (_ BitVec 14) Int)
          (store ((as const (Array (_ BitVec 14) Int)) 0) (_ bv0 14) 1))
        (assert (= (default a) 1))
        (check-sat)
    "#,
    );
    assert_eq!(large[0], "unsat", "BV14 preserves the base default");
}

/// A relevant default follows an array equality to the store term before the
/// finite-carrier axioms are instantiated.
#[test]
#[timeout(10_000)]
fn default_bool_store_propagates_through_array_alias() {
    let result = crate::common::solve_vec(
        r#"
        (declare-const a (Array Bool Bool))
        (assert (= a
          (store (store ((as const (Array Bool Bool)) false) false true) true true)))
        (assert (not (default a)))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "default parent must cross array aliases"
    );
}

/// On a singleton carrier the stored value is necessarily the array default.
#[test]
#[timeout(10_000)]
fn default_singleton_datatype_store_is_stored_value() {
    let result = crate::common::solve_vec(
        r#"
        (declare-datatype Unit ((unit)))
        (define-fun a () (Array Unit Bool)
          (store ((as const (Array Unit Bool)) false) unit true))
        (assert (not (default a)))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "unsat", "unit carrier default is stored value");
}

/// A bare array default is still an independent model else-value in Z3; the
/// epsilon/select rule is instantiated for stores, not for every array term.
#[test]
#[timeout(10_000)]
fn default_bare_bool_array_need_not_equal_either_read() {
    let result = crate::common::solve_vec(
        r#"
        (declare-const a (Array Bool Int))
        (assert (distinct (default a) (select a false)))
        (assert (distinct (default a) (select a true)))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "sat", "bare default must remain unconstrained");
}

/// default on a symbolic array: basic satisfiability.
#[test]
#[timeout(10_000)]
fn default_symbolic_array_sat() {
    let result = crate::common::solve_vec(
        r#"
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (assert (= (default a) x))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "sat", "default(a) = x is satisfiable");
}

/// A nonzero symbolic else-value must survive substitution and model recovery.
#[test]
#[timeout(10_000)]
fn default_symbolic_array_nonzero_value_sat() {
    let result = crate::common::solve_vec(
        r#"
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (assert (= (default a) x))
        (assert (= x 5))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "sat",
        "default(a) = x = 5 must retain one coherent recovered value"
    );
}

/// Bool defaults cannot be dropped by the ArrayEUF alias fast path: unlike Int
/// recovery, an opaque Bool array observation has no arithmetic model slot.
#[test]
#[timeout(10_000)]
fn default_symbolic_bool_array_alias_sat() {
    let result = crate::common::solve_vec(
        r#"
        (declare-const a (Array Int Bool))
        (declare-const x Bool)
        (assert (= (default a) x))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "sat",
        "default(a) = x is satisfiable for Bool arrays"
    );
}

/// A true Bool default must be present in the whole-array witness, not only in
/// the SAT literal used to validate `(default a)`.
#[test]
#[timeout(10_000)]
fn default_symbolic_bool_array_model_matches_scalar_value() {
    let result = crate::common::solve_vec(
        r#"
        (declare-const a (Array Int Bool))
        (assert (default a))
        (check-sat)
        (get-model)
        (get-value (a (default a)))
    "#,
    );
    assert_eq!(result[0], "sat", "a true-default array has a valid model");
    let model = result.get(1).expect("get-model output");
    assert!(
        model.contains("((as const (Array Int Bool)) true)"),
        "whole-array model lost the committed true default: {model}"
    );
    let values = result.get(2).expect("get-value output");
    assert!(
        values.contains("((as const (Array Int Bool)) true)"),
        "get-value(a) lost the committed true default: {values}"
    );
    assert!(
        values.contains("((default a) true)"),
        "scalar default and array witness disagree: {values}"
    );
}

/// Changing a finite store value into the array default changes every unlisted
/// index and is therefore not a semantics-preserving model minimization.
#[test]
#[timeout(10_000)]
fn default_model_minimization_preserves_unlisted_indices() {
    let result = crate::common::solve_vec(
        r#"
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (assert (= (default a) x))
        (assert (= x 0))
        (assert (= (select a 0) 5))
        (assert (= (select a 1) 5))
        (check-sat)
        (get-value ((default a) x (select a 0) (select a 1) (select a 2)))
    "#,
    );
    assert_eq!(
        result[0], "sat",
        "the pinned-default array has a valid model"
    );
    let values = result.get(1).expect("get-value output");
    assert!(
        values.contains("((default a) 0)"),
        "wrong default: {values}"
    );
    assert!(values.contains("(x 0)"), "wrong scalar alias: {values}");
    assert!(
        values.contains("((select a 0) 5)"),
        "lost store 0: {values}"
    );
    assert!(
        values.contains("((select a 1) 5)"),
        "lost store 1: {values}"
    );
    assert!(
        values.contains("((select a 2) 0)"),
        "unlisted index changed with model minimization: {values}"
    );
}

/// default(store(a, i, v)) = default(a) for a symbolic array.
#[test]
#[timeout(10_000)]
fn default_store_symbolic_unsat() {
    let result = crate::common::solve_vec(
        r#"
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const v Int)
        (assert (not (= (default (store a i v)) (default a))))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "default(store(a, i, v)) = default(a) must hold"
    );
}

/// Nested store chains preserve default.
#[test]
#[timeout(10_000)]
fn default_nested_stores_unsat() {
    let result = crate::common::solve_vec(
        r#"
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v1 Int)
        (declare-const v2 Int)
        (assert (not (= (default (store (store a i v1) j v2)) (default a))))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "default propagates through nested stores"
    );
}
