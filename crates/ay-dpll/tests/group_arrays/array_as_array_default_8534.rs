// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for as-array and default array operations (#8534).
//!
//! Tests the following axioms:
//! - select(as-array(f), i) = f(i)
//! - default(const-array(v)) = v
//! - Z3 5.0.0's carrier-sensitive default(store(...)) rules
//!
//! Reference: Z3 theory_array_full.cpp:
//! - instantiate_select_as_array_axiom()
//! - default_const_axiom()
//! - instantiate_default_store_axiom()

use ntest::timeout;

// === as-array axiom: select(as-array(f), i) = f(i) ===

/// Basic as-array axiom: select(as-array(f), i) = f(i) is a tautology.
#[test]
#[timeout(10_000)]
fn as_array_select_equals_apply_unsat() {
    let result = crate::common::solve_vec(
        r#"
        (declare-fun f (Int) Int)
        (declare-const i Int)
        (assert (not (= (select (_ as-array f) i) (f i))))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "select(as-array(f), i) = f(i) must hold"
    );
}

/// as-array in a satisfiable context: f(0) = 42 implies select(as-array(f), 0) = 42.
#[test]
#[timeout(10_000)]
fn as_array_select_sat_with_constraint() {
    let result = crate::common::solve_vec(
        r#"
        (declare-fun f (Int) Int)
        (assert (= (f 0) 42))
        (assert (= (select (_ as-array f) 0) 42))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "sat",
        "f(0)=42 and select(as-array(f),0)=42 is consistent"
    );
}

/// as-array contradiction: f(0) = 42 but select(as-array(f), 0) = 99 is UNSAT.
#[test]
#[timeout(10_000)]
fn as_array_select_contradiction_unsat() {
    let result = crate::common::solve_vec(
        r#"
        (declare-fun f (Int) Int)
        (assert (= (f 0) 42))
        (assert (= (select (_ as-array f) 0) 99))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "f(0)=42 contradicts select(as-array(f),0)=99"
    );
}

/// as-array with Bool return sort: select(as-array(p), x) is p(x).
#[test]
#[timeout(10_000)]
fn as_array_bool_predicate_sat() {
    let result = crate::common::solve_vec(
        r#"
        (declare-fun p (Int) Bool)
        (declare-const x Int)
        (assert (p x))
        (assert (select (_ as-array p) x))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "sat",
        "p(x) and select(as-array(p), x) are the same"
    );
}

/// as-array with Bool: p(x) but NOT select(as-array(p), x) is UNSAT.
#[test]
#[timeout(10_000)]
fn as_array_bool_predicate_contradiction_unsat() {
    let result = crate::common::solve_vec(
        r#"
        (declare-fun p (Int) Bool)
        (declare-const x Int)
        (assert (p x))
        (assert (not (select (_ as-array p) x)))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "p(x) and NOT select(as-array(p), x) contradicts"
    );
}

/// as-array used in store: store(as-array(f), i, v) then select at i gives v.
#[test]
#[timeout(10_000)]
fn as_array_store_then_select_same_index_unsat() {
    let result = crate::common::solve_vec(
        r#"
        (declare-fun f (Int) Int)
        (declare-const i Int)
        (declare-const v Int)
        (assert (not (= (select (store (_ as-array f) i v) i) v)))
        (check-sat)
    "#,
    );
    assert_eq!(result[0], "unsat", "ROW1 on store over as-array");
}

/// as-array with store at different index: select at j gives f(j).
#[test]
#[timeout(10_000)]
fn as_array_store_select_different_index_unsat() {
    let result = crate::common::solve_vec(
        r#"
        (declare-fun f (Int) Int)
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (assert (not (= i j)))
        (assert (not (= (select (store (_ as-array f) i v) j) (f j))))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "unsat",
        "ROW2 on store over as-array: select at j gives f(j)"
    );
}

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

// === Combined as-array + default ===

/// default(as-array(f)) is a well-formed satisfiable term.
#[test]
#[timeout(10_000)]
fn default_as_array_sat() {
    let result = crate::common::solve_vec(
        r#"
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (assert (= (default (_ as-array f)) x))
        (check-sat)
    "#,
    );
    assert!(
        matches!(result[0].as_str(), "sat" | "unknown"),
        "default(as-array(f)) = x must not be reported unsat"
    );
}

/// Two as-array terms from same function are equal.
#[test]
#[timeout(10_000)]
fn as_array_same_function_equal_sat() {
    let result = crate::common::solve_vec(
        r#"
        (declare-fun f (Int) Int)
        (assert (= (_ as-array f) (_ as-array f)))
        (check-sat)
    "#,
    );
    assert_eq!(
        result[0], "sat",
        "as-array(f) = as-array(f) is trivially true"
    );
}

/// A SINGLETON element sort collapses an array sort to one inhabitant, whatever
/// the index sort is — `|Array I E| = |E|^|I|`, and `1^n = 1` even for infinite
/// `n`. So `(Array Int E)` with `|E| = 1` has exactly ONE inhabitant, a store
/// over it REPLACES that inhabitant, and `default(store(a,i,v)) = default(a)` is
/// FALSE there.
///
/// Regression: `sort_finite_cardinality` used to resolve the INDEX component
/// first and bail on it, so `Int` made this carrier report "unknown". The caller
/// fell through to the large-or-unknown arm and AY *asserted* the preservation
/// axiom, which agrees with the user's assertion here and yields a wrong `sat`.
/// Z3 5.0.0 answers `unsat`:
///
/// ```text
/// (assert (= (default (store a i 9)) (default a)))              => unsat
/// (assert (= (default (store a i 9)) 9)) (assert (= (default a) 5))  => sat
/// ```
#[test]
#[timeout(10_000)]
fn default_over_singleton_carrier_does_not_preserve_base_default() {
    let result = crate::common::solve_vec(
        r#"
        (declare-datatypes ((E 0)) (((C))))
        (declare-const i (Array Int E))
        (define-fun a () (Array (Array Int E) Int)
          ((as const (Array (Array Int E) Int)) 5))
        (assert (= (default (store a i 9)) (default a)))
        (check-sat)
    "#,
    );
    // Assert the SOUNDNESS property, not completeness: AY may legitimately answer
    // `unknown` here (it does today), but it must never publish `sat` for a
    // formula the oracle refutes. Before the cardinality-ordering fix it
    // answered exactly that.
    assert!(
        matches!(result[0].as_str(), "unsat" | "unknown"),
        "a store over a SINGLETON carrier replaces the sole element, so the base \
         default is NOT preserved; publishing `sat` here is a wrong answer \
         (z3 5.0.0 says unsat). got: {}",
        result[0]
    );
}

/// The positive half of the same shape: the store's default IS the stored value.
#[test]
#[timeout(10_000)]
fn default_over_singleton_carrier_is_the_stored_value() {
    let result = crate::common::solve_vec(
        r#"
        (declare-datatypes ((E 0)) (((C))))
        (declare-const i (Array Int E))
        (define-fun a () (Array (Array Int E) Int)
          ((as const (Array (Array Int E) Int)) 5))
        (assert (= (default (store a i 9)) 9))
        (assert (= (default a) 5))
        (check-sat)
    "#,
    );
    assert!(
        matches!(result[0].as_str(), "sat" | "unknown"),
        "the singleton carrier's sole element becomes the stored value, so this \
         is satisfiable; publishing `unsat` would be a wrong answer. got: {}",
        result[0]
    );
}
