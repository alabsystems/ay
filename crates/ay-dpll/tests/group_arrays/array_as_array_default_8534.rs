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

include!("array_as_array_default_8534/default_axioms.rs");

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
