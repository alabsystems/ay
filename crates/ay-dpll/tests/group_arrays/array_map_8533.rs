// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for map[f] array operation (#8533).
//!
//! Tests the select-map axiom:
//!   select(map[f](a1,...,an), i) = f(select(a1,i),...,select(an,i))
//! and the Z3 5.0.0 default-map axiom:
//!   default(map[f](a1,...,an)) = f(default(a1),...,default(an))
//!
//! The eager rewrite in mk_select handles the syntactic case.
//! The theory solver check_select_map handles equality-graph-induced cases.

use crate::common::{sat_result, solve};

/// `default` distributes through `map` using the mapped declaration.  This is
/// a separate Z3 array-theory axiom from the pointwise select rule.
#[test]
fn test_array_map_declared_function_default_unsat() {
    let output = solve(
        r#"
        (set-logic ALL)
        (declare-fun f (Int) Int)
        (declare-const a (Array Bool Int))
        (assert (distinct (default ((_ map f) a)) (f (default a))))
        (check-sat)
    "#,
    );
    assert_eq!(
        sat_result(&output),
        Some("unsat"),
        "default(map[f](a)) must equal f(default(a))"
    );
}

/// Basic map[f] with unary function: the eager rewrite at term construction
/// should rewrite `select(map[inc](a), 0)` to `inc(select(a, 0))`.
/// With `select(a, 0) = 5` and `inc(5) = 6`, the formula is satisfiable.
#[test]
fn test_array_map_unary_sat() {
    let output = solve(
        r#"
        (set-logic QF_ALIA)
        (declare-fun inc (Int) Int)
        (declare-const a (Array Int Int))
        (assert (= (select a 0) 5))
        (assert (= (inc 5) 6))
        (assert (= (select ((_ map inc) a) 0) 6))
        (check-sat)
    "#,
    );
    assert_eq!(
        sat_result(&output),
        Some("sat"),
        "map[inc] with consistent function values should be SAT"
    );
}

/// map[f] with unary function, inconsistent: the eager rewrite should
/// produce inc(select(a, 0)) which must equal 6, but inc(5) = 7.
#[test]
fn test_array_map_unary_unsat() {
    let output = solve(
        r#"
        (set-logic QF_ALIA)
        (declare-fun inc (Int) Int)
        (declare-const a (Array Int Int))
        (assert (= (select a 0) 5))
        (assert (= (inc 5) 7))
        (assert (= (select ((_ map inc) a) 0) 6))
        (check-sat)
    "#,
    );
    assert_eq!(
        sat_result(&output),
        Some("unsat"),
        "map[inc] with inconsistent function values should be UNSAT"
    );
}

/// map[f] with binary function: `select(map[f](a, b), i) = f(select(a, i), select(b, i))`
#[test]
fn test_array_map_binary_sat() {
    let output = solve(
        r#"
        (set-logic QF_ALIA)
        (declare-fun f (Int Int) Int)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= (select a 0) 3))
        (assert (= (select b 0) 4))
        (assert (= (f 3 4) 7))
        (assert (= (select ((_ map f) a b) 0) 7))
        (check-sat)
    "#,
    );
    assert_eq!(
        sat_result(&output),
        Some("sat"),
        "map[f] with binary function and consistent values should be SAT"
    );
}

/// map[f] with binary function, inconsistent: f(3,4) = 7 but select(map[f](a,b), 0) = 8.
#[test]
fn test_array_map_binary_unsat() {
    let output = solve(
        r#"
        (set-logic QF_ALIA)
        (declare-fun f (Int Int) Int)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= (select a 0) 3))
        (assert (= (select b 0) 4))
        (assert (= (f 3 4) 7))
        (assert (= (select ((_ map f) a b) 0) 8))
        (check-sat)
    "#,
    );
    assert_eq!(
        sat_result(&output),
        Some("unsat"),
        "map[f] with binary function and inconsistent values should be UNSAT"
    );
}

/// Set union via map[or]: s1 union s2 at index i should be (or (s1 i) (s2 i)).
#[test]
fn test_array_map_set_union() {
    let output = solve(
        r#"
        (set-logic QF_ALIA)
        (declare-fun or (Bool Bool) Bool)
        (declare-const s1 (Array Int Bool))
        (declare-const s2 (Array Int Bool))
        (assert (select s1 5))
        (assert (not (select s2 5)))
        (assert (select ((_ map or) s1 s2) 5))
        (check-sat)
    "#,
    );
    assert_eq!(
        sat_result(&output),
        Some("sat"),
        "set union via map[or] should be SAT when s1 contains element"
    );
}

/// Set intersection via map[and]:
/// s1 has 5, s2 does not have 5. Intersection at 5 should be false.
#[test]
fn test_array_map_set_intersection_unsat() {
    let output = solve(
        r#"
        (set-logic QF_ALIA)
        (declare-fun and (Bool Bool) Bool)
        (declare-const s1 (Array Int Bool))
        (declare-const s2 (Array Int Bool))
        (assert (= (and true false) false))
        (assert (= (and false true) false))
        (assert (= (and true true) true))
        (assert (= (and false false) false))
        (assert (select s1 5))
        (assert (not (select s2 5)))
        (assert (select ((_ map and) s1 s2) 5))
        (check-sat)
    "#,
    );
    assert_eq!(
        sat_result(&output),
        Some("unsat"),
        "set intersection via map[and] should be UNSAT when one set lacks element"
    );
}

/// map[f] sort correctness: map[f: Int -> Bool](a: Array Int Int) should produce
/// Array Int Bool. Selecting from it should yield a Bool.
#[test]
fn test_array_map_sort_change() {
    let output = solve(
        r#"
        (set-logic QF_ALIA)
        (declare-fun is_positive (Int) Bool)
        (declare-const a (Array Int Int))
        (assert (= (select a 0) 42))
        (assert (= (is_positive 42) true))
        (assert (select ((_ map is_positive) a) 0))
        (check-sat)
    "#,
    );
    assert_eq!(
        sat_result(&output),
        Some("sat"),
        "map[f] changing element sort from Int to Bool should work correctly"
    );
}

/// Multiple select indices on a mapped array: the eager rewrite should
/// handle each index independently.
#[test]
fn test_array_map_multiple_indices() {
    let output = solve(
        r#"
        (set-logic QF_ALIA)
        (declare-fun double (Int) Int)
        (declare-const a (Array Int Int))
        (assert (= (select a 0) 3))
        (assert (= (select a 1) 5))
        (assert (= (double 3) 6))
        (assert (= (double 5) 10))
        (assert (= (select ((_ map double) a) 0) 6))
        (assert (= (select ((_ map double) a) 1) 10))
        (check-sat)
    "#,
    );
    assert_eq!(
        sat_result(&output),
        Some("sat"),
        "map[double] at multiple indices should be SAT"
    );
}

/// Chained map: map[g](map[f](a)) should compose as g(f(select(a, i))).
#[test]
fn test_array_map_chained() {
    let output = solve(
        r#"
        (set-logic QF_ALIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const a (Array Int Int))
        (assert (= (select a 0) 1))
        (assert (= (f 1) 2))
        (assert (= (g 2) 3))
        (assert (= (select ((_ map g) ((_ map f) a)) 0) 3))
        (check-sat)
    "#,
    );
    assert_eq!(
        sat_result(&output),
        Some("sat"),
        "chained map[g](map[f](a)) should compose correctly"
    );
}

/// Map on const-array: select(map[f](const-array(v)), i) = f(v).
#[test]
fn test_array_map_const_array() {
    let output = solve(
        r#"
        (set-logic QF_ALIA)
        (declare-fun negate (Int) Int)
        (assert (= (negate 42) (- 42)))
        (declare-const i Int)
        (assert (= (select ((_ map negate) ((as const (Array Int Int)) 42)) i) (- 42)))
        (check-sat)
    "#,
    );
    assert_eq!(
        sat_result(&output),
        Some("sat"),
        "map[negate] on const-array(42) should give negate(42) at any index"
    );
}
