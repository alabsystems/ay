// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for issue #5848: Finite domain enumeration.
//!
//! Tests that quantifiers over finite-domain sorts (Bool, small BitVec) are
//! expanded into ground conjunctions/disjunctions rather than relying on
//! E-matching.

use ntest::timeout;

/// `(forall ((b Bool)) (or b (not b)))` is a tautology → sat.
#[test]
#[timeout(10000)]
fn test_forall_bool_tautology() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((b Bool)) (or b (not b))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "forall over Bool tautology should be sat"
    );
}

/// `(forall ((b Bool)) b)` means both true and false must hold → unsat.
#[test]
#[timeout(10000)]
fn test_forall_bool_unsat() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((b Bool)) b))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["unsat"],
        "forall ((b Bool)) b should be unsat"
    );
}

/// `(exists ((b Bool)) b)` — at least one Bool value satisfies `b` (true does) → sat.
/// This is also covered by Skolemization, but finite domain expansion gives an
/// explicit disjunction: `(or true false)` which simplifies to `true`.
#[test]
#[timeout(10000)]
fn test_exists_bool_sat() {
    let smt = r#"
        (set-logic ALL)
        (assert (exists ((b Bool)) b))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(results, vec!["sat"], "exists bool sat should work");
}

/// `(forall ((b Bool)) (=> b (> x 0)))` with `(> x 0)` declared.
/// Expanded: `(and (=> true (> x 0)) (=> false (> x 0)))`.
/// `(=> false anything)` is true, so this reduces to `(> x 0)` → sat with x=1.
#[test]
#[timeout(10000)]
fn test_forall_bool_with_free_var() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (forall ((b Bool)) (=> b (> x 0))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "forall bool with free var should be sat"
    );
}

/// Two Bool variables: `(forall ((a Bool) (b Bool)) (= (and a b) (and b a)))`.
/// Commutativity of and — 4 combinations, all true → sat.
#[test]
#[timeout(10000)]
fn test_forall_two_bools() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((a Bool) (b Bool)) (= (and a b) (and b a))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "forall two bools commutativity should be sat"
    );
}

/// BitVec(1): `(forall ((x (_ BitVec 1))) (bvuge x #b0))` — all BV1 >= 0 → sat.
#[test]
#[timeout(10000)]
fn test_forall_bv1_sat() {
    let smt = r#"
        (set-logic QF_BV)
        (assert (forall ((x (_ BitVec 1))) (bvuge x #b0)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(results, vec!["sat"], "forall bv1 >= 0 should be sat");
}

// ---- Bounded integer quantifier tests (#5848) ----

/// `(forall ((i Int)) (=> (and (<= 0 i) (<= i 2)) (< i 10)))` → sat.
/// All values 0,1,2 satisfy (< i 10).
#[test]
#[timeout(10000)]
fn test_forall_bounded_int_sat() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((i Int)) (=> (and (<= 0 i) (<= i 2)) (< i 10))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "forall bounded int [0,2] with (< i 10) should be sat"
    );
}

/// `(forall ((i Int)) (=> (and (<= 0 i) (<= i 2)) (> i 1)))` → unsat.
/// Fails for i=0 and i=1 (not > 1).
#[test]
#[timeout(10000)]
fn test_forall_bounded_int_unsat() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((i Int)) (=> (and (<= 0 i) (<= i 2)) (> i 1))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["unsat"],
        "forall bounded int [0,2] with (> i 1) should be unsat — fails for i=0"
    );
}

/// `(exists ((i Int)) (and (<= 0 i) (<= i 5) (= i 3)))` → sat.
/// Value 3 is in range [0,5] and equals 3.
#[test]
#[timeout(10000)]
fn test_exists_bounded_int_sat() {
    let smt = r#"
        (set-logic ALL)
        (assert (exists ((i Int)) (and (<= 0 i) (<= i 5) (= i 3))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "exists bounded int with (= i 3) in [0,5] should be sat"
    );
}

/// Bounded int with strict less-than: `(forall ((i Int)) (=> (and (<= 0 i) (< i 3)) (< i 10)))`.
/// Range is [0,2], all < 10.
#[test]
#[timeout(10000)]
fn test_forall_bounded_int_strict_lt() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((i Int)) (=> (and (<= 0 i) (< i 3)) (< i 10))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "forall bounded int [0,2] with (< i 10) should be sat"
    );
}

/// Unbounded Int (no guard) → falls back, should still work via E-matching/CEGQI.
/// `(forall ((x Int)) (= x 5))` → unsat (can't hold for all integers).
#[test]
#[timeout(10000)]
fn test_forall_unbounded_int_fallback() {
    let smt = r#"
        (set-logic ALL)
        (assert (forall ((x Int)) (= x 5)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        results == vec!["unsat"] || results == vec!["unknown"],
        "forall unbounded int (= x 5) should be unsat or unknown via E-matching/CEGQI, got: {results:?}"
    );
}

/// Bounded int with free variable interaction:
/// `(forall ((i Int)) (=> (and (<= 0 i) (<= i 3)) (<= i x)))` with `(declare-fun x () Int)`.
/// This is satisfiable: x >= 3 works.
#[test]
#[timeout(10000)]
fn test_forall_bounded_int_with_free_var() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun x () Int)
        (assert (forall ((i Int)) (=> (and (<= 0 i) (<= i 3)) (<= i x))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert_eq!(
        results,
        vec!["sat"],
        "forall bounded int [0,3] with (<= i x) should be sat (x=3)"
    );
}
