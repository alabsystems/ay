// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Tests for AUFLIA incremental push/pop correctness.
//!
//! AUFLIA (Arrays, Uninterpreted Functions, Linear Integer Arithmetic) is the
//! primary logic used by verification-consumer for separation logic verification. These tests
//! cover the combined theory solver's incremental behavior with arrays.
//!
//! Key invariant: array stores and function equalities asserted inside a push
//! scope must not leak after pop. The Nelson-Oppen combination loop must
//! properly handle scope restoration for all three theories.

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

/// Basic push/pop: scoped array store must not leak.
/// After pop, the array should revert to its pre-push state.
#[test]
#[timeout(15_000)]
fn test_auflia_push_pop_array_store_no_leak() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)

        ; Base: select(a, 0) = 42
        (assert (= (select a 0) 42))
        (check-sat)

        ; Push: store different value at index 0
        (push 1)
        (assert (= (select a 0) 99))
        (check-sat)
        (pop 1)

        ; After pop: only original constraint survives
        ; select(a, 0) = 42 is consistent
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    let r = results(&output);
    assert_eq!(r[0], "sat", "Base: select(a,0)=42 is SAT");
    // Second check-sat: 42=99 contradiction => UNSAT
    assert_eq!(
        r[1], "unsat",
        "Push: select(a,0)=42 AND select(a,0)=99 is UNSAT"
    );
    assert_eq!(
        r[2], "sat",
        "After pop: only select(a,0)=42 survives => SAT"
    );
}

/// Array with UF: function applied to array select inside push scope.
/// Tests that congruence closure + array reasoning doesn't leak.
#[test]
#[timeout(15_000)]
fn test_auflia_push_pop_uf_over_array() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (declare-fun f (Int) Int)

        ; Base: f(select(a, 0)) = 10
        (assert (= (f (select a 0)) 10))
        (check-sat)

        ; Push: f(select(a, 0)) != 10 => UNSAT with base
        (push 1)
        (assert (not (= (f (select a 0)) 10)))
        (check-sat)
        (pop 1)

        ; After pop: base constraint survives => SAT
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    let r = results(&output);
    assert_eq!(r[0], "sat");
    assert_eq!(r[1], "unsat");
    assert_eq!(r[2], "sat");
}

/// Multi-cycle push/pop with arithmetic over array selects.
/// Tests that LIA reasoning over array-selected values is properly scoped.
#[test]
#[timeout(15_000)]
fn test_auflia_multi_cycle_arithmetic_over_arrays() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))

        ; Base: select(a, 0) >= 0
        (assert (>= (select a 0) 0))

        ; Cycle 1: add upper bound
        (push 1)
        (assert (<= (select a 0) 5))
        (assert (> (select a 0) 10))
        (check-sat)
        (pop 1)

        ; Cycle 2: different constraint
        (push 1)
        (assert (= (select a 0) 3))
        (check-sat)
        (pop 1)

        ; After both cycles: only base constraint
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    let r = results(&output);
    // Cycle 1: select(a,0) >= 0 AND <= 5 AND > 10 => UNSAT
    assert_eq!(r[0], "unsat", "Cycle 1: contradictory bounds");
    // Cycle 2: select(a,0) >= 0 AND = 3 => SAT
    assert_eq!(r[1], "sat", "Cycle 2: consistent");
    // After: select(a,0) >= 0 => SAT (#6191 fixed: LIA model resolves select values)
    assert_eq!(r[2], "sat", "After cycles: base only => SAT");
}

/// Nested push/pop with arrays and distinct constraints.
/// Tests the pattern used by verification-consumer for separation logic heap encoding.
#[test]
#[timeout(15_000)]
fn test_auflia_nested_push_pop_distinct() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-const heap (Array Int Int))
        (declare-const loc1 Int)
        (declare-const loc2 Int)

        ; Base: two distinct locations
        (assert (distinct loc1 loc2))
        (assert (>= loc1 0))
        (assert (>= loc2 0))

        ; Outer push: heap[loc1] = 10
        (push 1)
        (assert (= (select heap loc1) 10))

        ; Inner push: heap[loc2] = 20
        (push 1)
        (assert (= (select heap loc2) 20))
        (check-sat)
        (pop 1)

        ; After inner pop: only heap[loc1] = 10 + base
        (check-sat)
        (pop 1)

        ; After outer pop: only base (distinct, non-negative)
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    let r = results(&output);
    assert_eq!(
        r[0], "sat",
        "Inner: heap[loc1]=10 AND heap[loc2]=20 AND distinct => SAT"
    );
    assert_eq!(
        r[1], "sat",
        "After inner pop: heap[loc1]=10 AND distinct => SAT"
    );
    assert_eq!(r[2], "sat", "After outer pop: distinct locs => SAT");
}

/// Global assertion survival after push/pop.
/// Ensures assertions at scope 0 persist through push/pop cycles.
#[test]
#[timeout(15_000)]
fn test_auflia_global_assertion_survival() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))

        ; Global: select(a, 0) = 1 AND select(a, 1) = 2
        (assert (= (select a 0) 1))
        (assert (= (select a 1) 2))

        ; Push/pop cycle
        (push 1)
        (assert (= (select a 2) 3))
        (check-sat)
        (pop 1)

        ; Verify globals survived: select(a, 0) + select(a, 1) = 3
        (push 1)
        (assert (= (+ (select a 0) (select a 1)) 3))
        (check-sat)
        (pop 1)

        ; Verify globals: select(a, 0) + select(a, 1) = 4 => UNSAT
        (push 1)
        (assert (= (+ (select a 0) (select a 1)) 4))
        (check-sat)
        (pop 1)
    "#;
    let output = crate::common::solve(smt);
    let r = results(&output);
    assert_eq!(r[0], "sat", "Scoped: a[0]=1, a[1]=2, a[2]=3 => SAT");
    assert_eq!(r[1], "sat", "Globals survived: a[0]+a[1]=1+2=3 => SAT");
    assert_eq!(r[2], "unsat", "Globals survived: a[0]+a[1]=1+2!=4 => UNSAT");
}
