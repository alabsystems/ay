// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #4877: AUFLIA solver returns SAT for contradictory
//! neq embedded deeply in and_many with foralls.
//!
//! The bug: when `neq(a, b)` is deeply nested inside `and(and(...))` combined
//! with `forall` quantifiers IN THE SAME AND NODE, the solver returns SAT
//! despite a contradicting `eq(a, b)` assertion.

#![allow(clippy::panic)]

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// Solve returning Ok(outputs) or Err(error_string).
/// Used for tests where model validation may catch a solver bug.
fn solve_tolerant(smt: &str) -> Result<Vec<String>, String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    exec.execute_all(&commands).map_err(|e| e.to_string())
}

/// #4877 Core: deeply nested neq(a,b) inside and with separate forall assertions
/// contradicts eq(a,b). This variant passes because FlattenAnd only needs to
/// handle the ground conjunction.
#[test]
#[timeout(60_000)]
fn test_auflia_deep_neq_unsat_4877() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-sort HeapObj 0)
        (declare-fun f (HeapObj) Int)
        (declare-fun g (HeapObj) Int)
        (declare-const a HeapObj)
        (declare-const b HeapObj)

        (assert (forall ((x HeapObj)) (>= (f x) 0)))
        (assert (forall ((x HeapObj)) (>= (g x) 0)))
        (assert (forall ((x HeapObj)) (<= (f x) 100)))
        (assert (forall ((x HeapObj)) (<= (g x) 100)))

        (assert (and
            (>= (f a) 0)
            (and
                (>= (g a) 0)
                (and
                    (>= (f b) 0)
                    (and
                        (>= (g b) 0)
                        (and
                            (<= (f a) 50)
                            (and
                                (<= (g a) 50)
                                (and
                                    (<= (f b) 50)
                                    (and
                                        (<= (g b) 50)
                                        (and
                                            (>= (+ (f a) (g a)) 10)
                                            (and
                                                (>= (+ (f b) (g b)) 10)
                                                (and
                                                    (<= (+ (f a) (f b)) 80)
                                                    (and
                                                        (<= (+ (g a) (g b)) 80)
                                                        (and
                                                            (>= (+ (f a) (g b)) 5)
                                                            (not (= a b))))))))))))))))

        (assert (= a b))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Bug #4877: deeply nested neq(a,b) inside and_many with foralls \
         must be detected as contradicting eq(a,b)"
    );
}

/// #4877 Exact verification-consumer pattern: foralls INSIDE the same and as the deeply nested neq.
///
/// This is the exact bug reproduction. The solver should return unsat.
#[test]
#[timeout(60_000)]
fn test_auflia_forall_in_same_and_as_deep_neq_4877() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-sort HeapObj 0)
        (declare-fun f (HeapObj) Int)
        (declare-fun g (HeapObj) Int)
        (declare-const a HeapObj)
        (declare-const b HeapObj)

        (assert (and
            (forall ((x HeapObj)) (>= (f x) 0))
            (and
                (forall ((x HeapObj)) (>= (g x) 0))
                (and
                    (forall ((x HeapObj)) (<= (f x) 100))
                    (and
                        (forall ((x HeapObj)) (<= (g x) 100))
                        (and
                            (>= (f a) 0)
                            (and
                                (>= (g a) 0)
                                (and
                                    (>= (f b) 0)
                                    (and
                                        (>= (g b) 0)
                                        (and
                                            (<= (f a) 50)
                                            (and
                                                (<= (g a) 50)
                                                (and
                                                    (<= (f b) 50)
                                                    (and
                                                        (<= (g b) 50)
                                                        (and
                                                            (>= (+ (f a) (g b)) 5)
                                                            (not (= a b))))))))))))))))

        (assert (= a b))

        (check-sat)
    "#;

    match solve_tolerant(smt) {
        Ok(outputs) => {
            assert_eq!(
                outputs,
                vec!["unsat"],
                "Bug #4877: verification-consumer-exact pattern must return unsat, got {outputs:?}"
            );
        }
        Err(e) => {
            panic!("Bug #4877 NOT FIXED: solver returned SAT (model validation caught it): {e}");
        }
    }
}

/// #4877 Variant: flat neq without deep nesting (baseline).
#[test]
#[timeout(60_000)]
fn test_auflia_flat_neq_unsat_4877() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-sort HeapObj 0)
        (declare-fun f (HeapObj) Int)
        (declare-const a HeapObj)
        (declare-const b HeapObj)

        (assert (forall ((x HeapObj)) (>= (f x) 0)))
        (assert (forall ((x HeapObj)) (<= (f x) 100)))

        (assert (>= (f a) 0))
        (assert (<= (f a) 50))
        (assert (>= (f b) 0))
        (assert (<= (f b) 50))
        (assert (not (= a b)))
        (assert (= a b))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Flat neq(a,b) with foralls must be UNSAT when eq(a,b) is also asserted"
    );
}

/// #4877 Variant: deeply nested neq without foralls (baseline).
#[test]
#[timeout(60_000)]
fn test_auflia_deep_neq_no_foralls_unsat_4877() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)

        (assert (and
            (>= (f a) 0)
            (and
                (>= (f b) 0)
                (and
                    (<= (f a) 50)
                    (and
                        (<= (f b) 50)
                        (and
                            (>= (+ (f a) (f b)) 10)
                            (and
                                (<= (+ (f a) (f b)) 80)
                                (not (= a b)))))))))

        (assert (= a b))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Deeply nested neq(a,b) without foralls must be UNSAT with eq(a,b)"
    );
}
