// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for QF_LIA timeout on 4-variable equality chain (#2767).
//!
//! The solver must handle equality chains like:
//!   pre:  self_a + self_b = 10
//!   body: result_a = self_a + 1, result_b = self_b - 1
//!   post: NOT(result_a + result_b = 10)
//!
//! This is trivially UNSAT: result_a + result_b = (self_a+1) + (self_b-1) = self_a + self_b = 10.
//! Z3 solves this instantly. AY was timing out due to insufficient equality propagation
//! through intermediate variables.

use ntest::timeout;

/// 4-variable equality chain: the core pattern from verification-consumer type invariant proofs.
#[test]
#[timeout(10_000)]
fn test_equality_chain_4var_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const self_a Int)
        (declare-const self_b Int)
        (declare-const result_a Int)
        (declare-const result_b Int)

        ; Pre: self_a + self_b = 10
        (assert (= (+ self_a self_b) 10))

        ; Body: result_a = self_a + 1, result_b = self_b - 1
        (assert (= result_a (+ self_a 1)))
        (assert (= result_b (- self_b 1)))

        ; Post: NOT(result_a + result_b = 10) — trivially UNSAT
        (assert (not (= (+ result_a result_b) 10)))

        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Same problem with inlined body — this already works (verifies the math is right).
#[test]
#[timeout(10_000)]
fn test_equality_chain_2var_inlined_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const self_a Int)
        (declare-const self_b Int)

        ; Pre: self_a + self_b = 10
        (assert (= (+ self_a self_b) 10))

        ; Post with inlined body: NOT((self_a + 1) + (self_b - 1) = 10)
        (assert (not (= (+ (+ self_a 1) (- self_b 1)) 10)))

        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// 3-variable variant: a = b, c = a + 1, NOT(c = b + 1)
#[test]
#[timeout(10_000)]
fn test_equality_chain_3var_transitive() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)

        (assert (= a b))
        (assert (= c (+ a 1)))
        (assert (not (= c (+ b 1))))

        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Incremental context: equality chain with push/pop followed by check-sat.
/// Exercises the incremental → non-incremental fallback for Int/Real equalities (#2767).
#[test]
#[timeout(10_000)]
fn test_equality_chain_incremental_fallback() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const self_a Int)
        (declare-const self_b Int)
        (declare-const result_a Int)
        (declare-const result_b Int)

        (assert (= (+ self_a self_b) 10))
        (assert (= result_a (+ self_a 1)))
        (assert (= result_b (- self_b 1)))

        (push 1)
        (assert (not (= (+ result_a result_b) 10)))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (= (+ result_a result_b) 10))
        (check-sat)
        (pop 1)
    "#;
    let output = crate::common::solve(smt);
    let lines: Vec<&str> = output
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    assert_eq!(lines, vec!["unsat", "sat"]);
}
