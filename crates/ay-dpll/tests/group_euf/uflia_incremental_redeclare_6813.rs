// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression for #6813: redeclaring Int constants after pop must not alias
//! stale incremental UFLIA state.

use ntest::timeout;

#[test]
#[timeout(10_000)]
fn test_uflia_redeclare_after_pop_remains_unsat_6813() {
    let smt = r#"
        (set-logic QF_UFLIA)
        (set-option :produce-models true)

        (push 1)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (not (= a b)))

        (push 1)
        (declare-fun c () Int)
        (assert (and (= a 0) (= b a) (= c 2)))
        (check-sat)
        (pop 1)
        (pop 1)

        (push 1)
        (declare-fun c () Int)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (and (= a 0) (= b a) (= c 2) (not (= a b))))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat", "unsat"]);
}
