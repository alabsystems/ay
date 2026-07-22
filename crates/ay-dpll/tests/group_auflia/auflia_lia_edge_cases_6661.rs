// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regressions for #6661 on combined AUFLIA paths.
//!
//! Pure QF_LIA already handles constant mod/div and equality substitution
//! natively. These tests pin the remaining combined-theory requirement:
//! arithmetic equalities discovered by LIA must still drive EUF/array
//! congruence in AUFLIA formulas.

use ntest::timeout;

#[test]
#[timeout(60_000)]
fn test_auflia_mod_div_drives_array_index_congruence_6661() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (assert (= (mod x 5) 0))
        (assert (= (div x 5) 3))
        (assert (not (= (select a x) (select a 15))))
        (check-sat)
    "#;
    let output = crate::common::solve_vec(smt);
    assert_eq!(
        output,
        vec!["unsat"],
        "LIA must expose x = 15 to EUF/arrays so select(a,x) and select(a,15) are congruent"
    );
}

#[test]
#[timeout(60_000)]
fn test_auflia_equality_substitution_drives_array_index_congruence_6661() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (declare-const y Int)
        (assert (= y (+ x 1)))
        (assert (= x 4))
        (assert (= (select a y) 7))
        (assert (not (= (select a 5) 7)))
        (check-sat)
    "#;
    let output = crate::common::solve_vec(smt);
    assert_eq!(
        output,
        vec!["unsat"],
        "equality substitution facts must still reach array congruence on AUFLIA"
    );
}
