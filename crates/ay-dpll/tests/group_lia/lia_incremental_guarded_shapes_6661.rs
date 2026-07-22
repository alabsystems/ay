// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for #6661: LIA incremental path handling of guarded formula shapes.
//!
//! Verifies that `solve_lia_incremental` correctly handles formulas containing
//! int mod/div by constant and int-real equality substitution in push/pop mode.
//! Previously these shapes bailed to the legacy split-loop path; now the
//! incremental path preprocesses per check-sat with fresh state.

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

/// Incremental push/pop with mod/div by constant assertions.
/// Each scope adds mod/div constraints that require preprocessing (mod/div
/// elimination) before the LIA solver can handle them.
#[test]
#[timeout(10_000)]
fn test_incremental_lia_mod_div_push_pop() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (assert (<= x 20))
        (push 1)
        (assert (= (mod x 3) 0))
        (assert (= (div x 3) 2))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= (mod x 5) 1))
        (check-sat)
        (pop 1)
    "#;
    // Scope 1: div x 3 = 2 → x in {6,7,8}, mod x 3 = 0 → x divisible by 3 → x=6: sat
    // Scope 2: mod x 5 = 1 → x in {1,6,11,16}, all in [0,20]: sat
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat"]);
}

/// Incremental push/pop with int-real equality substitution.
/// The equality `y = x + 1` triggers variable substitution preprocessing.
#[test]
#[timeout(10_000)]
fn test_incremental_lia_eq_subst_push_pop() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= y (+ x 1)))
        (push 1)
        (assert (>= y 5))
        (assert (<= x 10))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (< y 0))
        (assert (> x 0))
        (check-sat)
        (pop 1)
    "#;
    // Scope 1: y=x+1, y>=5 → x>=4, x<=10: sat
    // Scope 2: y=x+1, y<0 → x<-1, but x>0: unsat
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "unsat"]);
}

/// Mod constraint followed by pop and a simple constraint.
/// Tests that preprocessing artifacts from mod/div elimination don't leak
/// across pop boundaries.
#[test]
#[timeout(10_000)]
fn test_incremental_lia_mod_no_leak_after_pop() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (assert (<= x 100))
        (push 1)
        (assert (= (mod x 7) 3))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= x 5))
        (check-sat)
        (pop 1)
    "#;
    // Scope 1: mod x 7 = 3, 0<=x<=100 → x in {3,10,17,...,94}: sat
    // Scope 2: x = 5, 0<=x<=100: sat (mod constraint doesn't leak)
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["sat", "sat"]);
}

/// Equality substitution with contradictory scoped constraints.
/// Verifies UNSAT detection works correctly in the preprocessed incremental path.
#[test]
#[timeout(10_000)]
fn test_incremental_lia_eq_subst_unsat_scope() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const a Int)
        (declare-const b Int)
        (assert (= b (+ a 10)))
        (push 1)
        (assert (>= b 20))
        (assert (< a 5))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (< b 5))
        (assert (> a 0))
        (check-sat)
        (pop 1)
    "#;
    // Scope 1: b=a+10, b>=20 → a>=10, a<5: unsat
    // Scope 2: b=a+10, b<5 → a<-5, a>0: unsat
    let output = crate::common::solve(smt);
    assert_eq!(results(&output), vec!["unsat", "unsat"]);
}
