// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regular-expression API regressions.

use super::*;

// =========================================================================
// Regex operations
// =========================================================================

#[test]
fn test_str_to_re_and_in_re() {
    let mut solver = Solver::new(Logic::QfSlia);
    let hello = solver.string_const("hello");
    let re_hello = solver.str_to_re(hello);
    let s = solver.string_var("s");
    let in_re = solver.str_in_re(s, re_hello);
    solver.assert_term(in_re);
    let eq = solver.eq(s, hello);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_re_star() {
    let mut solver = Solver::new(Logic::QfSlia);
    let a = solver.string_const("a");
    let re_a = solver.str_to_re(a);
    let re_a_star = solver.re_star(re_a);
    let aaa = solver.string_const("aaa");
    let in_re = solver.str_in_re(aaa, re_a_star);
    solver.assert_term(in_re);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_re_plus() {
    let mut solver = Solver::new(Logic::QfSlia);
    let a = solver.string_const("a");
    let re_a = solver.str_to_re(a);
    let re_a_plus = solver.re_plus(re_a);
    let empty = solver.string_const("");
    let in_re = solver.str_in_re(empty, re_a_plus);
    solver.assert_term(in_re);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::unsat());
}

#[test]
fn test_re_union() {
    let mut solver = Solver::new(Logic::QfSlia);
    let a = solver.string_const("a");
    let b = solver.string_const("b");
    let re_a = solver.str_to_re(a);
    let re_b = solver.str_to_re(b);
    let re_ab = solver.re_union(re_a, re_b);
    let s = solver.string_var("s");
    let in_re = solver.str_in_re(s, re_ab);
    solver.assert_term(in_re);
    let eq_a = solver.eq(s, a);
    solver.assert_term(eq_a);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_re_concat() {
    let mut solver = Solver::new(Logic::QfSlia);
    let a = solver.string_const("a");
    let b = solver.string_const("b");
    let re_a = solver.str_to_re(a);
    let re_b = solver.str_to_re(b);
    let re_ab = solver.re_concat(re_a, re_b);
    let ab = solver.string_const("ab");
    let in_re = solver.str_in_re(ab, re_ab);
    solver.assert_term(in_re);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_try_str_to_re_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let n = solver.int_var("n");
    let err = solver.try_str_to_re(n).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "str.to_re",
            ..
        }
    ));
}

#[test]
fn test_try_str_in_re_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let n = solver.int_var("n");
    let a = solver.string_const("a");
    let re_a = solver.str_to_re(a);
    let err = solver.try_str_in_re(n, re_a).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "str.in_re",
            ..
        }
    ));
}

#[test]
fn test_try_re_star_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_var("s");
    let err = solver.try_re_star(s).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "re.*",
            ..
        }
    ));
}

#[test]
fn test_try_re_union_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_var("s");
    let a = solver.string_const("a");
    let re_a = solver.str_to_re(a);
    let err = solver.try_re_union(s, re_a).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "re.union",
            ..
        }
    ));
}
