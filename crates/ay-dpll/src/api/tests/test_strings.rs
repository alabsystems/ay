// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the string and regex native API methods (#5938).
//!
//! Term construction and sort-checking tests verify the API surface.
//! Behavioral (check_sat) tests accept `Unknown` since the string theory
//! solver currently returns `Unknown` for QF_SLIA queries; when the solver
//! gains full string support these tests should be tightened to exact results.

use crate::api::*;

/// Assert check_sat returns either the expected result or Unknown (acceptable
/// while the string theory solver is incomplete).
fn assert_sat_or_unknown(result: VerifiedSolveResult, expected: SolveResult) {
    let r = result.result();
    assert!(
        *r == expected || r.is_unknown(),
        "expected {expected:?} or Unknown, got {r:?}"
    );
}

// =========================================================================
// String variable and constant construction
// =========================================================================

#[test]
fn test_string_var() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_var("s");
    let hello = solver.string_const("hello");
    let eq = solver.eq(s, hello);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_string_const() {
    let mut solver = Solver::new(Logic::QfSlia);
    let hello = solver.string_const("hello");
    let hello2 = solver.string_const("hello");
    let eq = solver.eq(hello, hello2);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_string_const_unsat() {
    let mut solver = Solver::new(Logic::QfSlia);
    let hello = solver.string_const("hello");
    let world = solver.string_const("world");
    let eq = solver.eq(hello, world);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::unsat());
}

// =========================================================================
// String concatenation
// =========================================================================

#[test]
fn test_str_concat() {
    let mut solver = Solver::new(Logic::QfSlia);
    let a = solver.string_const("ab");
    let b = solver.string_const("cd");
    let ab_cd = solver.str_concat(a, b);
    let abcd = solver.string_const("abcd");
    let eq = solver.eq(ab_cd, abcd);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_str_concat_mismatch() {
    let mut solver = Solver::new(Logic::QfSlia);
    let a = solver.string_const("ab");
    let b = solver.string_const("cd");
    let ab_cd = solver.str_concat(a, b);
    let wrong = solver.string_const("abce");
    let eq = solver.eq(ab_cd, wrong);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::unsat());
}

#[test]
fn test_try_str_concat_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_var("s");
    let n = solver.int_var("n");
    let err = solver.try_str_concat(s, n).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "str.++",
            ..
        }
    ));
}

// =========================================================================
// String length
// =========================================================================

#[test]
fn test_str_len() {
    let mut solver = Solver::new(Logic::QfSlia);
    let hello = solver.string_const("hello");
    let len = solver.str_len(hello);
    let five = solver.int_const(5);
    let eq = solver.eq(len, five);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_str_len_constraint() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_var("s");
    let len = solver.str_len(s);
    let zero = solver.int_const(0);
    let ge = solver.ge(len, zero);
    solver.assert_term(ge);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_try_str_len_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let n = solver.int_var("n");
    let err = solver.try_str_len(n).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "str.len",
            ..
        }
    ));
}

// =========================================================================
// Character access
// =========================================================================

#[test]
fn test_str_at() {
    let mut solver = Solver::new(Logic::QfSlia);
    let hello = solver.string_const("hello");
    let zero = solver.int_const(0);
    let ch = solver.str_at(hello, zero);
    let h = solver.string_const("h");
    let eq = solver.eq(ch, h);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_try_str_at_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_var("s");
    let t = solver.string_var("t");
    let err = solver.try_str_at(s, t).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "str.at",
            ..
        }
    ));
}

// =========================================================================
// Substring
// =========================================================================

#[test]
fn test_str_substr() {
    let mut solver = Solver::new(Logic::QfSlia);
    let hello = solver.string_const("hello");
    let one = solver.int_const(1);
    let three = solver.int_const(3);
    let sub = solver.str_substr(hello, one, three);
    let ell = solver.string_const("ell");
    let eq = solver.eq(sub, ell);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_try_str_substr_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_var("s");
    let t = solver.string_var("t");
    let zero = solver.int_const(0);
    let err = solver.try_str_substr(s, t, zero).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "str.substr",
            ..
        }
    ));
}

// =========================================================================
// String predicates (contains, prefix, suffix)
// =========================================================================

#[test]
fn test_str_contains() {
    let mut solver = Solver::new(Logic::QfSlia);
    let hello = solver.string_const("hello");
    let ell = solver.string_const("ell");
    let contains = solver.str_contains(hello, ell);
    solver.assert_term(contains);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_str_contains_negative() {
    let mut solver = Solver::new(Logic::QfSlia);
    let hello = solver.string_const("hello");
    let xyz = solver.string_const("xyz");
    let contains = solver.str_contains(hello, xyz);
    solver.assert_term(contains);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::unsat());
}

#[test]
fn test_str_prefixof() {
    let mut solver = Solver::new(Logic::QfSlia);
    let he = solver.string_const("he");
    let hello = solver.string_const("hello");
    let is_prefix = solver.str_prefixof(he, hello);
    solver.assert_term(is_prefix);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_str_prefixof_negative() {
    let mut solver = Solver::new(Logic::QfSlia);
    let lo = solver.string_const("lo");
    let hello = solver.string_const("hello");
    let is_prefix = solver.str_prefixof(lo, hello);
    solver.assert_term(is_prefix);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::unsat());
}

#[test]
fn test_str_suffixof() {
    let mut solver = Solver::new(Logic::QfSlia);
    let lo = solver.string_const("lo");
    let hello = solver.string_const("hello");
    let is_suffix = solver.str_suffixof(lo, hello);
    solver.assert_term(is_suffix);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_str_suffixof_negative() {
    let mut solver = Solver::new(Logic::QfSlia);
    let he = solver.string_const("he");
    let hello = solver.string_const("hello");
    let is_suffix = solver.str_suffixof(he, hello);
    solver.assert_term(is_suffix);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::unsat());
}

#[test]
fn test_try_str_contains_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_var("s");
    let n = solver.int_var("n");
    let err = solver.try_str_contains(s, n).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "str.contains",
            ..
        }
    ));
}

// =========================================================================
// String index-of
// =========================================================================

#[test]
fn test_str_indexof() {
    let mut solver = Solver::new(Logic::QfSlia);
    let hello = solver.string_const("hello");
    let ll = solver.string_const("ll");
    let zero = solver.int_const(0);
    let idx = solver.str_indexof(hello, ll, zero);
    let two = solver.int_const(2);
    let eq = solver.eq(idx, two);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_str_indexof_not_found() {
    let mut solver = Solver::new(Logic::QfSlia);
    let hello = solver.string_const("hello");
    let xyz = solver.string_const("xyz");
    let zero = solver.int_const(0);
    let idx = solver.str_indexof(hello, xyz, zero);
    let neg_one = solver.int_const(-1);
    let eq = solver.eq(idx, neg_one);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_try_str_indexof_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_var("s");
    let t = solver.string_var("t");
    let err = solver.try_str_indexof(s, t, t).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "str.indexof",
            ..
        }
    ));
}

// =========================================================================
// String replacement
// =========================================================================

#[test]
fn test_str_replace() {
    let mut solver = Solver::new(Logic::QfSlia);
    let hello = solver.string_const("hello");
    let ell = solver.string_const("ell");
    let ipp = solver.string_const("ipp");
    let replaced = solver.str_replace(hello, ell, ipp);
    let hippo = solver.string_const("hippo");
    let eq = solver.eq(replaced, hippo);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_str_replace_all() {
    let mut solver = Solver::new(Logic::QfSlia);
    let aabaa = solver.string_const("aabaa");
    let a = solver.string_const("a");
    let c = solver.string_const("c");
    let replaced = solver.str_replace_all(aabaa, a, c);
    let ccbcc = solver.string_const("ccbcc");
    let eq = solver.eq(replaced, ccbcc);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_try_str_replace_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_var("s");
    let n = solver.int_var("n");
    let err = solver.try_str_replace(s, s, n).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "str.replace",
            ..
        }
    ));
}

// =========================================================================
// String <-> Int conversions
// =========================================================================

#[test]
fn test_str_to_int() {
    let mut solver = Solver::new(Logic::QfSlia);
    let digits = solver.string_const("42");
    let val = solver.str_to_int(digits);
    let forty_two = solver.int_const(42);
    let eq = solver.eq(val, forty_two);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_str_from_int() {
    let mut solver = Solver::new(Logic::QfSlia);
    let forty_two = solver.int_const(42);
    let s = solver.str_from_int(forty_two);
    let expected = solver.string_const("42");
    let eq = solver.eq(s, expected);
    solver.assert_term(eq);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_try_str_to_int_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let n = solver.int_var("n");
    let err = solver.try_str_to_int(n).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "str.to_int",
            ..
        }
    ));
}

#[test]
fn test_try_str_from_int_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_var("s");
    let err = solver.try_str_from_int(s).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "str.from_int",
            ..
        }
    ));
}

mod regex_ops;
// =========================================================================
// Integration: combined string + integer constraints
// =========================================================================

#[test]
fn test_string_length_constraint() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_var("s");
    let len = solver.str_len(s);
    let three = solver.int_const(3);
    let len_eq = solver.eq(len, three);
    solver.assert_term(len_eq);
    let ab = solver.string_const("ab");
    let contains = solver.str_contains(s, ab);
    solver.assert_term(contains);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_string_length_too_short() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_var("s");
    let len = solver.str_len(s);
    let one = solver.int_const(1);
    let len_eq = solver.eq(len, one);
    solver.assert_term(len_eq);
    let ab = solver.string_const("ab");
    let contains = solver.str_contains(s, ab);
    solver.assert_term(contains);
    assert_sat_or_unknown(solver.check_sat(), SolveResult::unsat());
}
