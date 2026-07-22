// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the String/BV bridge API (#8333).
//!
//! These tests verify term construction and sort checking. Behavioral tests
//! accept `Unknown` since the combined String+BV theory may not fully solve
//! all queries; when full theory combination is supported, tighten to exact
//! results.

use crate::api::*;

/// Assert check_sat returns either the expected result or Unknown.
fn assert_sat_or_unknown(result: VerifiedSolveResult, expected: SolveResult) {
    let r = result.result();
    assert!(
        *r == expected || r.is_unknown(),
        "expected {expected:?} or Unknown, got {r:?}"
    );
}

// =========================================================================
// string_to_bv: term construction and sort checking
// =========================================================================

#[test]
fn test_string_to_bv_concrete() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_const("42");
    let bv = solver
        .try_string_to_bv(s, 32)
        .expect("string_to_bv should succeed");
    let expected = solver.bv_const(42, 32);
    let eq = solver.try_eq(bv, expected).expect("same sort");
    solver.try_assert_term(eq).expect("bool assertion");
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_string_to_bv_zero() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_const("0");
    let bv = solver
        .try_string_to_bv(s, 8)
        .expect("string_to_bv should succeed");
    let expected = solver.bv_const(0, 8);
    let eq = solver.try_eq(bv, expected).expect("same sort");
    solver.try_assert_term(eq).expect("bool assertion");
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_string_to_bv_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let n = solver.int_var("n");
    let err = solver.try_string_to_bv(n, 32).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "string_to_bv",
            ..
        }
    ));
}

#[test]
fn test_string_to_bv_zero_width_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_const("1");
    let err = solver.try_string_to_bv(s, 0).unwrap_err();
    assert!(matches!(
        err,
        SolverError::InvalidArgument {
            operation: "string_to_bv",
            ..
        }
    ));
}

// =========================================================================
// bv_to_string: term construction and sort checking
// =========================================================================

#[test]
fn test_bv_to_string_concrete() {
    let mut solver = Solver::new(Logic::QfSlia);
    let bv = solver.bv_const(42, 32);
    let s = solver
        .try_bv_to_string(bv)
        .expect("bv_to_string should succeed");
    let expected = solver.string_const("42");
    let eq = solver.try_eq(s, expected).expect("same sort");
    solver.try_assert_term(eq).expect("bool assertion");
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_bv_to_string_zero() {
    let mut solver = Solver::new(Logic::QfSlia);
    let bv = solver.bv_const(0, 8);
    let s = solver
        .try_bv_to_string(bv)
        .expect("bv_to_string should succeed");
    let expected = solver.string_const("0");
    let eq = solver.try_eq(s, expected).expect("same sort");
    solver.try_assert_term(eq).expect("bool assertion");
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_bv_to_string_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let n = solver.int_var("n");
    let err = solver.try_bv_to_string(n).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "bv_to_string",
            ..
        }
    ));
}

#[test]
fn test_bv_to_string_signed() {
    let mut solver = Solver::new(Logic::QfSlia);
    let bv = solver.bv_const(255, 8); // unsigned 255, signed -1
    let s = solver
        .try_bv_to_string(bv)
        .expect("unsigned bv_to_string should succeed");
    let expected = solver.string_const("255");
    let eq = solver.try_eq(s, expected).expect("same sort");
    solver.try_assert_term(eq).expect("bool assertion");
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

// =========================================================================
// Roundtrip: string -> bv -> string and bv -> string -> bv
// =========================================================================

#[test]
fn test_roundtrip_string_bv_string() {
    // "42" -> bv32 -> should equal "42" (unsigned interpretation)
    let mut solver = Solver::new(Logic::QfSlia);
    let original = solver.string_const("42");
    let bv = solver.try_string_to_bv(original, 32).expect("string_to_bv");
    let roundtripped = solver.try_bv_to_string(bv).expect("bv_to_string");
    let eq = solver.try_eq(roundtripped, original).expect("same sort");
    solver.try_assert_term(eq).expect("bool assertion");
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_roundtrip_bv_string_bv() {
    // bv32(100) -> "100" -> bv32 should equal bv32(100)
    let mut solver = Solver::new(Logic::QfSlia);
    let original = solver.bv_const(100, 32);
    let s = solver.try_bv_to_string(original).expect("bv_to_string");
    let roundtripped = solver.try_string_to_bv(s, 32).expect("string_to_bv");
    let eq = solver.try_eq(roundtripped, original).expect("same sort");
    solver.try_assert_term(eq).expect("bool assertion");
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

// =========================================================================
// string_length_bv: term construction and sort checking
// =========================================================================

#[test]
fn test_string_length_bv() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_const("hello");
    let len_bv = solver
        .try_string_length_bv(s)
        .expect("string_length_bv should succeed");
    let five_bv = solver.bv_const(5, 32);
    let eq = solver.try_eq(len_bv, five_bv).expect("same sort");
    solver.try_assert_term(eq).expect("bool assertion");
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_string_length_bv_empty() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_const("");
    let len_bv = solver
        .try_string_length_bv(s)
        .expect("string_length_bv should succeed");
    let zero_bv = solver.bv_const(0, 32);
    let eq = solver.try_eq(len_bv, zero_bv).expect("same sort");
    solver.try_assert_term(eq).expect("bool assertion");
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_string_length_bv_sort_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let n = solver.int_var("n");
    let err = solver.try_string_length_bv(n).unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "string_length_bv",
            ..
        }
    ));
}

#[test]
fn test_string_length_bv_width_16() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_const("abc");
    let len_bv = solver
        .try_string_length_bv_width(s, 16)
        .expect("string_length_bv_width should succeed");
    let three_bv = solver.bv_const(3, 16);
    let eq = solver.try_eq(len_bv, three_bv).expect("same sort");
    solver.try_assert_term(eq).expect("bool assertion");
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_string_length_bv_width_zero_error() {
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_const("x");
    let err = solver.try_string_length_bv_width(s, 0).unwrap_err();
    assert!(matches!(
        err,
        SolverError::InvalidArgument {
            operation: "string_length_bv_width",
            ..
        }
    ));
}

// =========================================================================
// format_string_vuln_check: term construction and sort checking
// =========================================================================

#[test]
fn test_format_vuln_check_small_buffer_overflow() {
    // "hello " (6 chars) + user_input. If user_input has any content,
    // total > 6, so with buffer of 6 bytes, overflow is possible.
    let mut solver = Solver::new(Logic::QfSlia);
    let fmt = solver.string_const("hello ");
    let arg = solver.string_var("user_input");
    let buf = solver.bv_const(6, 32);

    // Constrain user_input to be non-empty
    let arg_len = solver.try_str_len(arg).expect("str.len");
    let one = solver.int_const(1);
    let len_ge_1 = solver.try_ge(arg_len, one).expect("ge");
    solver.try_assert_term(len_ge_1).expect("assert");

    let overflow = solver
        .try_format_string_vuln_check(fmt, &[arg], buf)
        .expect("format_string_vuln_check should succeed");
    solver.try_assert_term(overflow).expect("assert overflow");
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_format_vuln_check_large_buffer_no_overflow() {
    // "hi" (2 chars) + "!" (1 char) = 3. Buffer = 100. No overflow.
    let mut solver = Solver::new(Logic::QfSlia);
    let fmt = solver.string_const("hi");
    let arg = solver.string_const("!");
    let buf = solver.bv_const(100, 32);
    let overflow = solver
        .try_format_string_vuln_check(fmt, &[arg], buf)
        .expect("format_string_vuln_check should succeed");
    solver.try_assert_term(overflow).expect("assert overflow");
    // Total is 3, buffer is 100 => no overflow => should be UNSAT
    assert_sat_or_unknown(solver.check_sat(), SolveResult::unsat());
}

#[test]
fn test_format_vuln_check_sort_error_fmt_not_string() {
    let mut solver = Solver::new(Logic::QfSlia);
    let n = solver.int_var("n");
    let buf = solver.bv_const(100, 32);
    let err = solver
        .try_format_string_vuln_check(n, &[], buf)
        .unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "format_string_vuln_check (fmt)",
            ..
        }
    ));
}

#[test]
fn test_format_vuln_check_sort_error_arg_not_string_or_bv() {
    let mut solver = Solver::new(Logic::QfSlia);
    let fmt = solver.string_const("test");
    let n = solver.int_var("n");
    let buf = solver.bv_const(100, 32);
    let err = solver
        .try_format_string_vuln_check(fmt, &[n], buf)
        .unwrap_err();
    assert!(matches!(
        err,
        SolverError::SortMismatch {
            operation: "format_string_vuln_check",
            ..
        }
    ));
}

#[test]
fn test_format_vuln_check_sort_error_buf_not_bv32() {
    let mut solver = Solver::new(Logic::QfSlia);
    let fmt = solver.string_const("test");
    let buf = solver.bv_const(100, 16); // wrong width
    let err = solver
        .try_format_string_vuln_check(fmt, &[], buf)
        .unwrap_err();
    assert!(matches!(
        err,
        SolverError::InvalidArgument {
            operation: "format_string_vuln_check",
            ..
        }
    ));
}

#[test]
fn test_format_vuln_check_no_args() {
    // Just format string "abc" with buffer of 2 => overflow
    let mut solver = Solver::new(Logic::QfSlia);
    let fmt = solver.string_const("abc");
    let buf = solver.bv_const(2, 32);
    let overflow = solver
        .try_format_string_vuln_check(fmt, &[], buf)
        .expect("format_string_vuln_check should succeed");
    solver.try_assert_term(overflow).expect("assert overflow");
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_format_vuln_check_with_bv_arg() {
    // Format "val=" (4 chars) + bv32 arg. The BV arg gets converted to its
    // decimal string representation. Term construction should succeed.
    let mut solver = Solver::new(Logic::QfSlia);
    let fmt = solver.string_const("val=");
    let bv_arg = solver.bv_var("num", 32);
    let buf = solver.bv_const(5, 32);
    let overflow = solver
        .try_format_string_vuln_check(fmt, &[bv_arg], buf)
        .expect("format_string_vuln_check with BV arg should succeed");
    // We just verify the term was constructed without error
    let _ = overflow;
}

// =========================================================================
// Integration: combined String + BV constraints
// =========================================================================

#[test]
fn test_string_to_bv_then_bv_arithmetic() {
    // Parse "10" to bv32, add 5, check result = 15
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_const("10");
    let bv = solver.try_string_to_bv(s, 32).expect("string_to_bv");
    let five = solver.bv_const(5, 32);
    let sum = solver.try_bvadd(bv, five).expect("bvadd");
    let fifteen = solver.bv_const(15, 32);
    let eq = solver.try_eq(sum, fifteen).expect("same sort");
    solver.try_assert_term(eq).expect("bool assertion");
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_string_length_bv_in_buffer_check() {
    // Check that string length as BV can be compared to a BV buffer size
    let mut solver = Solver::new(Logic::QfSlia);
    let s = solver.string_var("input");
    let len_bv = solver.try_string_length_bv(s).expect("string_length_bv");
    let max_buf = solver.bv_const(10, 32);
    let fits = solver.try_bvule(len_bv, max_buf).expect("bvule");
    solver.try_assert_term(fits).expect("assert fits");
    assert_sat_or_unknown(solver.check_sat(), SolveResult::Sat);
}
