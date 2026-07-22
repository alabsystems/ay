// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for floor_div and floor_mod API (#3959).
//!
//! SMT-LIB `div`/`mod` use Euclidean semantics (remainder always >= 0).
//! Floor division rounds toward negative infinity. They differ when
//! the divisor is negative.

use ay_dpll::api::*;
use ntest::timeout;

fn get_int(solver: &Solver, term: Term) -> i64 {
    let val = solver.value(term).expect("model value");
    match val {
        ModelValue::Int(n) => i64::try_from(&n).expect("fits i64"),
        other => panic!("expected Int, got {other:?}"),
    }
}

/// Test floor_div via Solver API: floor_div(7, 2) = 3
#[test]
#[timeout(10_000)]
fn test_floor_div_positive_positive_3959() {
    let mut s = Solver::try_new(Logic::QfLia).unwrap();
    let x = s.int_var("x");
    let seven = s.int_const(7);
    let two = s.int_const(2);
    let fdiv = s.try_floor_div(seven, two).unwrap();
    let eq = s.try_eq(x, fdiv).unwrap();
    s.try_assert_term(eq).unwrap();
    let result = s.check_sat();
    assert!(result.is_sat(), "should be SAT");
    let val = get_int(&s, x);
    assert_eq!(val, 3, "floor_div(7, 2) should be 3");
}

/// Test floor_div via Solver API: floor_div(-7, 2) = -4
#[test]
#[timeout(10_000)]
fn test_floor_div_negative_positive_3959() {
    let mut s = Solver::try_new(Logic::QfLia).unwrap();
    let x = s.int_var("x");
    let neg_seven = s.int_const(-7);
    let two = s.int_const(2);
    let fdiv = s.try_floor_div(neg_seven, two).unwrap();
    let eq = s.try_eq(x, fdiv).unwrap();
    s.try_assert_term(eq).unwrap();
    let result = s.check_sat();
    assert!(result.is_sat(), "should be SAT");
    let val = get_int(&s, x);
    assert_eq!(val, -4, "floor_div(-7, 2) should be -4");
}

/// Test floor_div via Solver API: floor_div(7, -2) = -4
/// This is the critical case where Euclidean and floor differ:
/// Euclidean div(7, -2) = -3, but floor_div(7, -2) = -4.
#[test]
#[timeout(10_000)]
fn test_floor_div_positive_negative_3959() {
    let mut s = Solver::try_new(Logic::QfLia).unwrap();
    let x = s.int_var("x");
    let seven = s.int_const(7);
    let neg_two = s.int_const(-2);
    let fdiv = s.try_floor_div(seven, neg_two).unwrap();
    let eq = s.try_eq(x, fdiv).unwrap();
    s.try_assert_term(eq).unwrap();
    let result = s.check_sat();
    assert!(result.is_sat(), "should be SAT");
    let val = get_int(&s, x);
    assert_eq!(val, -4, "floor_div(7, -2) should be -4 (not Euclidean -3)");
}

/// Test floor_div via Solver API: floor_div(-7, -2) = 3
/// Euclidean div(-7, -2) = 4, but floor_div(-7, -2) = 3.
#[test]
#[timeout(10_000)]
fn test_floor_div_negative_negative_3959() {
    let mut s = Solver::try_new(Logic::QfLia).unwrap();
    let x = s.int_var("x");
    let neg_seven = s.int_const(-7);
    let neg_two = s.int_const(-2);
    let fdiv = s.try_floor_div(neg_seven, neg_two).unwrap();
    let eq = s.try_eq(x, fdiv).unwrap();
    s.try_assert_term(eq).unwrap();
    let result = s.check_sat();
    assert!(result.is_sat(), "should be SAT");
    let val = get_int(&s, x);
    assert_eq!(val, 3, "floor_div(-7, -2) should be 3 (not Euclidean 4)");
}

/// Test floor_div exact division: floor_div(6, -3) = -2 (same as Euclidean)
#[test]
#[timeout(10_000)]
fn test_floor_div_exact_negative_divisor_3959() {
    let mut s = Solver::try_new(Logic::QfLia).unwrap();
    let x = s.int_var("x");
    let six = s.int_const(6);
    let neg_three = s.int_const(-3);
    let fdiv = s.try_floor_div(six, neg_three).unwrap();
    let eq = s.try_eq(x, fdiv).unwrap();
    s.try_assert_term(eq).unwrap();
    let result = s.check_sat();
    assert!(result.is_sat(), "should be SAT");
    let val = get_int(&s, x);
    assert_eq!(val, -2, "floor_div(6, -3) should be -2 (exact division)");
}

/// Test floor_mod via Solver API: floor_mod(7, -2) = -1
/// Euclidean mod(7, -2) = 1, but floor_mod(7, -2) = -1.
#[test]
#[timeout(10_000)]
fn test_floor_mod_positive_negative_3959() {
    let mut s = Solver::try_new(Logic::QfLia).unwrap();
    let x = s.int_var("x");
    let seven = s.int_const(7);
    let neg_two = s.int_const(-2);
    let fmod = s.try_floor_mod(seven, neg_two).unwrap();
    let eq = s.try_eq(x, fmod).unwrap();
    s.try_assert_term(eq).unwrap();
    let result = s.check_sat();
    assert!(result.is_sat(), "should be SAT");
    let val = get_int(&s, x);
    assert_eq!(val, -1, "floor_mod(7, -2) should be -1 (not Euclidean 1)");
}

/// Test floor_mod via Solver API: floor_mod(-7, 2) = 1
/// Same as Euclidean mod(-7, 2) = 1 for positive divisor.
#[test]
#[timeout(10_000)]
fn test_floor_mod_negative_positive_3959() {
    let mut s = Solver::try_new(Logic::QfLia).unwrap();
    let x = s.int_var("x");
    let neg_seven = s.int_const(-7);
    let two = s.int_const(2);
    let fmod = s.try_floor_mod(neg_seven, two).unwrap();
    let eq = s.try_eq(x, fmod).unwrap();
    s.try_assert_term(eq).unwrap();
    let result = s.check_sat();
    assert!(result.is_sat(), "should be SAT");
    let val = get_int(&s, x);
    assert_eq!(val, 1, "floor_mod(-7, 2) should be 1");
}

/// End-to-end test: use floor_div in a symbolic constraint via the API.
/// Assert floor_div(x, 3) = 2, which means 6 <= x <= 8.
#[test]
#[timeout(10_000)]
fn test_floor_div_symbolic_constraint_3959() {
    let mut s = Solver::try_new(Logic::QfLia).unwrap();
    let x = s.int_var("x");
    let three = s.int_const(3);
    let two = s.int_const(2);
    let fdiv = s.try_floor_div(x, three).unwrap();
    let eq = s.try_eq(fdiv, two).unwrap();
    s.try_assert_term(eq).unwrap();
    let result = s.check_sat();
    assert!(result.is_sat(), "should be SAT");
    let val = get_int(&s, x);
    assert!(
        (6..=8).contains(&val),
        "floor_div(x, 3) = 2 means x in [6, 8], got {val}"
    );
}

/// End-to-end test: floor_div identity a = floor_div(a, b) * b + floor_mod(a, b).
#[test]
#[timeout(10_000)]
fn test_floor_div_mod_identity_3959() {
    let mut s = Solver::try_new(Logic::QfLia).unwrap();
    let a = s.int_var("a");
    let b = s.int_var("b");

    // b != 0
    let zero = s.int_const(0);
    let b_eq_zero = s.try_eq(b, zero).unwrap();
    let b_ne_zero = s.try_not(b_eq_zero).unwrap();
    s.try_assert_term(b_ne_zero).unwrap();

    // fdiv and fmod
    let fdiv = s.try_floor_div(a, b).unwrap();
    let fmod = s.try_floor_mod(a, b).unwrap();

    // a = fdiv * b + fmod should always hold
    let fdiv_times_b = s.try_mul(fdiv, b).unwrap();
    let sum = s.try_add(fdiv_times_b, fmod).unwrap();
    let identity = s.try_eq(a, sum).unwrap();

    // NOT(identity) should be unsat if the identity always holds
    let neg_identity = s.try_not(identity).unwrap();
    s.try_assert_term(neg_identity).unwrap();
    let result = s.check_sat();
    assert!(
        result.is_unsat(),
        "floor_div/floor_mod identity must hold: a = fdiv(a,b)*b + fmod(a,b)"
    );
}
