// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for SAT-preserving counterexample minimization (#4522).

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use crate::api::*;
use crate::CounterexampleStyle;

#[test]
fn test_counterexample_style_forwarding_default_minimal() {
    let solver = Solver::new(Logic::QfLia);
    assert_eq!(solver.counterexample_style(), CounterexampleStyle::Minimal);
}

#[test]
fn test_counterexample_style_any_disables_minimization() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_counterexample_style(CounterexampleStyle::Any);
    assert_eq!(solver.counterexample_style(), CounterexampleStyle::Any);
}

#[test]
fn test_counterexample_style_roundtrip() {
    let mut solver = Solver::new(Logic::QfLia);
    for style in [
        CounterexampleStyle::Any,
        CounterexampleStyle::Minimal,
        CounterexampleStyle::Readable,
    ] {
        solver.set_counterexample_style(style);
        assert_eq!(solver.counterexample_style(), style);
    }
}

#[test]
fn test_minimize_int_prefers_zero() {
    // x >= 0 — any non-negative integer satisfies, but minimizer should pick 0
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.int_var("x");
    let zero = solver.int_const(0);
    let ge = solver.ge(x, zero);
    solver.assert_term(ge);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    if let Some(ModelValue::Int(val)) = solver.value(x) {
        assert_eq!(val, BigInt::from(0), "minimizer should prefer 0 for x >= 0");
    }
}

#[test]
fn test_minimize_int_bounded_range() {
    // 5 <= x <= 7 — minimizer should pick 5 (smallest feasible)
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.int_var("x");
    let five = solver.int_const(5);
    let seven = solver.int_const(7);
    let ge = solver.ge(x, five);
    let le = solver.le(x, seven);
    solver.assert_term(ge);
    solver.assert_term(le);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    if let Some(ModelValue::Int(val)) = solver.value(x) {
        assert!(
            val >= BigInt::from(5) && val <= BigInt::from(7),
            "x should be in [5,7], got {val}"
        );
    }
}

#[test]
fn test_minimize_int_negative_range() {
    // -3 <= x <= -1 — minimizer should prefer -1 (smallest magnitude)
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.int_var("x");
    let neg3 = solver.int_const(-3);
    let neg1 = solver.int_const(-1);
    let ge = solver.ge(x, neg3);
    let le = solver.le(x, neg1);
    solver.assert_term(ge);
    solver.assert_term(le);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    if let Some(ModelValue::Int(val)) = solver.value(x) {
        assert_eq!(
            val,
            BigInt::from(-1),
            "minimizer should prefer -1 for x in [-3,-1]"
        );
    }
}

#[test]
fn test_minimize_any_style_does_not_minimize() {
    // With `Any` style, the solver should return whatever it finds
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_counterexample_style(CounterexampleStyle::Any);

    let x = solver.int_var("x");
    let zero = solver.int_const(0);
    let ge = solver.ge(x, zero);
    solver.assert_term(ge);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    // Just check it returns a valid model — don't assert minimality
    let val = solver.value(x);
    assert!(val.is_some(), "should have a model value");
}

#[test]
fn test_minimize_preserves_correctness_on_constrained_pair() {
    // x + y = 10 — minimizer should not break the constraint
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.int_var("x");
    let y = solver.int_var("y");
    let sum = solver.add(x, y);
    let ten = solver.int_const(10);
    let eq = solver.eq(sum, ten);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    if let (Some(ModelValue::Int(xv)), Some(ModelValue::Int(yv))) =
        (solver.value(x), solver.value(y))
    {
        assert_eq!(
            &xv + &yv,
            BigInt::from(10),
            "minimized model must still satisfy x + y = 10"
        );
    }
}

#[test]
fn test_minimize_bv_prefers_zero() {
    use ay_core::BitVecSort;
    // x >= 0 is always true for unsigned BV, so minimizer should pick 0
    let mut solver = Solver::new(Logic::QfBv);
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let x = solver.declare_const("x", bv8);
    let zero = solver.bv_const(0, 8);
    let eq = solver.bvuge(x, zero);
    solver.assert_term(eq);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    if let Some(ModelValue::BitVec { value, width }) = solver.value(x) {
        assert_eq!(width, 8);
        assert_eq!(value, BigInt::from(0), "minimizer should prefer 0 for BV");
    }
}

#[test]
fn test_minimize_bv_constrained() {
    use ay_core::BitVecSort;
    // x > 5 (unsigned) — minimizer should prefer 6
    let mut solver = Solver::new(Logic::QfBv);
    let bv8 = Sort::BitVec(BitVecSort { width: 8 });
    let x = solver.declare_const("x", bv8);
    let five = solver.bv_const(5, 8);
    let gt = solver.bvugt(x, five);
    solver.assert_term(gt);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    if let Some(ModelValue::BitVec { value, width }) = solver.value(x) {
        assert_eq!(width, 8);
        assert!(
            value > BigInt::from(5) && value <= BigInt::from(255),
            "BV value should be in (5, 255], got {value}"
        );
    }
}

#[test]
fn test_minimize_lra_prefers_zero() {
    // x >= 0.0 — minimizer should pick 0.0
    let mut solver = Solver::new(Logic::QfLra);
    let x = solver.real_var("x");
    let zero = solver.real_const(0.0);
    let ge = solver.ge(x, zero);
    solver.assert_term(ge);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    if let Some(ModelValue::Real(val)) = solver.value(x) {
        assert_eq!(val, BigRational::from_integer(BigInt::from(0)));
    }
}

#[test]
fn test_minimize_lra_bounded_range() {
    // 1.5 <= x <= 3.0 — minimizer should pick a value in range
    let mut solver = Solver::new(Logic::QfLra);
    let x = solver.real_var("x");
    let lo = solver.real_const(1.5);
    let hi = solver.real_const(3.0);
    let ge = solver.ge(x, lo);
    let le = solver.le(x, hi);
    solver.assert_term(ge);
    solver.assert_term(le);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    if let Some(ModelValue::Real(val)) = solver.value(x) {
        let lo_rat = BigRational::new(BigInt::from(3), BigInt::from(2));
        let hi_rat = BigRational::from_integer(BigInt::from(3));
        assert!(
            val >= lo_rat && val <= hi_rat,
            "x should be in [1.5, 3.0], got {val}"
        );
    }
}

#[test]
fn test_minimize_multi_pass_convergence() {
    // x + y = 10, x >= 0, y >= 0. Multi-pass should converge so
    // the constraint is preserved and at least one variable is small.
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.int_var("x");
    let y = solver.int_var("y");
    let sum = solver.add(x, y);
    let ten = solver.int_const(10);
    let zero = solver.int_const(0);
    let eq = solver.eq(sum, ten);
    let ge_x = solver.ge(x, zero);
    let ge_y = solver.ge(y, zero);
    solver.assert_term(eq);
    solver.assert_term(ge_x);
    solver.assert_term(ge_y);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    if let (Some(ModelValue::Int(xv)), Some(ModelValue::Int(yv))) =
        (solver.value(x), solver.value(y))
    {
        assert_eq!(
            &xv + &yv,
            BigInt::from(10),
            "must satisfy x + y = 10, got x={xv} y={yv}"
        );
        assert!(xv >= BigInt::from(0), "x must be >= 0");
        assert!(yv >= BigInt::from(0), "y must be >= 0");
        // At least one should be minimized to a small value (0, 1, 2, 3, or 4)
        let min_of_pair = std::cmp::min(xv.abs(), yv.abs());
        assert!(
            min_of_pair <= BigInt::from(4),
            "multi-pass should minimize at least one variable, got x={xv} y={yv}"
        );
    }
}

#[test]
fn test_minimize_three_vars_sum_constraint() {
    // x + y + z = 6, all >= 0. Minimizer should produce small values.
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.int_var("x");
    let y = solver.int_var("y");
    let z = solver.int_var("z");
    let xy = solver.add(x, y);
    let xyz = solver.add(xy, z);
    let six = solver.int_const(6);
    let zero = solver.int_const(0);
    let eq = solver.eq(xyz, six);
    let ge_x = solver.ge(x, zero);
    let ge_y = solver.ge(y, zero);
    let ge_z = solver.ge(z, zero);
    solver.assert_term(eq);
    solver.assert_term(ge_x);
    solver.assert_term(ge_y);
    solver.assert_term(ge_z);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    if let (Some(ModelValue::Int(xv)), Some(ModelValue::Int(yv)), Some(ModelValue::Int(zv))) =
        (solver.value(x), solver.value(y), solver.value(z))
    {
        assert_eq!(
            &xv + &yv + &zv,
            BigInt::from(6),
            "must satisfy x + y + z = 6"
        );
        // At least one should be minimized to 0
        let zeros = [&xv, &yv, &zv].iter().filter(|v| v.is_zero()).count();
        assert!(
            zeros >= 1,
            "minimizer should zero at least one var, got x={xv} y={yv} z={zv}"
        );
    }
}

#[test]
fn test_minimize_int_large_lower_bound() {
    // x >= 100 — with power-of-10 candidates, minimizer should find exactly 100.
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.int_var("x");
    let hundred = solver.int_const(100);
    let ge = solver.ge(x, hundred);
    solver.assert_term(ge);

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    if let Some(ModelValue::Int(val)) = solver.value(x) {
        assert!(val >= BigInt::from(100), "x must be >= 100, got {val}");
        // Should pick 100 since it's in the candidate list as a power of 10
        assert_eq!(
            val,
            BigInt::from(100),
            "minimizer should pick 100 (power of 10 candidate)"
        );
    }
}
