// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(deprecated)] // Tests exercise the deprecated TranslationContext::new API

use super::*;
use crate::{TranslationContext, TranslationSession, TranslationState};
use ay_dpll::api::{Logic, Solver, Sort};

#[test]
fn test_fp_add_sat() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfFp);
    let x = ctx.get_or_declare("x".to_string(), "x", Sort::FloatingPoint(8, 24));
    let y = ctx.get_or_declare("y".to_string(), "y", Sort::FloatingPoint(8, 24));

    // x + y == x + y (tautology)
    let sum = add(&mut ctx, RoundingMode::Rne, x, y);
    let eq = cmp(&mut ctx, Cmp::Eq, sum, sum);
    // fp.eq(NaN, NaN) is false per IEEE 754, so constrain x,y to not be NaN
    let x_not_nan = ctx
        .solver()
        .try_fp_is_nan(x)
        .expect("fp_is_nan should type-check");
    let x_not_nan = ctx
        .solver()
        .try_not(x_not_nan)
        .expect("not should type-check");
    let y_not_nan = ctx
        .solver()
        .try_fp_is_nan(y)
        .expect("fp_is_nan should type-check");
    let y_not_nan = ctx
        .solver()
        .try_not(y_not_nan)
        .expect("not should type-check");
    ctx.assert_term(x_not_nan);
    ctx.assert_term(y_not_nan);
    ctx.assert_term(eq);
    let result = ctx.check_sat();
    assert!(result.is_sat(), "Expected Sat, got {result:?}");
}

#[test]
fn test_fp_classify() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfFp);
    let nan = nan(&mut ctx, 8, 24);
    let is_nan = classify(&mut ctx, ClassPred::IsNaN, nan);
    ctx.assert_term(is_nan);
    let result = ctx.check_sat();
    assert!(result.is_sat(), "Expected Sat, got {result:?}");
}

#[test]
fn test_fp_abs_positive() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfFp);
    let x = ctx.get_or_declare("x".to_string(), "x", Sort::FloatingPoint(8, 24));

    // |x| is positive (when x is not NaN)
    let abs_x = abs(&mut ctx, x);
    let is_pos = classify(&mut ctx, ClassPred::IsPositive, abs_x);
    let not_nan = ctx
        .solver()
        .try_fp_is_nan(x)
        .expect("fp_is_nan should type-check");
    let not_nan = ctx
        .solver()
        .try_not(not_nan)
        .expect("not should type-check");
    let not_zero = ctx
        .solver()
        .try_fp_is_zero(x)
        .expect("fp_is_zero should type-check");
    let not_zero = ctx
        .solver()
        .try_not(not_zero)
        .expect("not should type-check");
    ctx.assert_term(not_nan);
    ctx.assert_term(not_zero);
    ctx.assert_term(is_pos);
    let result = ctx.check_sat();
    assert!(result.is_sat(), "Expected Sat, got {result:?}");
}

#[test]
fn test_fp_classify_with_session() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfFp).expect("QfFp should be supported");
    let result = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        let nan_term = nan(&mut session, 8, 24);
        let is_nan = classify(&mut session, ClassPred::IsNaN, nan_term);
        session.assert_term(is_nan);
        session.check_sat()
    };

    assert!(result.is_sat(), "Expected Sat, got {result:?}");
}
