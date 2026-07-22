// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(deprecated)] // Tests exercise the deprecated TranslationContext::new API

use super::*;
use crate::{TranslationContext, TranslationSession, TranslationState};
use ay_dpll::api::{Logic, Sort};

#[test]
fn test_bool_nary() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfLia);
    let a = ctx.bool_const(true);
    let b = ctx.bool_const(false);
    let result = bool_nary(&mut ctx, NaryBoolOp::And, &[a, b]);
    ctx.assert_term(result);
    let result = ctx.check_sat();
    assert!(result.is_unsat(), "Expected Unsat, got {result:?}");
}

#[test]
fn test_comparison() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfLia);
    let x = ctx.get_or_declare("x".to_string(), "x", Sort::Int);
    let five = ctx.int_const(5);
    let gt = compare(&mut ctx, Comparison::Gt, x, five);
    ctx.assert_term(gt);
    let result = ctx.check_sat();
    assert!(result.is_sat(), "Expected Sat, got {result:?}");
}

#[test]
fn test_bool_nary_with_session() {
    use ay_dpll::api::Solver;

    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfLia).expect("QfLia should be supported");
    let result = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        let a = session.solver().bool_const(true);
        let b = session.solver().bool_const(false);
        let expr = bool_nary(&mut session, NaryBoolOp::And, &[a, b]);
        session.assert_term(expr);
        session.check_sat()
    };
    assert!(result.is_unsat(), "Expected Unsat, got {result:?}");
}
