// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(deprecated)] // Tests exercise the deprecated TranslationContext::new API

use super::*;
use crate::{TranslationContext, TranslationSession, TranslationState};
use ay_dpll::api::{Logic, Solver};

#[test]
fn test_uf_declare_and_apply_with_session() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfUf).expect("QfUf should be supported");
    let result = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        let func = declare(&mut session, "f", &[Sort::Int], Sort::Int);
        let x = session.get_or_declare("x".to_string(), "x", Sort::Int);
        let app = apply(&mut session, &func, &[x]);
        let eq = session
            .solver()
            .try_eq(app, x)
            .expect("UF application should compare to Int");
        session.assert_term(eq);
        session.check_sat()
    };

    assert!(result.is_sat(), "Expected Sat, got {result:?}");
    assert_eq!(state.func_count(), 1);
}

#[test]
fn test_uf_declare_and_apply_with_context() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfUf);
    let func = declare(&mut ctx, "f", &[Sort::Int], Sort::Int);
    let x = ctx.get_or_declare("x".to_string(), "x", Sort::Int);
    let app = apply(&mut ctx, &func, &[x]);
    let eq = ctx
        .solver()
        .try_eq(app, x)
        .expect("UF application should compare to Int");
    ctx.assert_term(eq);
    let result = ctx.check_sat();

    assert!(result.is_sat(), "Expected Sat, got {result:?}");
    assert_eq!(ctx.state().func_count(), 1);
}

#[test]
fn test_uf_define_caches_inline_function_with_session() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfLia).expect("QfLia should be supported");
    let result = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        let n = session.fresh_bound_var("n", Sort::Int);
        let one = session.int_const(1);
        let body = session
            .solver()
            .try_add(n, one)
            .expect("Int addition should build");
        let inc = define(&mut session, "inc", &[("n", n)], Sort::Int, body);
        let x = session.get_or_declare("x".to_string(), "x", Sort::Int);
        let inc_x = apply(&mut session, &inc, &[x]);
        let five = session.int_const(5);
        let eq = session
            .solver()
            .try_eq(inc_x, five)
            .expect("defined function result should compare to Int");
        session.assert_term(eq);
        session.check_sat()
    };

    assert!(result.is_sat(), "Expected Sat, got {result:?}");
    assert!(state.get_func("inc").is_some());
}
