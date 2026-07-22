// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for TranslationContext, TranslationSession, and TranslationState.

#![allow(deprecated)] // Tests exercise the deprecated TranslationContext::new/try_new API

use super::*;

#[test]
fn test_context_creation() {
    let ctx: TranslationContext<String> = TranslationContext::new(Logic::QfLia);
    assert_eq!(ctx.var_count(), 0);
}

#[test]
fn test_get_or_declare() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfLia);
    let x1 = ctx.get_or_declare("x".to_string(), "x", Sort::Int);
    let x2 = ctx.get_or_declare("x".to_string(), "x", Sort::Int);
    assert_eq!(x1, x2);
    assert_eq!(ctx.var_count(), 1);
}

#[test]
fn test_fresh_variables() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfLia);
    let f1 = ctx.fresh_const("tmp", Sort::Int);
    let f2 = ctx.fresh_const("tmp", Sort::Int);
    assert_ne!(f1, f2);
}

#[test]
fn test_context_inherent_fresh_parity_methods() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfLia);
    let fresh = ctx.fresh_const("tmp", Sort::Int);
    let bound = ctx.fresh_bound_var("tmp", Sort::Int);
    // Verify all three produce distinct terms
    let fresh2 = ctx.fresh_const("tmp", Sort::Int);
    assert_ne!(fresh, bound);
    assert_ne!(fresh, fresh2);
    assert_ne!(bound, fresh2);
}

#[test]
fn test_state_independence() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfLia).expect("QfLia should be supported");

    let x = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        session.get_or_declare("x".to_string(), "x", Sort::Int)
    };

    assert_eq!(state.var_count(), 1);
    assert_eq!(state.vars.get("x"), Some(&x));
}

#[test]
fn test_declare_or_get_fun() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfUf);
    let f1 = ctx.declare_or_get_fun("f", &[Sort::Int], Sort::Int);
    let f2 = ctx.declare_or_get_fun("f", &[Sort::Int], Sort::Int);
    assert_eq!(f1, f2);
    assert_eq!(ctx.state().func_count(), 1);
}

#[test]
fn test_session_convenience_methods() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfLia).expect("QfLia should be supported");

    let (result, fresh, bound) = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        let x = session.get_or_declare("x".to_string(), "x", Sort::Int);
        let one = session.int_const(1);
        let eq = session
            .solver()
            .try_eq(x, one)
            .expect("Int terms should compare");
        let truth = session.bool_const(true);
        session.assert_term(truth);
        session.assert_term(eq);
        assert_eq!(session.var_count(), 1);
        let fresh = session.fresh_const("tmp", Sort::Int);
        let bound = session.fresh_bound_var("tmp", Sort::Int);
        (session.check_sat(), fresh, bound)
    };

    assert!(result.is_sat(), "Expected Sat, got {result:?}");
    assert_eq!(state.var_count(), 1);
    assert_ne!(fresh, bound);
}

#[test]
fn test_session_bv_const() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfBv).expect("QfBv should be supported");

    let result = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        let five = session.bv_const(5, 8);
        let eq = session
            .solver()
            .try_eq(five, five)
            .expect("BV terms should compare");
        session.assert_term(eq);
        session.check_sat()
    };

    assert!(result.is_sat(), "Expected Sat, got {result:?}");
}

#[test]
fn test_try_bv_const_returns_error_for_invalid_width() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfBv).expect("QfBv should be supported");

    let result = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        session.try_bv_const(5, 0)
    };

    assert!(matches!(
        result,
        Err(SolverError::InvalidArgument {
            operation: "bv_const",
            ..
        })
    ));

    let mut ctx: TranslationContext<String> =
        TranslationContext::try_new(Logic::QfBv).expect("QfBv should be supported");
    assert!(matches!(
        ctx.try_bv_const(5, 0),
        Err(SolverError::InvalidArgument {
            operation: "bv_const",
            ..
        })
    ));
}

#[test]
fn test_bv_const_u64_accepts_unsigned_masks() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfBv).expect("QfBv should be supported");

    {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        let mask = session.bv_const_u64(u64::MAX, 128);
        assert_eq!(session.solver().sort_of(mask), Sort::bitvec(128));
    }

    let mut ctx: TranslationContext<String> =
        TranslationContext::try_new(Logic::QfBv).expect("QfBv should be supported");
    let sign_bit = ctx.bv_const_u64(0x8000_0000_0000_0000, 64);
    assert_eq!(ctx.solver().sort_of(sign_bit), Sort::bitvec(64));
}

#[test]
fn test_try_bv_const_u64_returns_error_for_invalid_width() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfBv).expect("QfBv should be supported");

    let result = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        session.try_bv_const_u64(u64::MAX, 0)
    };

    assert!(matches!(
        result,
        Err(SolverError::InvalidArgument {
            operation: "bv_const_u64",
            ..
        })
    ));

    let mut ctx: TranslationContext<String> =
        TranslationContext::try_new(Logic::QfBv).expect("QfBv should be supported");
    assert!(matches!(
        ctx.try_bv_const_u64(u64::MAX, 0),
        Err(SolverError::InvalidArgument {
            operation: "bv_const_u64",
            ..
        })
    ));
}

#[test]
fn test_session_from_context() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfLia);
    let x = {
        let mut session = ctx.session();
        session.get_or_declare("x".to_string(), "x", Sort::Int)
    };
    assert_eq!(ctx.get_var(&"x".to_string()), Some(x));
}

#[test]
fn test_try_scope_operations() {
    let mut ctx: TranslationContext<String> =
        TranslationContext::try_new(Logic::QfLia).expect("QfLia should be supported");

    ctx.try_push().expect("push should succeed");
    ctx.try_pop().expect("pop should succeed");
}
