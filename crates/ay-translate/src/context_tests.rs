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
fn test_fresh_const_skips_existing_solver_declarations() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfUflia).expect("QfUflia should be supported");
    let existing = solver.declare_const("tmp0", Sort::Int);
    let fresh = TranslationSession::new(&mut solver, &mut state)
        .try_fresh_const("tmp", Sort::Int)
        .expect("a later numbered name is available");
    assert_ne!(fresh, existing);
    assert!(solver
        .declared_variables()
        .any(|(name, term)| name == "tmp1" && term == fresh));
}

#[test]
fn test_fresh_const_skips_existing_function_declarations() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfUf).expect("QfUf should be supported");
    solver.declare_fun("tmp0", &[], Sort::Bool);
    let fresh = TranslationSession::new(&mut solver, &mut state)
        .try_fresh_const("tmp", Sort::Bool)
        .expect("a function collision should advance the suffix");
    assert!(solver
        .declared_variables()
        .any(|(name, term)| name == "tmp1" && term == fresh));
}

#[test]
fn test_cached_variable_rejects_a_different_sort() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfUflia).expect("QfUflia should be supported");
    let mut session = TranslationSession::new(&mut solver, &mut state);
    session
        .try_get_or_declare("x".to_string(), "x", Sort::Int)
        .expect("first declaration succeeds");
    assert!(matches!(
        session.try_get_or_declare("x".to_string(), "x", Sort::Bool),
        Err(SolverError::InvalidArgument {
            operation: "declare_const",
            ..
        })
    ));
}

#[test]
fn test_cached_variable_rejects_a_different_name() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfLia).expect("QfLia should be supported");
    let mut session = TranslationSession::new(&mut solver, &mut state);
    session
        .try_get_or_declare("source-id".to_string(), "x", Sort::Int)
        .expect("first declaration succeeds");
    assert!(matches!(
        session.try_get_or_declare("source-id".to_string(), "y", Sort::Int),
        Err(SolverError::InvalidArgument {
            operation: "declare_const",
            ..
        })
    ));
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
    assert_eq!(state.get_var("x"), Some(x));
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
fn test_cached_function_rejects_a_different_signature() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfUf).expect("QfUf should be supported");
    let mut session = TranslationSession::new(&mut solver, &mut state);
    session
        .try_declare_or_get_fun("f", &[Sort::Int], Sort::Int)
        .expect("first declaration succeeds");
    assert!(matches!(
        session.try_declare_or_get_fun("f", &[Sort::Bool], Sort::Bool),
        Err(SolverError::InvalidArgument {
            operation: "declare_fun",
            ..
        })
    ));
}

#[test]
fn test_state_invalidates_solver_local_handles_when_rebound() {
    let mut state: TranslationState<String> = TranslationState::new();

    let stale_term = {
        let mut first = Solver::try_new(Logic::QfUflia).expect("first solver");
        let mut session = TranslationSession::new(&mut first, &mut state);
        session.get_or_declare("x".to_string(), "x", Sort::Int)
    };
    assert_eq!(
        state.var_count(),
        0,
        "a dropped solver invalidates its arena"
    );
    assert!(state.get_var("x").is_none());

    let mut second = Solver::try_new(Logic::QfUflia).expect("second solver");
    let unrelated = second.declare_const("unrelated", Sort::Bool);
    assert_eq!(
        stale_term, unrelated,
        "the regression needs the stale raw handle to alias a different term"
    );

    let mut session = TranslationSession::new(&mut second, &mut state);
    assert_eq!(
        session.var_count(),
        0,
        "rebind must clear stale term handles"
    );
    let x = session.get_or_declare("x".to_string(), "x", Sort::Int);
    assert_ne!(x, unrelated);
    assert_eq!(session.solver().sort_of(x), Sort::Int);
}

#[test]
fn test_state_invalidates_function_cache_when_rebound() {
    let mut state: TranslationState<String> = TranslationState::new();
    {
        let mut first = Solver::try_new(Logic::QfUf).expect("first solver");
        let mut session = TranslationSession::new(&mut first, &mut state);
        session
            .try_declare_or_get_fun("f", &[Sort::Int], Sort::Int)
            .expect("first declaration");
    }
    assert_eq!(
        state.func_count(),
        0,
        "a dropped solver invalidates its declaration arena"
    );
    assert!(state.get_func("f").is_none());

    let mut second = Solver::try_new(Logic::QfUf).expect("second solver");
    let mut session = TranslationSession::new(&mut second, &mut state);
    assert!(session.get_func("f").is_none());
    session
        .try_declare_or_get_fun("f", &[Sort::Bool], Sort::Bool)
        .expect("the old solver's signature must not leak into the new solver");
}

#[test]
fn test_state_invalidates_solver_local_handles_after_full_reset() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfUflia).expect("solver");

    let stale_term = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        session.get_or_declare("x".to_string(), "x", Sort::Int)
    };
    solver.try_reset().expect("full reset succeeds");
    let unrelated = solver.declare_const("unrelated", Sort::Bool);
    assert_eq!(
        stale_term, unrelated,
        "the reset regression needs the stale raw handle to be reused"
    );

    let mut session = TranslationSession::new(&mut solver, &mut state);
    assert_eq!(session.var_count(), 0, "reset must invalidate cached terms");
    let x = session.get_or_declare("x".to_string(), "x", Sort::Int);
    assert_ne!(x, unrelated);
    assert_eq!(session.solver().sort_of(x), Sort::Int);
}

#[test]
fn test_open_session_invalidates_caches_after_reset_through_solver_accessor() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfUflia).expect("solver");
    let mut session = TranslationSession::new(&mut solver, &mut state);
    let stale = session.get_or_declare("x".to_string(), "x", Sort::Int);
    session
        .try_declare_or_get_fun("f", &[Sort::Int], Sort::Int)
        .expect("function declaration");

    session.solver().try_reset().expect("full reset succeeds");
    let unrelated = session.solver().declare_const("unrelated", Sort::Bool);
    assert_eq!(
        stale, unrelated,
        "the regression needs the reset arena to reuse a raw term ID"
    );

    assert!(!session.has_var(&"x".to_string()));
    assert!(session.get_var(&"x".to_string()).is_none());
    assert!(session.get_func("f").is_none());
    assert_eq!(session.var_count(), 0);

    let current = session
        .try_get_or_declare("x".to_string(), "x", Sort::Int)
        .expect("cache mutation rebinds to the reset solver");
    assert_ne!(current, unrelated);
    assert_eq!(session.solver().sort_of(current), Sort::Int);
}

#[test]
fn test_owning_context_invalidates_caches_after_reset_through_solver_accessor() {
    let mut context: TranslationContext<String> = TranslationContext::new(Logic::QfUflia);
    let stale = context.get_or_declare("x".to_string(), "x", Sort::Int);
    context
        .try_declare_or_get_fun("f", &[Sort::Int], Sort::Int)
        .expect("function declaration");

    context.solver().try_reset().expect("full reset succeeds");
    let unrelated = context.solver().declare_const("unrelated", Sort::Bool);
    assert_eq!(
        stale, unrelated,
        "the regression needs the reset arena to reuse a raw term ID"
    );

    assert!(!context.has_var(&"x".to_string()));
    assert!(context.get_var(&"x".to_string()).is_none());
    assert!(context.get_func("f").is_none());
    assert_eq!(context.var_count(), 0);
    assert!(context.state().get_var("x").is_none());
    assert!(context.state().get_func("f").is_none());

    let current = context
        .try_get_or_declare("x".to_string(), "x", Sort::Int)
        .expect("cache mutation rebinds to the reset solver");
    assert_ne!(current, unrelated);
    assert_eq!(context.solver().sort_of(current), Sort::Int);
}

#[test]
fn test_open_session_rejects_cache_after_live_solver_is_swapped() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut original = Solver::try_new(Logic::QfUflia).expect("original solver");
    let mut replacement = Solver::try_new(Logic::QfUflia).expect("replacement solver");
    let unrelated = replacement.declare_const("unrelated", Sort::Bool);
    let mut session = TranslationSession::new(&mut original, &mut state);
    let stale = session.get_or_declare("x".to_string(), "x", Sort::Int);
    assert_eq!(stale, unrelated, "the two live arenas must reuse a raw ID");

    std::mem::swap(session.solver(), &mut replacement);
    assert!(session.get_var(&"x".to_string()).is_none());
    assert_eq!(session.var_count(), 0);

    let current = session
        .try_get_or_declare("x".to_string(), "x", Sort::Int)
        .expect("cache mutation rebinds to the replacement solver");
    assert_ne!(current, unrelated);
    assert_eq!(session.solver().sort_of(current), Sort::Int);
}

#[test]
fn test_owning_context_rejects_cache_after_live_solver_is_swapped() {
    let mut context: TranslationContext<String> = TranslationContext::new(Logic::QfUflia);
    let stale = context.get_or_declare("x".to_string(), "x", Sort::Int);
    context
        .try_declare_or_get_fun("f", &[Sort::Int], Sort::Int)
        .expect("function declaration");

    let mut replacement = Solver::try_new(Logic::QfUflia).expect("replacement solver");
    let unrelated = replacement.declare_const("unrelated", Sort::Bool);
    assert_eq!(stale, unrelated, "the two live arenas must reuse a raw ID");
    std::mem::swap(context.solver(), &mut replacement);

    assert!(!context.has_var(&"x".to_string()));
    assert!(context.get_var(&"x".to_string()).is_none());
    assert!(context.get_func("f").is_none());
    assert_eq!(context.var_count(), 0);

    let current = context
        .try_get_or_declare("x".to_string(), "x", Sort::Int)
        .expect("cache mutation rebinds to the replacement solver");
    assert_ne!(current, unrelated);
    assert_eq!(context.solver().sort_of(current), Sort::Int);
}

#[test]
fn test_reset_assertions_preserves_translation_cache_generation() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        session.get_or_declare("x".to_string(), "x", Sort::Int)
    };
    solver
        .try_reset_assertions()
        .expect("reset-assertions succeeds");
    let mut session = TranslationSession::new(&mut solver, &mut state);
    assert_eq!(session.get_or_declare("x".to_string(), "x", Sort::Int), x);
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
