// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(deprecated)] // Tests exercise the deprecated TranslationContext::new API

use super::*;
use crate::{TranslationContext, TranslationSession, TranslationState};
use ay_dpll::api::{Logic, SolveResult, Solver};

/// Accept either the expected result or Unknown (seq solver is incomplete).
fn assert_expected_or_unknown(result: ay_dpll::api::VerifiedSolveResult, expected: SolveResult) {
    let r = result.result();
    assert!(
        *r == expected || r.is_unknown(),
        "expected {expected:?} or Unknown, got {r:?}"
    );
}

#[test]
fn test_seq_unit_len() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfSeqlia);
    let five = ctx.int_const(5);
    let u = unit(&mut ctx, five);
    let l = len(&mut ctx, u);
    let one = ctx.int_const(1);
    let eq = ctx
        .solver()
        .try_eq(l, one)
        .expect("sequence length should compare to Int");
    ctx.assert_term(eq);
    assert_expected_or_unknown(ctx.check_sat(), SolveResult::Sat);
}

#[test]
fn test_seq_empty_len_zero() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfSeqlia);
    let e = empty(&mut ctx, Sort::Int);
    let l = len(&mut ctx, e);
    let zero = ctx.int_const(0);
    let eq = ctx
        .solver()
        .try_eq(l, zero)
        .expect("sequence length should compare to Int");
    ctx.assert_term(eq);
    assert_expected_or_unknown(ctx.check_sat(), SolveResult::Sat);
}

#[test]
fn test_seq_concat_contains() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfSeqlia);
    let a = ctx.get_or_declare("a".to_string(), "a", Sort::seq(Sort::Int));
    let five = ctx.int_const(5);
    let u5 = unit(&mut ctx, five);

    // seq.++(a, seq.unit(5)) contains seq.unit(5)
    let cat = concat(&mut ctx, a, u5);
    let has = predicate(&mut ctx, SeqPredicate::Contains, cat, u5);
    ctx.assert_term(has);
    assert_expected_or_unknown(ctx.check_sat(), SolveResult::Sat);
}

#[test]
fn test_seq_concat_contains_with_session() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfSeqlia).expect("QfSeqlia should be supported");
    let result = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        let a = session.get_or_declare("a".to_string(), "a", Sort::seq(Sort::Int));
        let five = session.solver().int_const(5);
        let u5 = unit(&mut session, five);
        let cat = concat(&mut session, a, u5);
        let has = predicate(&mut session, SeqPredicate::Contains, cat, u5);
        session.assert_term(has);
        session.check_sat()
    };

    assert_expected_or_unknown(result, SolveResult::Sat);
    assert_eq!(state.var_count(), 1);
}
