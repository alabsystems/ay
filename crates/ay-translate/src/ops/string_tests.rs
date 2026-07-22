// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(deprecated)] // Tests exercise the deprecated TranslationContext::new API

use super::*;
use crate::{TranslationContext, TranslationSession, TranslationState};
use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

/// Accept either the expected result or Unknown (string solver is incomplete).
fn assert_expected_or_unknown(result: ay_dpll::api::VerifiedSolveResult, expected: SolveResult) {
    let r = result.result();
    assert!(
        *r == expected || r.is_unknown(),
        "expected {expected:?} or Unknown, got {r:?}"
    );
}

#[test]
fn test_str_concat_sat() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfSlia);
    let s = ctx.get_or_declare("s".to_string(), "s", Sort::String);
    let hello = string_const(&mut ctx, "hello");

    // s ++ "hello" contains "hello"
    let cat = concat(&mut ctx, s, hello);
    let has = predicate(&mut ctx, StrPredicate::Contains, cat, hello);
    ctx.assert_term(has);
    assert_expected_or_unknown(ctx.check_sat(), SolveResult::Sat);
}

#[test]
fn test_str_len_nonneg() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfSlia);
    let s = ctx.get_or_declare("s".to_string(), "s", Sort::String);

    // str.len(s) >= 0 is a tautology, assert its negation is unsat
    let l = len(&mut ctx, s);
    let zero = ctx.int_const(0);
    let lt_zero = ctx
        .solver()
        .try_lt(l, zero)
        .expect("string length should compare to Int");
    ctx.assert_term(lt_zero);
    let result = ctx.check_sat();
    assert!(
        result.result().is_unsat() || result.result().is_unknown(),
        "expected Unsat or Unknown, got {:?}",
        result.result()
    );
}

#[test]
fn test_str_concat_sat_with_session() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfSlia).expect("QfSlia should be supported");
    let result = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        let s = session.get_or_declare("s".to_string(), "s", Sort::String);
        let hello = string_const(&mut session, "hello");
        let cat = concat(&mut session, s, hello);
        let has = predicate(&mut session, StrPredicate::Contains, cat, hello);
        session.assert_term(has);
        session.check_sat()
    };

    assert_expected_or_unknown(result, SolveResult::Sat);
    assert_eq!(state.var_count(), 1);
}
