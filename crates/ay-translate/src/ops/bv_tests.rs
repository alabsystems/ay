// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(deprecated)] // Tests exercise the deprecated TranslationContext::new API

use super::*;
use crate::TranslationContext;
use ay_dpll::api::{Logic, SolverError, Sort, Term};

fn assert_sort_mismatch(result: Result<Term, SolverError>) {
    match result {
        Err(SolverError::SortMismatch { .. }) => {}
        other => panic!("expected SortMismatch, got {other:?}"),
    }
}

#[test]
fn test_bv_try_binary_convenience_returns_errors_instead_of_panicking() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfBv);
    let bv = ctx.bv_const(3, 8);
    let bool_term = ctx.bool_const(true);

    assert_sort_mismatch(try_add(&mut ctx, bv, bool_term));
    assert_sort_mismatch(try_and(&mut ctx, bv, bool_term));
    assert_sort_mismatch(try_shl(&mut ctx, bv, bool_term));
}

#[test]
fn test_bv_try_unary_and_extend_convenience_returns_errors_instead_of_panicking() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfBv);
    let bool_term = ctx.bool_const(true);

    assert_sort_mismatch(try_not(&mut ctx, bool_term));
    assert_sort_mismatch(try_neg(&mut ctx, bool_term));
    assert_sort_mismatch(try_zext(&mut ctx, 4, bool_term));
    assert_sort_mismatch(try_sext(&mut ctx, 4, bool_term));
}

#[test]
fn test_bv_try_convenience_success_sorts() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfBv);
    let a = ctx.bv_const(1, 8);
    let b = ctx.bv_const(2, 8);

    let sum = try_add(&mut ctx, a, b).expect("bv add should type-check");
    let inverted = try_not(&mut ctx, a).expect("bv not should type-check");
    let extended = try_zext(&mut ctx, 4, a).expect("bv zero-extension should type-check");

    assert_eq!(ctx.solver().sort_of(sum), Sort::bitvec(8));
    assert_eq!(ctx.solver().sort_of(inverted), Sort::bitvec(8));
    assert_eq!(ctx.solver().sort_of(extended), Sort::bitvec(12));
}
