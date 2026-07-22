// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the `ChcExpr::Int(i128)` / `SmtValue::Int(i128)`
//! lockstep widening (gap-log #19, wishlist rank 6 Phase 1).
//!
//! The historic bug class guarded here: a wrapped/clamped constant makes
//! hypotheses UNSAT and proves anything by ex falso. Every fold must be
//! exact-or-refused — never wrap, never clamp.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::*;
use crate::smt::SmtValue;
use crate::ChcVar;

const U64_MAX_I128: i128 = u64::MAX as i128; // 18446744073709551615

/// (a) `Int(u64::MAX) + Int(1)` constant-folds EXACTLY (no wrap) to 2^64.
#[test]
fn i128_fold_u64_max_plus_one_exact() {
    let expr = ChcExpr::Op(
        ChcOp::Add,
        vec![
            Arc::new(ChcExpr::Int(U64_MAX_I128)),
            Arc::new(ChcExpr::Int(1)),
        ],
    );
    assert_eq!(
        expr.simplify_constants(),
        ChcExpr::Int(18_446_744_073_709_551_616_i128),
        "u64::MAX + 1 must fold exactly in the widened i128 lane"
    );
}

/// (a') The same fold through the canonical evaluator.
#[test]
fn i128_evaluate_u64_max_plus_one_exact() {
    let model = FxHashMap::default();
    let expr = ChcExpr::Op(
        ChcOp::Add,
        vec![
            Arc::new(ChcExpr::Int(U64_MAX_I128)),
            Arc::new(ChcExpr::Int(1)),
        ],
    );
    assert_eq!(
        evaluate_expr(&expr, &model),
        Some(SmtValue::Int(18_446_744_073_709_551_616_i128))
    );
}

/// (b) `x <= Int(u64::MAX)` evaluates correctly under a model with
/// `x = i64::MAX` (true: i64::MAX < u64::MAX) — and the strict converse
/// (`Int(u64::MAX) <= x`) is false, guarding against sign/order slips.
#[test]
fn i128_compare_var_against_u64_max_literal() {
    let x = ChcVar::new("x", ChcSort::Int);
    let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(i128::from(i64::MAX)));

    let le = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(U64_MAX_I128));
    assert_eq!(
        evaluate_expr(&le, &model),
        Some(SmtValue::Bool(true)),
        "i64::MAX <= u64::MAX must evaluate true (was Indeterminate pre-widening)"
    );

    let ge = ChcExpr::le(ChcExpr::Int(U64_MAX_I128), ChcExpr::var(x));
    assert_eq!(
        evaluate_expr(&ge, &model),
        Some(SmtValue::Bool(false)),
        "u64::MAX <= i64::MAX must evaluate false"
    );
}

/// (b') A model value ABOVE i64 range participates in evaluation.
#[test]
fn i128_model_value_above_i64_evaluates() {
    let x = ChcVar::new("x", ChcSort::Int);
    let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(U64_MAX_I128));

    let eq = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(U64_MAX_I128));
    assert_eq!(evaluate_expr(&eq, &model), Some(SmtValue::Bool(true)));
}

/// (c) A fold whose result would exceed i128 does NOT fold — the expression
/// stays symbolic (fail-closed), it is never wrapped or clamped.
#[test]
fn i128_fold_beyond_i128_stays_symbolic() {
    // i128::MAX + 1 would overflow: must NOT fold to a constant.
    let add = ChcExpr::Op(
        ChcOp::Add,
        vec![Arc::new(ChcExpr::Int(i128::MAX)), Arc::new(ChcExpr::Int(1))],
    );
    if let ChcExpr::Int(n) = add.simplify_constants() {
        panic!("must not fold beyond-i128 sum, got Int({n})");
    }

    // i128::MAX * 2 likewise.
    let mul = ChcExpr::Op(
        ChcOp::Mul,
        vec![Arc::new(ChcExpr::Int(i128::MAX)), Arc::new(ChcExpr::Int(2))],
    );
    if let ChcExpr::Int(n) = mul.simplify_constants() {
        panic!("must not fold beyond-i128 product, got Int({n})");
    }

    // And the evaluator abstains (None), never wraps.
    let model = FxHashMap::default();
    assert_eq!(evaluate_expr(&add, &model), None);
    assert_eq!(evaluate_expr(&mul, &model), None);
}

/// The Horner tree the parser used to emit for u64::MAX still evaluates to
/// the exact constant (compatibility with pre-widening encodings, e.g. from
/// model-checker-consumer's Phase-0 lowering).
#[test]
fn i128_horner_encoding_still_folds_exactly() {
    // (+ (* (+ (* 18 10^9) 446744073) 10^9) 709551615) = 18446744073709551615
    let horner = ChcExpr::add(
        ChcExpr::mul(
            ChcExpr::add(
                ChcExpr::mul(ChcExpr::Int(18), ChcExpr::Int(1_000_000_000)),
                ChcExpr::Int(446_744_073),
            ),
            ChcExpr::Int(1_000_000_000),
        ),
        ChcExpr::Int(709_551_615),
    );
    let model = FxHashMap::default();
    assert_eq!(
        evaluate_expr(&horner, &model),
        Some(SmtValue::Int(U64_MAX_I128))
    );
    assert_eq!(horner.simplify_constants(), ChcExpr::Int(U64_MAX_I128));
}

/// `as_i64` narrows fail-closed: in-range extracts, out-of-range is None
/// (never truncated); `as_i128` extracts the full width.
#[test]
fn i128_as_i64_fail_closed_narrowing() {
    let small = ChcExpr::Int(42);
    assert_eq!(small.as_i64(), Some(42));
    assert_eq!(small.as_i128(), Some(42));

    let big = ChcExpr::Int(U64_MAX_I128);
    assert_eq!(big.as_i64(), None, "beyond-i64 must not truncate");
    assert_eq!(big.as_i128(), Some(U64_MAX_I128));

    let neg_big = ChcExpr::neg(ChcExpr::Int(U64_MAX_I128));
    assert_eq!(neg_big.as_i64(), None);
    assert_eq!(neg_big.as_i128(), Some(-U64_MAX_I128));
}
