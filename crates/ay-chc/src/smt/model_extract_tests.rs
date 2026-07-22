// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{SmtContext, SmtValue};
use crate::{ChcDtConstructor, ChcDtSelector, ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

#[test]
fn test_get_term_value_ite_uses_then_branch_when_condition_true() {
    let mut ctx = SmtContext::new();
    let ite_expr = ChcExpr::ite(
        ChcExpr::le(
            ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
            ChcExpr::int(0),
        ),
        ChcExpr::int(10),
        ChcExpr::int(20),
    );

    let ite_term = ctx.convert_expr(&ite_expr);
    let mut values = FxHashMap::default();
    values.insert("x".to_string(), SmtValue::Int(-1));

    assert_eq!(ctx.get_term_value(ite_term, &values, &None), Some(10));
}

#[test]
fn test_get_term_value_ite_uses_else_branch_when_condition_false() {
    let mut ctx = SmtContext::new();
    let ite_expr = ChcExpr::ite(
        ChcExpr::le(
            ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
            ChcExpr::int(0),
        ),
        ChcExpr::int(10),
        ChcExpr::int(20),
    );

    let ite_term = ctx.convert_expr(&ite_expr);
    let mut values = FxHashMap::default();
    values.insert("x".to_string(), SmtValue::Int(1));

    assert_eq!(ctx.get_term_value(ite_term, &values, &None), Some(20));
}

#[test]
fn test_get_term_value_ite_returns_none_when_condition_indeterminate() {
    let mut ctx = SmtContext::new();
    let ite_expr = ChcExpr::ite(
        ChcExpr::le(
            ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
            ChcExpr::int(0),
        ),
        ChcExpr::int(10),
        ChcExpr::int(20),
    );

    let ite_term = ctx.convert_expr(&ite_expr);
    let mut values = FxHashMap::default();
    // x is unassigned, so x <= 0 is indeterminate.
    values.insert("y".to_string(), SmtValue::Int(7));

    assert_eq!(ctx.get_term_value(ite_term, &values, &None), None);
}

/// Verify that term_to_chc_expr handles Let bindings by converting the body (#6097).
///
/// NOTE: The current implementation skips Let bindings and converts only the body.
/// This is correct for frontend-expanded Let nodes (where the body TermIds already
/// reference the bound values directly) but drops bindings for internally-generated
/// Let nodes (CEGQI, e-matching). See algorithm audit P1:52 for details.
#[test]
fn test_term_to_chc_expr_handles_let_binding() {
    let mut ctx = SmtContext::new();
    // Build let x = 42 in x + 1 via the term store directly.
    let x_val = ctx.terms.mk_int(num_bigint::BigInt::from(42));
    let x_var = ctx.terms.mk_var("x", ay_core::Sort::Int);
    let one = ctx.terms.mk_int(num_bigint::BigInt::from(1));
    let x_plus_one = ctx.terms.mk_add(vec![x_var, one]);
    let let_term = ctx.terms.mk_let(vec![("x".to_string(), x_val)], x_plus_one);

    // term_to_chc_expr should succeed (not return None as before #6097).
    let result = ctx.term_to_chc_expr(let_term);
    assert!(
        result.is_some(),
        "term_to_chc_expr should handle Let bindings"
    );

    // The result converts the body only — bindings are dropped.
    // For internally-generated Let nodes, this means x remains a free variable.
    let result = result.unwrap();
    let result_str = format!("{result:?}");
    assert!(
        result_str.contains("Var("),
        "body-only conversion produces Var reference (bindings dropped): {result_str}"
    );
}

/// Verify that term_to_chc_expr correctly handles frontend-expanded Let bindings.
///
/// When the frontend expands `(let ((x 42)) (+ x 1))`, the body TermId already
/// references the constant 42 directly (no Var("x") node). This is the common path.
#[test]
fn test_term_to_chc_expr_handles_frontend_expanded_let() {
    let mut ctx = SmtContext::new();
    // Simulate frontend expansion: body directly uses the bound value.
    let x_val = ctx.terms.mk_int(num_bigint::BigInt::from(42));
    let one = ctx.terms.mk_int(num_bigint::BigInt::from(1));
    // Body references x_val directly (as the frontend would produce)
    let body = ctx.terms.mk_add(vec![x_val, one]);
    let let_term = ctx.terms.mk_let(vec![("x".to_string(), x_val)], body);

    let result = ctx.term_to_chc_expr(let_term);
    assert!(result.is_some(), "expanded Let should convert");

    // With frontend expansion, the body already references constants directly.
    // mk_add constant-folds 42 + 1 = 43, so the result is Int(43).
    let result = result.unwrap();
    let result_str = format!("{result:?}");
    assert!(
        !result_str.contains("Var("),
        "frontend-expanded Let body should NOT contain free variables: {result_str}"
    );
    assert_eq!(
        result,
        ChcExpr::Int(43),
        "frontend-expanded Let body should evaluate to 43 (42+1): {result_str}"
    );
}

/// Verify that term_to_chc_expr handles div/intdiv operations (#6097).
#[test]
fn test_term_to_chc_expr_handles_div() {
    let mut ctx = SmtContext::new();
    // Build (div 10 3) via ChcExpr and round-trip through term_to_chc_expr.
    let div_expr = ChcExpr::Op(
        crate::expr::ChcOp::Div,
        vec![Arc::new(ChcExpr::int(10)), Arc::new(ChcExpr::int(3))],
    );
    let div_term = ctx.convert_expr(&div_expr);
    let result = ctx.term_to_chc_expr(div_term);
    assert!(result.is_some(), "term_to_chc_expr should handle div");
}

/// Verify that term_to_chc_expr handles neg operations (#6097).
#[test]
fn test_term_to_chc_expr_handles_neg() {
    let mut ctx = SmtContext::new();
    let neg_expr = ChcExpr::neg(ChcExpr::int(5));
    let neg_term = ctx.convert_expr(&neg_expr);
    let result = ctx.term_to_chc_expr(neg_term);
    assert!(result.is_some(), "term_to_chc_expr should handle neg");
}

/// Verify that term_to_chc_expr handles bv2nat operations (#6097).
#[test]
fn test_term_to_chc_expr_handles_bv2nat() {
    let mut ctx = SmtContext::new();
    let bv = ChcExpr::BitVec(42, 8);
    let bv2nat_expr = ChcExpr::Op(crate::expr::ChcOp::Bv2Nat, vec![Arc::new(bv)]);
    let bv2nat_term = ctx.convert_expr(&bv2nat_expr);
    let result = ctx.term_to_chc_expr(bv2nat_term);
    assert!(result.is_some(), "term_to_chc_expr should handle bv2nat");
}

/// #3827 (updated for the i128 widening): get_term_value returns None (not a
/// wrong saturated value) when a BigInt constant exceeds the widened i128
/// range; beyond-i64-but-in-i128 values now extract EXACTLY.
#[test]
fn test_get_term_value_overflow_returns_none() {
    let mut ctx = SmtContext::new();

    // i128-lockstep: i64::MAX + 1 now extracts exactly.
    let big = num_bigint::BigInt::from(i64::MAX) + num_bigint::BigInt::from(1);
    let big_term = ctx.terms.mk_int(big);
    let values = FxHashMap::default();
    assert_eq!(
        ctx.get_term_value(big_term, &values, &None),
        Some(i128::from(i64::MAX) + 1),
        "beyond-i64 in-i128 constants must extract exactly"
    );

    // Beyond-i128 must still return None, never clamp.
    let huge = num_bigint::BigInt::from(i128::MAX) + num_bigint::BigInt::from(1);
    let huge_term = ctx.terms.mk_int(huge);
    assert_eq!(
        ctx.get_term_value(huge_term, &values, &None),
        None,
        "get_term_value must return None for BigInt exceeding i128::MAX"
    );

    // Negative overflow: smaller than i128::MIN
    let neg_huge = num_bigint::BigInt::from(i128::MIN) - num_bigint::BigInt::from(1);
    let neg_huge_term = ctx.terms.mk_int(neg_huge);
    assert_eq!(
        ctx.get_term_value(neg_huge_term, &values, &None),
        None,
        "get_term_value must return None for BigInt below i128::MIN"
    );
}

/// #3827: Addition of overflowing terms in get_term_value returns None via
/// checked arithmetic, not a wrapped/saturated value.
#[test]
fn test_get_term_value_addition_overflow_returns_none() {
    let mut ctx = SmtContext::new();

    // i128-lockstep: (+ i64::MAX 1) now evaluates exactly.
    let max_expr = ChcExpr::add(ChcExpr::int(i64::MAX), ChcExpr::int(1));
    let max_term = ctx.convert_expr(&max_expr);
    let values = FxHashMap::default();
    assert_eq!(
        ctx.get_term_value(max_term, &values, &None),
        Some(i128::from(i64::MAX) + 1),
        "beyond-i64 in-i128 sums must evaluate exactly"
    );

    // (+ i128::MAX 1) must return None, never wrap — whether the sum is
    // evaluated by checked i128 addition or pre-folded into a beyond-i128
    // BigInt constant by term construction.
    let huge_expr = ChcExpr::add(ChcExpr::int(i128::MAX), ChcExpr::int(1));
    let huge_term = ctx.convert_expr(&huge_expr);
    assert_eq!(
        ctx.get_term_value(huge_term, &values, &None),
        None,
        "addition overflow beyond i128 must return None"
    );
}

/// #6215: term_to_chc_expr correctly extracts 128-bit BV constants.
/// Previously (pre-#6215), u64 storage caused >64-bit values to be rejected.
/// Now with u128 storage, values up to 128 bits are correctly handled.
#[test]
fn test_term_to_chc_expr_wide_bv_succeeds() {
    let mut ctx = SmtContext::new();

    // 128-bit BV with value > u64::MAX (u64::MAX + 1 = 2^64)
    let big = num_bigint::BigInt::from(u64::MAX) + num_bigint::BigInt::from(1u64);
    let wide_bv = ctx.terms.mk_bitvec(big, 128);

    // Now correctly returns Some with u128 value
    assert_eq!(
        ctx.term_to_chc_expr(wide_bv),
        Some(ChcExpr::BitVec(1u128 << 64, 128)),
        "term_to_chc_expr should handle 128-bit BV values"
    );
}

/// #6175: term_to_chc_expr succeeds for BV constants that fit in u64.
#[test]
fn test_term_to_chc_expr_normal_bv_succeeds() {
    let mut ctx = SmtContext::new();

    let bv = ctx.terms.mk_bitvec(num_bigint::BigInt::from(255u64), 8);
    let result = ctx.term_to_chc_expr(bv);
    assert_eq!(result, Some(ChcExpr::BitVec(255, 8)));
}

#[test]
fn test_term_to_chc_expr_preserves_datatype_sort_metadata() {
    let mut ctx = SmtContext::new();
    let pair_sort = ChcSort::Datatype {
        name: "Pair".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mkPair".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "fst".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "snd".to_string(),
                    sort: ChcSort::Bool,
                },
            ],
        }]),
    };
    let mut datatype_defs = FxHashMap::default();
    datatype_defs.insert(
        "Pair".to_string(),
        vec![(
            "mkPair".to_string(),
            vec![
                ("fst".to_string(), ChcSort::Int),
                ("snd".to_string(), ChcSort::Bool),
            ],
        )],
    );
    ctx.set_datatype_defs(datatype_defs);

    let expr = ChcExpr::FuncApp(
        "mkPair".to_string(),
        pair_sort.clone(),
        vec![Arc::new(ChcExpr::Int(7)), Arc::new(ChcExpr::Bool(true))],
    );

    let term = ctx.convert_expr(&expr);
    let roundtrip = ctx
        .term_to_chc_expr(term)
        .expect("datatype constructor app should round-trip");

    assert_eq!(
        roundtrip, expr,
        "term_to_chc_expr must preserve datatype constructor metadata instead of degrading to an uninterpreted sort"
    );
}

/// #3827 (updated for the i128 widening): term_to_chc_expr extracts
/// beyond-i64 in-i128 constants exactly and returns None only beyond i128.
#[test]
fn test_term_to_chc_expr_overflow_returns_none() {
    let mut ctx = SmtContext::new();

    // i128-lockstep: i64::MAX + 1 now extracts exactly.
    let big = num_bigint::BigInt::from(i64::MAX) + num_bigint::BigInt::from(1);
    let big_term = ctx.terms.mk_int(big);
    assert_eq!(
        ctx.term_to_chc_expr(big_term),
        Some(ChcExpr::Int(i128::from(i64::MAX) + 1)),
        "beyond-i64 in-i128 BigInt must extract exactly"
    );

    // Phase-2 BigInt escape: beyond-i128 constants re-enter the symbolic
    // lane as the exact Horner tree (never wrapped, no longer aborting the
    // extraction). ChcExpr::from_bigint is the shared encoder.
    let huge = num_bigint::BigInt::from(i128::MAX) + num_bigint::BigInt::from(1);
    let huge_term = ctx.terms.mk_int(huge.clone());
    assert_eq!(
        ctx.term_to_chc_expr(huge_term),
        Some(ChcExpr::from_bigint(huge)),
        "beyond-i128 BigInt must extract as the exact Horner encoding"
    );
}
