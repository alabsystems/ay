// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the Phase-2 BigInt escape (wishlist rank 6 follow-up):
//! beyond-i128 integer constants and model witnesses must be handled EXACTLY
//! (via `SmtValue::BigInt` + the `eval_int_big` slow lane) instead of
//! degrading verdicts to Unknown — while bare beyond-i128 arithmetic in the
//! i128 fast lane still abstains (never wraps, never clamps).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::*;
use crate::smt::SmtValue;
use crate::ChcVar;
use num_bigint::BigInt;

/// `2^128 + 1` — the canonical beyond-i128 probe constant.
fn big_probe() -> BigInt {
    (BigInt::from(1u8) << 128) + 1
}

/// `int_from_bigint` canonical-form invariant at both i128 boundaries:
/// exactly-representable values stay `Int`, the first out-of-range values on
/// either side become `BigInt`.
#[test]
fn bigint_escape_int_from_bigint_canonicalization_boundaries() {
    assert_eq!(
        SmtValue::int_from_bigint(BigInt::from(i128::MAX)),
        SmtValue::Int(i128::MAX),
        "i128::MAX must stay canonical Int"
    );
    assert_eq!(
        SmtValue::int_from_bigint(BigInt::from(i128::MIN)),
        SmtValue::Int(i128::MIN),
        "i128::MIN must stay canonical Int"
    );

    let two_127: BigInt = BigInt::from(1u8) << 127; // i128::MAX + 1
    match SmtValue::int_from_bigint(two_127.clone()) {
        SmtValue::BigInt(b) => assert_eq!(b.as_ref(), &two_127),
        other => panic!("2^127 must become SmtValue::BigInt, got {other:?}"),
    }

    let below_min: BigInt = BigInt::from(i128::MIN) - 1;
    match SmtValue::int_from_bigint(below_min.clone()) {
        SmtValue::BigInt(b) => assert_eq!(b.as_ref(), &below_min),
        other => panic!("i128::MIN - 1 must become SmtValue::BigInt, got {other:?}"),
    }
}

/// `ChcExpr::from_bigint` is Int-if-fits, else a symbolic Horner tree that the
/// exact lane folds back to the same value (positive AND negative).
#[test]
fn bigint_escape_from_bigint_roundtrip() {
    assert_eq!(
        ChcExpr::from_bigint(BigInt::from(i128::MAX)),
        ChcExpr::Int(i128::MAX)
    );
    assert_eq!(
        ChcExpr::from_bigint(BigInt::from(i128::MIN)),
        ChcExpr::Int(i128::MIN)
    );

    let model = FxHashMap::default();
    for value in [big_probe(), -big_probe()] {
        let encoded = ChcExpr::from_bigint(value.clone());
        assert!(
            !matches!(encoded, ChcExpr::Int(_)),
            "beyond-i128 must not be squeezed into Int"
        );
        // The i128 fast lane abstains on the beyond-i128 tree (never wraps)...
        assert_eq!(evaluate_expr(&encoded, &model), None);
        // ...and the comparison path decides it exactly: encoded == encoded
        // is true, encoded == encoded+1 is false.
        let eq_same = ChcExpr::eq(encoded.clone(), ChcExpr::from_bigint(value.clone()));
        assert_eq!(evaluate_expr(&eq_same, &model), Some(SmtValue::Bool(true)));
        let eq_off = ChcExpr::eq(encoded, ChcExpr::from_bigint(value + 1));
        assert_eq!(evaluate_expr(&eq_off, &model), Some(SmtValue::Bool(false)));
    }
}

/// A beyond-i128 `SmtValue::BigInt` model value participates in integer
/// comparisons against parser-style Horner literals — true AND false
/// variants — and in sign checks.
#[test]
fn bigint_escape_model_value_comparisons() {
    let x = ChcVar::new("x", ChcSort::Int);
    let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::int_from_bigint(big_probe()));

    // x = 2^128+1 (Horner literal): true.
    let eq_hit = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::from_bigint(big_probe()));
    assert_eq!(evaluate_expr(&eq_hit, &model), Some(SmtValue::Bool(true)));

    // x = 2^128+2: false (mutated-witness negative control).
    let eq_miss = ChcExpr::eq(
        ChcExpr::var(x.clone()),
        ChcExpr::from_bigint(big_probe() + 1),
    );
    assert_eq!(evaluate_expr(&eq_miss, &model), Some(SmtValue::Bool(false)));

    // x > 0: true; x < 0: false.
    let gt0 = ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0));
    assert_eq!(evaluate_expr(&gt0, &model), Some(SmtValue::Bool(true)));
    let lt0 = ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(0));
    assert_eq!(evaluate_expr(&lt0, &model), Some(SmtValue::Bool(false)));

    // Negative big witness: x < 0 true, ordering against the positive probe.
    model.insert("x".to_string(), SmtValue::int_from_bigint(-big_probe()));
    assert_eq!(evaluate_expr(&lt0, &model), Some(SmtValue::Bool(true)));
    let lt_big = ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::from_bigint(big_probe()));
    assert_eq!(evaluate_expr(&lt_big, &model), Some(SmtValue::Bool(true)));

    // Mixed lane: an in-range Int model value compared against a beyond-i128
    // literal (the fast lane overflows mid-fold, the slow lane decides).
    model.insert("x".to_string(), SmtValue::Int(5));
    assert_eq!(evaluate_expr(&lt_big, &model), Some(SmtValue::Bool(true)));
    let gt_big = ChcExpr::gt(ChcExpr::var(x), ChcExpr::from_bigint(big_probe()));
    assert_eq!(evaluate_expr(&gt_big, &model), Some(SmtValue::Bool(false)));
}

/// Guard: no new mint path opened. Bare beyond-i128 ARITHMETIC (not under a
/// comparison) still evaluates to None in the canonical evaluator, and a
/// BigInt model value inside an arithmetic arm still abstains.
#[test]
fn bigint_escape_arithmetic_arms_still_abstain() {
    let model_empty = FxHashMap::default();
    let overflow = ChcExpr::Op(
        ChcOp::Add,
        vec![Arc::new(ChcExpr::Int(i128::MAX)), Arc::new(ChcExpr::Int(1))],
    );
    assert_eq!(evaluate_expr(&overflow, &model_empty), None);

    let x = ChcVar::new("x", ChcSort::Int);
    let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::int_from_bigint(big_probe()));
    let add_big_var = ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1));
    assert_eq!(
        evaluate_expr(&add_big_var, &model),
        None,
        "arithmetic arms are NOT promoted to BigInt (conservative core)"
    );
    // But the same term is decided exactly under a comparison.
    let cmp = ChcExpr::gt(add_big_var, ChcExpr::int(0));
    assert_eq!(evaluate_expr(&cmp, &model), Some(SmtValue::Bool(true)));
    // And a var bound to BigInt still evaluates to the BigInt value itself.
    assert_eq!(
        evaluate_expr(&ChcExpr::var(x), &model),
        Some(SmtValue::int_from_bigint(big_probe()))
    );
}
