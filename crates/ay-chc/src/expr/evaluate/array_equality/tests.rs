// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{evaluate_expr, smt_values_equal, FxHashMap};
use super::*;
use crate::{ChcDtConstructor, ChcVar};
use num_bigint::BigInt;
use std::sync::Arc;

fn operands(key: ChcSort) -> (ChcExpr, ChcExpr) {
    let sort = ChcSort::Array(Box::new(key), Box::new(ChcSort::Int));
    (
        ChcExpr::var(ChcVar::new("lhs", sort.clone())),
        ChcExpr::var(ChcVar::new("rhs", sort)),
    )
}

fn constant(value: i128) -> SmtValue {
    SmtValue::ConstArray(Box::new(SmtValue::Int(value)))
}

fn stored(default: i128, entries: Vec<(SmtValue, SmtValue)>) -> SmtValue {
    SmtValue::ArrayMap {
        default: Box::new(SmtValue::Int(default)),
        entries,
    }
}

fn check_comparisons(lhs: &ChcExpr, rhs: &ChcExpr, a: SmtValue, b: SmtValue, equal: Option<bool>) {
    let mut model = FxHashMap::default();
    model.insert("lhs".to_string(), a);
    model.insert("rhs".to_string(), b);
    for (left, right) in [(lhs, rhs), (rhs, lhs)] {
        assert_eq!(
            evaluate_expr(&ChcExpr::eq(left.clone(), right.clone()), &model),
            equal.map(SmtValue::Bool)
        );
        assert_eq!(
            evaluate_expr(&ChcExpr::ne(left.clone(), right.clone()), &model),
            equal.map(|value| SmtValue::Bool(!value))
        );
        assert_eq!(
            evaluate_expr(
                &ChcExpr::not(ChcExpr::eq(left.clone(), right.clone())),
                &model
            ),
            equal.map(|value| SmtValue::Bool(!value))
        );
    }
}

#[test]
fn integer_arrays_with_different_defaults_decide_all_equality_spellings() {
    let (lhs, rhs) = operands(ChcSort::Int);
    let a = constant(1);
    let b = stored(0, vec![(SmtValue::Int(5), SmtValue::Int(1))]);
    assert_eq!(smt_values_equal(&a, &b), None);
    check_comparisons(&lhs, &rhs, a, b, Some(false));

    let a = stored(0, vec![(SmtValue::Int(-5), SmtValue::Int(1))]);
    let b = stored(1, vec![(SmtValue::Int(5), SmtValue::Int(0))]);
    assert_eq!(smt_values_equal(&a, &b), None);
    check_comparisons(&lhs, &rhs, a, b, Some(false));
}

#[test]
fn ground_integer_store_expressions_retain_index_sort_evidence() {
    let a = ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(1));
    let b = ChcExpr::store(
        ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0)),
        ChcExpr::add(ChcExpr::Int(2), ChcExpr::Int(3)),
        ChcExpr::Int(1),
    );
    let div = ChcExpr::Op(
        ChcOp::Div,
        vec![ChcExpr::Int(4).into(), ChcExpr::Int(4).into()],
    );
    let query = ChcExpr::and_all([
        ChcExpr::le(ChcExpr::Int(1), div),
        ChcExpr::not(ChcExpr::eq(a.clone(), b.clone())),
    ]);
    assert_eq!(
        evaluate_expr(&query, &FxHashMap::default()),
        Some(SmtValue::Bool(true))
    );
    assert_eq!(
        evaluate_expr(&ChcExpr::ne(b, a), &FxHashMap::default()),
        Some(SmtValue::Bool(true))
    );
}

#[test]
fn canonical_beyond_i128_integer_values_remain_exact() {
    let (lhs, rhs) = operands(ChcSort::Int);
    let magnitude = BigInt::from(1_u8) << 200_usize;
    let positive = SmtValue::int_from_bigint(magnitude.clone());
    let negative = SmtValue::int_from_bigint(-magnitude);
    let a = SmtValue::ConstArray(Box::new(positive.clone()));
    let b = SmtValue::ArrayMap {
        default: Box::new(negative.clone()),
        entries: vec![(negative, positive)],
    };
    assert_eq!(smt_values_equal(&a, &b), None);
    check_comparisons(&lhs, &rhs, a, b, Some(false));
}

#[test]
fn finite_and_unknown_index_domains_keep_differing_defaults_indeterminate() {
    let singleton = ChcSort::Datatype {
        name: "Singleton".to_string(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "only".to_string(),
            selectors: Vec::new(),
        }]),
    };
    for (sort, keys) in [
        (
            ChcSort::Bool,
            vec![SmtValue::Bool(false), SmtValue::Bool(true)],
        ),
        (
            ChcSort::BitVec(1),
            vec![SmtValue::BitVec(0, 1), SmtValue::BitVec(1, 1)],
        ),
        (
            singleton,
            vec![SmtValue::Datatype("only".to_string(), Vec::new())],
        ),
        (
            ChcSort::Uninterpreted("U".to_string()),
            vec![SmtValue::Opaque("u".to_string())],
        ),
    ] {
        let (lhs, rhs) = operands(sort);
        let a = constant(1);
        let b = stored(
            0,
            keys.into_iter()
                .map(|key| (key, SmtValue::Int(1)))
                .collect(),
        );
        assert_eq!(smt_values_equal(&a, &b), None);
        check_comparisons(&lhs, &rhs, a, b, None);
    }

    // Neither support covers Bool alone, but their union does. Both arrays
    // map false to 1 and true to 0, despite different stored defaults.
    let (lhs, rhs) = operands(ChcSort::Bool);
    let a = stored(0, vec![(SmtValue::Bool(false), SmtValue::Int(1))]);
    let b = stored(1, vec![(SmtValue::Bool(true), SmtValue::Int(0))]);
    assert_eq!(smt_values_equal(&a, &b), None);
    check_comparisons(&lhs, &rhs, a, b, None);
}

#[test]
fn malformed_and_opaque_integer_values_do_not_gain_a_typed_answer() {
    let (lhs, rhs) = operands(ChcSort::Int);
    let bad_values = [
        SmtValue::Bool(true),
        SmtValue::Real(num_rational::BigRational::from_integer(1.into())),
        SmtValue::Opaque("unknown".to_string()),
        constant(1),
        SmtValue::BigInt(Arc::new(BigInt::from(0))),
    ];
    for bad in bad_values {
        for entries in [
            vec![(bad.clone(), SmtValue::Int(1))],
            vec![(SmtValue::Int(0), bad.clone())],
            vec![
                (SmtValue::Int(0), bad.clone()),
                (SmtValue::Int(0), SmtValue::Int(1)),
            ],
        ] {
            let a = stored(0, entries);
            let b = constant(1);
            assert_eq!(smt_values_equal(&a, &b), None);
            check_comparisons(&lhs, &rhs, a, b, None);
        }
    }
    for bad_default in [
        SmtValue::Bool(true),
        SmtValue::Opaque("unknown".to_string()),
        SmtValue::BigInt(Arc::new(BigInt::from(0))),
    ] {
        let a = SmtValue::ArrayMap {
            default: Box::new(bad_default),
            entries: Vec::new(),
        };
        let b = constant(0);
        assert_eq!(smt_values_equal(&a, &b), None);
        check_comparisons(&lhs, &rhs, a, b, None);
    }
    check_comparisons(
        &lhs,
        &rhs,
        SmtValue::Opaque("array".to_string()),
        constant(0),
        None,
    );
}

#[test]
fn mismatched_and_malformed_source_carriers_do_not_gain_a_typed_answer() {
    let (lhs, _) = operands(ChcSort::Int);
    let (_, rhs) = operands(ChcSort::Bool);
    let a = stored(0, Vec::new());
    let b = constant(1);
    assert_eq!(smt_values_equal(&a, &b), None);
    check_comparisons(&lhs, &rhs, a.clone(), b.clone(), None);

    let base = ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0));
    for malformed in [
        ChcExpr::store(base.clone(), ChcExpr::Bool(false), ChcExpr::Int(1)),
        ChcExpr::store(base.clone(), ChcExpr::Int(0), ChcExpr::Bool(true)),
        ChcExpr::Op(ChcOp::Store, vec![base.clone().into()]),
        ChcExpr::const_array(ChcSort::Int, ChcExpr::Bool(false)),
        ChcExpr::const_array(ChcSort::Int, ChcExpr::Op(ChcOp::Div, Vec::new())),
    ] {
        // The direct fallback sees canonical values, so this specifically
        // proves refusal comes from the source carrier/type checks.
        assert_eq!(integer_array_equality(&malformed, &lhs, &a, &b), None);
        assert_eq!(integer_array_equality(&lhs, &malformed, &b, &a), None);
    }
}

#[test]
fn integer_array_fallback_shares_source_entry_and_payload_budgets() {
    let (lhs, rhs) = operands(ChcSort::Int);
    let entries = vec![(SmtValue::Int(0), SmtValue::Int(0)); MAX_WORK / 4];
    let a = stored(0, entries.clone());
    let b = stored(1, entries);
    assert_eq!(
        integer_array_equality(&lhs, &rhs, &a, &constant(1)),
        Some(false)
    );
    assert_eq!(
        integer_array_equality(&lhs, &rhs, &b, &constant(0)),
        Some(false)
    );
    assert_eq!(smt_values_equal(&a, &b), None);
    check_comparisons(&lhs, &rhs, a, b, None);

    // Source visits and value entries share the same allowance, rather than
    // each receiving MAX_WORK independently.
    #[expect(
        clippy::rc_clone_in_vec_init,
        reason = "the work-cap fixture intentionally shares one immutable zero node to isolate edge accounting"
    )]
    let middle_default = ChcExpr::Op(ChcOp::Add, vec![Arc::new(ChcExpr::Int(0)); MAX_WORK / 2]);
    let middle_source = ChcExpr::const_array(ChcSort::Int, middle_default);
    let a = stored(0, Vec::new());
    let b = stored(1, vec![(SmtValue::Int(0), SmtValue::Int(0)); MAX_WORK / 4]);
    assert_eq!(
        integer_array_equality(&middle_source, &rhs, &a, &constant(1)),
        Some(false)
    );
    assert_eq!(integer_array_equality(&lhs, &rhs, &a, &b), Some(false));
    assert_eq!(integer_array_equality(&middle_source, &rhs, &a, &b), None);

    #[expect(
        clippy::rc_clone_in_vec_init,
        reason = "the work-cap fixture intentionally shares one immutable zero node to isolate edge accounting"
    )]
    let wide_default = ChcExpr::Op(ChcOp::Add, vec![Arc::new(ChcExpr::Int(0)); MAX_WORK]);
    let wide_source = ChcExpr::const_array(ChcSort::Int, wide_default);
    assert_eq!(
        integer_array_equality(&wide_source, &rhs, &stored(0, Vec::new()), &constant(1)),
        None
    );

    let oversized = SmtValue::int_from_bigint(BigInt::from(1_u8) << (MAX_WORK * 64));
    let a = SmtValue::ArrayMap {
        default: Box::new(oversized),
        entries: Vec::new(),
    };
    let b = constant(0);
    assert_eq!(smt_values_equal(&a, &b), None);
    check_comparisons(&lhs, &rhs, a, b, None);

    let magnitude = BigInt::from(1_u8) << (MAX_WORK / 2 * 64);
    let a = SmtValue::ConstArray(Box::new(SmtValue::int_from_bigint(magnitude.clone())));
    let b = SmtValue::ArrayMap {
        default: Box::new(SmtValue::int_from_bigint(-magnitude)),
        entries: Vec::new(),
    };
    assert_eq!(
        integer_array_equality(&lhs, &rhs, &a, &constant(0)),
        Some(false)
    );
    assert_eq!(
        integer_array_equality(&lhs, &rhs, &b, &constant(0)),
        Some(false)
    );
    assert_eq!(smt_values_equal(&a, &b), None);
    check_comparisons(&lhs, &rhs, a, b, None);
}

#[test]
fn equal_defaults_preserve_untyped_last_store_wins() {
    let (lhs, rhs) = operands(ChcSort::Int);
    let a = stored(
        0,
        vec![
            (SmtValue::Int(1), SmtValue::Int(10)),
            (SmtValue::Int(1), SmtValue::Int(20)),
        ],
    );
    let b = stored(0, vec![(SmtValue::Int(1), SmtValue::Int(20))]);
    assert_eq!(smt_values_equal(&a, &b), Some(true));
    check_comparisons(&lhs, &rhs, a, b, Some(true));
}
