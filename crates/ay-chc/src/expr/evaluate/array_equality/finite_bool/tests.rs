// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::expr::evaluate::{evaluate_expr, smt_values_equal};
use crate::ChcVar;
use ay_core::kani_compat::DetHashMap;

fn source(width: u32) -> ChcExpr {
    ChcExpr::var(ChcVar::new(
        "array",
        ChcSort::Array(Box::new(ChcSort::BitVec(width)), Box::new(ChcSort::Bool)),
    ))
}

fn table(width: u32, default: bool, bits: u128) -> SmtValue {
    SmtValue::ArrayMap {
        default: Box::new(SmtValue::Bool(default)),
        entries: (0..1u128 << width)
            .filter_map(|key| {
                let value = bits & (1u128 << key) != 0;
                (value != default).then_some((SmtValue::BitVec(key, width), SmtValue::Bool(value)))
            })
            .collect(),
    }
}

#[test]
fn every_bv1_bv2_boolean_array_table_has_exact_equality_and_disequality() {
    for width in [1, 2] {
        let tables = 1u128 << (1u32 << width);
        for left in 0..tables {
            for right in 0..tables {
                for a_default in [false, true] {
                    for b_default in [false, true] {
                        let lhs = source(width);
                        let rhs = ChcExpr::var(ChcVar::new("other", lhs.sort()));
                        let model = DetHashMap::from_iter([
                            ("array".to_string(), table(width, a_default, left)),
                            ("other".to_string(), table(width, b_default, right)),
                        ]);
                        for (a, b) in [(&lhs, &rhs), (&rhs, &lhs)] {
                            assert_eq!(
                                evaluate_expr(&ChcExpr::eq(a.clone(), b.clone()), &model),
                                Some(SmtValue::Bool(left == right))
                            );
                            assert_eq!(
                                evaluate_expr(&ChcExpr::ne(a.clone(), b.clone()), &model),
                                Some(SmtValue::Bool(left != right))
                            );
                            assert_eq!(
                                evaluate_expr(
                                    &ChcExpr::not(ChcExpr::eq(a.clone(), b.clone())),
                                    &model
                                ),
                                Some(SmtValue::Bool(left != right))
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn duplicate_stores_obey_last_write_and_wide_domains_never_overflow() {
    let a = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Bool(false)),
        entries: vec![
            (SmtValue::BitVec(0, 1), SmtValue::Bool(false)),
            (SmtValue::BitVec(0, 1), SmtValue::Bool(true)),
        ],
    };
    let b = table(1, true, 1);
    assert_eq!(smt_values_equal(&a, &b), None);
    assert_eq!(equality(&source(1), &source(1), &a, &b), Some(true));
    for width in [2, 32, 64, 128] {
        let a = SmtValue::ArrayMap {
            default: Box::new(SmtValue::Bool(false)),
            entries: vec![(SmtValue::BitVec(0, width), SmtValue::Bool(true))],
        };
        let b = SmtValue::ArrayMap {
            default: Box::new(SmtValue::Bool(true)),
            entries: vec![(SmtValue::BitVec(1, width), SmtValue::Bool(false))],
        };
        assert_eq!(
            equality(&source(width), &source(width), &a, &b),
            Some(false)
        );
    }
}

#[test]
fn finite_comparison_declines_malformed_source_carriers_and_model_values() {
    let good = table(1, false, 1);
    let other = table(1, true, 1);
    for malformed in [
        ChcExpr::store(source(1), ChcExpr::BitVec(0, 2), ChcExpr::Bool(true)),
        ChcExpr::store(source(1), ChcExpr::BitVec(0, 1), ChcExpr::Int(1)),
        source(0),
        source(129),
    ] {
        assert_eq!(equality(&malformed, &source(1), &good, &other), None);
    }
    for (key, value) in [
        (SmtValue::BitVec(0, 2), SmtValue::Bool(true)),
        (SmtValue::BitVec(3, 1), SmtValue::Bool(true)),
        (SmtValue::Int(0), SmtValue::Bool(true)),
        (SmtValue::BitVec(0, 1), SmtValue::Int(1)),
    ] {
        let malformed = SmtValue::ArrayMap {
            default: Box::new(SmtValue::Bool(false)),
            entries: vec![(key, value)],
        };
        assert_eq!(equality(&source(1), &source(1), &malformed, &other), None);
    }
    let oversized = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Bool(false)),
        entries: vec![(SmtValue::BitVec(0, 1), SmtValue::Bool(true)); MAX_WORK],
    };
    assert_eq!(equality(&source(1), &source(1), &oversized, &other), None);
}
