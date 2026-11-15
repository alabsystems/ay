// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::SmtValue;
use ay_core::kani_compat::DetHashMap;

fn bv(value: u128, width: u32) -> ChcExpr {
    ChcExpr::BitVec(value, width)
}

#[test]
fn exact_concat_and_extract_preserve_all_128_bits() {
    let literal = (0x123456789abcdef0u128 << 64) | 0xfedcba9876543210;
    let joined = op(
        ChcOp::BvConcat,
        vec![bv(literal >> 64, 64), bv(literal & u64::MAX as u128, 64)],
    );
    let cases = [
        (joined.clone(), bv(literal, 128)),
        (
            op(ChcOp::BvExtract(127, 0), vec![joined.clone()]),
            bv(literal, 128),
        ),
        (
            op(ChcOp::BvExtract(127, 127), vec![joined.clone()]),
            bv(0, 1),
        ),
        (
            op(ChcOp::BvExtract(63, 0), vec![joined]),
            bv(0xfedcba9876543210, 64),
        ),
        (
            op(ChcOp::BvConcat, vec![bv(1, 1), bv(u128::MAX >> 1, 127)]),
            bv(u128::MAX, 128),
        ),
    ];
    for (actual, expected) in cases {
        assert_eq!(
            prove(&ChcExpr::Bool(true), &ChcExpr::eq(actual, expected)),
            Ok(true)
        );
    }
}

#[test]
fn changed_constant_operands_widths_and_unsupported_wide_folds_decline() {
    let joined = op(ChcOp::BvConcat, vec![bv(2, 2), bv(1, 2)]);
    assert_eq!(
        prove(
            &ChcExpr::Bool(true),
            &ChcExpr::eq(joined.clone(), bv(10, 4))
        ),
        Ok(false)
    );
    assert_eq!(
        prove(&ChcExpr::Bool(true), &ChcExpr::eq(joined, bv(9, 5))),
        Ok(false)
    );
    let invalid_extract = op(ChcOp::BvExtract(4, 0), vec![bv(1, 4)]);
    assert_eq!(
        prove(
            &ChcExpr::Bool(false),
            &ChcExpr::eq(invalid_extract.clone(), invalid_extract)
        ),
        Ok(false)
    );
    // A valid 129-bit expression is not silently narrowed to the u128 payload.
    let wide = op(ChcOp::BvConcat, vec![bv(1, 1), bv(0, 128)]);
    assert_eq!(
        prove(&ChcExpr::Bool(true), &ChcExpr::eq(wide, bv(0, 129))),
        Ok(false)
    );
    let extract = op(ChcOp::BvExtract(127, 0), vec![bv(1, 129)]);
    assert_eq!(
        prove(&ChcExpr::Bool(true), &ChcExpr::eq(extract, bv(1, 128))),
        Ok(false)
    );
}

#[test]
fn original_equalities_close_nested_congruence_but_not_changed_operators() {
    let x = variable("x", ChcSort::BitVec(2));
    let y = variable("y", ChcSort::BitVec(2));
    let z = variable("z", ChcSort::BitVec(2));
    let body = op(
        ChcOp::And,
        vec![ChcExpr::eq(x.clone(), y.clone()), ChcExpr::eq(y, z.clone())],
    );
    let left = op(ChcOp::BvAdd, vec![x.clone(), bv(1, 2)]);
    let right = op(ChcOp::BvAdd, vec![z.clone(), bv(1, 2)]);
    let head = ChcExpr::eq(
        op(ChcOp::BvConcat, vec![left.clone(), x]),
        op(ChcOp::BvConcat, vec![right, z.clone()]),
    );
    assert_eq!(prove(&body, &head), Ok(true));
    let wrong = ChcExpr::eq(left, op(ChcOp::BvSub, vec![z, bv(1, 2)]));
    assert_eq!(prove(&body, &wrong), Ok(false));
}

#[test]
fn boolean_equalities_entail_exact_polarity_in_both_orientations() {
    let b = variable("b", ChcSort::Bool);
    for value in [false, true] {
        for body in [
            ChcExpr::eq(b.clone(), ChcExpr::Bool(value)),
            ChcExpr::eq(ChcExpr::Bool(value), b.clone()),
        ] {
            let head = if value {
                b.clone()
            } else {
                ChcExpr::not(b.clone())
            };
            assert_eq!(prove(&body, &head), Ok(true));
            assert_eq!(prove(&body, &ChcExpr::not(head)), Ok(false));
        }
    }
}

#[test]
fn only_original_conjunction_atoms_seed_equality_classes() {
    let x = variable("x", ChcSort::BitVec(2));
    let y = variable("y", ChcSort::BitVec(2));
    let equality = ChcExpr::eq(x.clone(), y.clone());
    let head = ChcExpr::eq(
        op(ChcOp::BvConcat, vec![x, bv(0, 1)]),
        op(ChcOp::BvConcat, vec![y, bv(0, 1)]),
    );
    for body in [
        op(ChcOp::Or, vec![equality.clone(), ChcExpr::Bool(true)]),
        ChcExpr::not(equality.clone()),
        op(
            ChcOp::Ite,
            vec![variable("b", ChcSort::Bool), equality, ChcExpr::Bool(true)],
        ),
    ] {
        assert_eq!(prove(&body, &head), Ok(false));
    }
}

#[test]
fn redundant_const_stores_need_the_complete_typed_value_class() {
    let sort = ChcSort::Array(Box::new(ChcSort::BitVec(2)), Box::new(ChcSort::Bool));
    let a = variable("a", sort);
    let b = variable("b", ChcSort::Bool);
    let constant = ChcExpr::const_array(ChcSort::BitVec(2), ChcExpr::Bool(true));
    let body = op(
        ChcOp::And,
        vec![
            ChcExpr::eq(a.clone(), constant.clone()),
            ChcExpr::eq(b.clone(), ChcExpr::Bool(true)),
        ],
    );
    let store = op(ChcOp::Store, vec![a.clone(), bv(2, 2), b]);
    assert_eq!(
        prove(&body, &ChcExpr::eq(store, constant.clone())),
        Ok(true)
    );
    for value in [ChcExpr::Bool(false), variable("unrelated", ChcSort::Bool)] {
        let changed = op(ChcOp::Store, vec![a.clone(), bv(2, 2), value]);
        assert_eq!(
            prove(&body, &ChcExpr::eq(changed, constant.clone())),
            Ok(false)
        );
    }
    let wrong_index_sort = op(ChcOp::Store, vec![a, bv(2, 3), ChcExpr::Bool(true)]);
    assert_eq!(
        prove(&body, &ChcExpr::eq(wrong_index_sort, constant)),
        Ok(false)
    );
}

#[test]
fn store_indices_and_array_sort_keys_never_disappear_from_signatures() {
    let a = variable(
        "a",
        ChcSort::Array(Box::new(ChcSort::BitVec(2)), Box::new(ChcSort::Bool)),
    );
    let left = op(ChcOp::Store, vec![a.clone(), bv(0, 2), ChcExpr::Bool(true)]);
    let right = op(ChcOp::Store, vec![a, bv(1, 2), ChcExpr::Bool(true)]);
    assert_eq!(
        prove(&ChcExpr::Bool(true), &ChcExpr::eq(left, right)),
        Ok(false)
    );
    let a = ChcExpr::const_array(ChcSort::BitVec(2), ChcExpr::Bool(true));
    let b = ChcExpr::const_array(ChcSort::BitVec(3), ChcExpr::Bool(true));
    assert_eq!(prove(&ChcExpr::Bool(false), &ChcExpr::eq(a, b)), Ok(false));
}

#[test]
fn new_bv_proofs_and_sat_mutations_match_every_small_original_assignment() {
    let x = variable("x", ChcSort::BitVec(2));
    let y = variable("y", ChcSort::BitVec(2));
    let body = ChcExpr::eq(x.clone(), y.clone());
    let left = op(ChcOp::BvConcat, vec![x, bv(1, 2)]);
    let right = op(ChcOp::BvConcat, vec![y, bv(1, 2)]);
    let valid = ChcExpr::eq(left.clone(), right);
    let invalid = ChcExpr::eq(left, bv(0, 4));
    assert_eq!(prove(&body, &valid), Ok(true));
    assert_eq!(prove(&body, &invalid), Ok(false));
    let mut sat_mutation = false;
    for xv in 0..4 {
        for yv in 0..4 {
            let env: DetHashMap<_, _> = [
                ("x".into(), SmtValue::BitVec(xv, 2)),
                ("y".into(), SmtValue::BitVec(yv, 2)),
            ]
            .into_iter()
            .collect();
            if crate::expr::evaluate_expr(&body, &env) == Some(SmtValue::Bool(true)) {
                assert_eq!(
                    crate::expr::evaluate_expr(&valid, &env),
                    Some(SmtValue::Bool(true))
                );
                sat_mutation |=
                    crate::expr::evaluate_expr(&invalid, &env) == Some(SmtValue::Bool(false));
            }
        }
    }
    assert!(
        sat_mutation,
        "the negative control must have an actual countermodel"
    );
}
