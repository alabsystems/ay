// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::SmtValue;
use ay_core::kani_compat::DetHashMap;

fn bv(value: u128, width: u32) -> ChcExpr {
    ChcExpr::BitVec(value, width)
}

fn product(a: u128, b: u128, width: u32) -> ChcExpr {
    op(ChcOp::BvMul, vec![bv(a, width), bv(b, width)])
}

#[test]
fn constant_multiplication_uses_exact_modular_overflow_through_128_bits() {
    for (a, b, width, expected) in [
        (1, 1, 1, 1),
        (3, 3, 2, 1),
        (255, 2, 8, 254),
        (4, 2, 64, 8),
        (u64::MAX as u128, 2, 64, u64::MAX as u128 - 1),
        (u128::MAX, u128::MAX, 128, 1),
        (u128::MAX, 2, 128, u128::MAX - 1),
    ] {
        let actual = product(a, b, width);
        assert_eq!(
            prove(
                &ChcExpr::Bool(true),
                &ChcExpr::eq(actual.clone(), bv(expected, width))
            ),
            Ok(true)
        );
        assert_eq!(
            prove(
                &ChcExpr::Bool(true),
                &ChcExpr::eq(actual, bv(expected ^ 1, width))
            ),
            Ok(false)
        );
    }
}

#[test]
fn multiplication_never_repairs_bad_widths_or_narrows_a_wide_result() {
    for (actual, expected) in [
        (product(0, 0, 0), bv(0, 0)),
        (product(2, 2, 129), bv(4, 129)),
        (product(4, 1, 2), bv(0, 2)),
        (op(ChcOp::BvMul, vec![bv(1, 2), bv(1, 3)]), bv(1, 2)),
    ] {
        assert_eq!(
            prove(&ChcExpr::Bool(true), &ChcExpr::eq(actual, expected)),
            Ok(false)
        );
    }
}

#[test]
fn exact_literal_disequality_is_not_guessed_from_separate_classes() {
    let x = variable("x", ChcSort::BitVec(2));
    let y = variable("y", ChcSort::BitVec(2));
    let body = op(
        ChcOp::And,
        vec![
            ChcExpr::eq(x.clone(), bv(1, 2)),
            ChcExpr::eq(y.clone(), bv(2, 2)),
        ],
    );
    let equal = ChcExpr::eq(x.clone(), y.clone());
    let unequal = op(ChcOp::Ne, vec![x, y]);
    assert_eq!(prove(&body, &ChcExpr::not(equal.clone())), Ok(true));
    assert_eq!(prove(&body, &unequal), Ok(true));
    assert_eq!(prove(&body, &equal), Ok(false));
    assert_eq!(prove(&ChcExpr::Bool(true), &unequal), Ok(false));
    for (a, b) in [(false, true), (true, false), (true, true), (false, false)] {
        let comparison = ChcExpr::eq(ChcExpr::Bool(a), ChcExpr::Bool(b));
        assert_eq!(
            prove(
                &ChcExpr::Bool(true),
                &ChcExpr::eq(comparison, ChcExpr::Bool(a == b))
            ),
            Ok(true)
        );
    }
}

#[test]
fn ite_selection_uses_only_a_proven_condition_and_preserves_full_branch_sorts() {
    let tag = variable("tag", ChcSort::BitVec(4));
    let condition = ChcExpr::eq(tag.clone(), bv(3, 4));
    let term = op(ChcOp::Ite, vec![condition, bv(7, 8), bv(9, 8)]);
    for (value, expected) in [(3, 7), (4, 9)] {
        let body = ChcExpr::eq(tag.clone(), bv(value, 4));
        assert_eq!(
            prove(&body, &ChcExpr::eq(term.clone(), bv(expected, 8))),
            Ok(true)
        );
        assert_eq!(
            prove(&body, &ChcExpr::eq(term.clone(), bv(expected ^ 1, 8))),
            Ok(false)
        );
    }
    assert_eq!(
        prove(&ChcExpr::Bool(true), &ChcExpr::eq(term, bv(7, 8))),
        Ok(false)
    );
    let malformed = op(ChcOp::Ite, vec![ChcExpr::Bool(true), bv(7, 8), bv(7, 9)]);
    assert_eq!(
        prove(&ChcExpr::Bool(true), &ChcExpr::eq(malformed, bv(7, 8))),
        Ok(false)
    );
}

#[test]
fn selected_array_branch_keeps_index_sort_and_every_value() {
    let a = ChcExpr::const_array(ChcSort::BitVec(2), ChcExpr::Bool(true));
    let b = ChcExpr::const_array(ChcSort::BitVec(2), ChcExpr::Bool(false));
    let term = op(ChcOp::Ite, vec![ChcExpr::Bool(false), a.clone(), b.clone()]);
    assert_eq!(
        prove(&ChcExpr::Bool(true), &ChcExpr::eq(term.clone(), b)),
        Ok(true)
    );
    assert_eq!(
        prove(&ChcExpr::Bool(true), &ChcExpr::eq(term, a.clone())),
        Ok(false)
    );
    let invalid = op(
        ChcOp::Store,
        vec![a.clone(), bv(0, 3), ChcExpr::Bool(false)],
    );
    let dead = op(ChcOp::Ite, vec![ChcExpr::Bool(true), a.clone(), invalid]);
    assert_eq!(
        prove(&ChcExpr::Bool(false), &ChcExpr::eq(dead, a)),
        Ok(false)
    );
}

#[test]
fn all_small_constant_products_match_the_independent_expression_evaluator() {
    let env = DetHashMap::default();
    for width in 1..=4 {
        for a in 0..(1u128 << width) {
            for b in 0..(1u128 << width) {
                let term = product(a, b, width);
                let Some(SmtValue::BitVec(value, actual_width)) =
                    crate::expr::evaluate_expr(&term, &env)
                else {
                    panic!("native concrete BV product");
                };
                assert_eq!(actual_width, width);
                let equality = ChcExpr::eq(term, bv(value, width));
                assert_eq!(prove(&ChcExpr::Bool(true), &equality), Ok(true));
                assert_eq!(
                    prove(&ChcExpr::Bool(true), &ChcExpr::not(equality)),
                    Ok(false)
                );
            }
        }
    }
}
