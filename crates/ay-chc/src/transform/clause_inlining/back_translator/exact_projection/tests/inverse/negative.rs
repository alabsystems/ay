// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn repeated_or_hidden_occurrences_on_either_side_are_not_inverted() {
    let x = var("x", 3);
    let r = var("r", 3);
    let t = var("t", 3);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    for formula in [
        eq(expr(&r), op(ChcOp::BvAdd, vec![expr(&x), expr(&x)])),
        eq(expr(&r), op(ChcOp::BvSub, vec![expr(&x), expr(&x)])),
        eq(expr(&x), op(ChcOp::BvSub, vec![expr(&r), expr(&x)])),
        eq(
            op(ChcOp::BvAdd, vec![expr(&x), expr(&r)]),
            op(ChcOp::BvAdd, vec![expr(&x), expr(&t)]),
        ),
        eq(
            expr(&r),
            op(
                ChcOp::BvAdd,
                vec![
                    expr(&x),
                    op(ChcOp::Ite, vec![expr(&flag), expr(&x), expr(&t)]),
                ],
            ),
        ),
        eq(
            op(ChcOp::Ite, vec![expr(&flag), expr(&x), expr(&r)]),
            op(ChcOp::BvSub, vec![expr(&t), expr(&x)]),
        ),
    ] {
        declined(&formula, &[r.clone(), t.clone(), flag.clone()]);
    }
}

#[test]
fn unsupported_nested_multiplicative_and_nonpositive_equalities_still_decline() {
    let x = var("x", 3);
    let r = var("r", 3);
    let t = var("t", 3);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let binding = eq(expr(&r), op(ChcOp::BvAdd, vec![expr(&x), expr(&t)]));
    for formula in [
        eq(
            expr(&r),
            op(
                ChcOp::BvAdd,
                vec![
                    op(ChcOp::BvAdd, vec![expr(&x), expr(&t)]),
                    ChcExpr::BitVec(1, 3),
                ],
            ),
        ),
        eq(
            expr(&r),
            op(ChcOp::BvMul, vec![expr(&x), ChcExpr::BitVec(2, 3)]),
        ),
        op(ChcOp::Not, vec![binding.clone()]),
        op(ChcOp::Ite, vec![expr(&flag), binding, ChcExpr::Bool(true)]),
    ] {
        declined(&formula, &[r.clone(), t.clone(), flag.clone()]);
    }
}

#[test]
fn indirect_cycle_and_unrelated_remaining_local_cannot_publish_a_prefix() {
    let x = var("x", 3);
    let y = var("y", 3);
    let r = var("r", 3);
    let t = var("t", 3);
    let cycle = op(
        ChcOp::And,
        vec![
            eq(expr(&y), op(ChcOp::BvAdd, vec![expr(&x), expr(&r)])),
            eq(expr(&x), op(ChcOp::BvAdd, vec![expr(&y), expr(&t)])),
        ],
    );
    declined(&cycle, &[r.clone(), t.clone()]);
    let binding = eq(expr(&r), op(ChcOp::BvAdd, vec![expr(&x), expr(&t)]));
    let unsupported = op(ChcOp::BvULt, vec![expr(&y), expr(&r)]);
    declined(
        &op(ChcOp::And, vec![binding.clone(), unsupported.clone()]),
        &[r.clone(), t.clone()],
    );
    declined(&op(ChcOp::Or, vec![binding, unsupported]), &[r, t]);
}

#[test]
fn kept_operands_are_not_quantified_away() {
    let (formula, mut keep) = fixture(3, Form::SubRight, Orientation::Forward);
    keep.push(var("x", 3));
    let projected = closed(&formula, &keep);
    for x in 0..8 {
        for result in 0..8 {
            for other in 0..8 {
                for flag in 0..2 {
                    let values = [
                        ("x", x),
                        ("result", result),
                        ("other", other),
                        ("flag", flag),
                    ];
                    assert_eq!(
                        oracle::truth(&projected, &values),
                        oracle::truth(&formula, &values)
                    );
                }
            }
        }
    }
}

#[test]
fn malformed_inverse_source_is_rejected_even_in_a_dead_alternative() {
    let x = var("x", 3);
    let r = var("r", 3);
    for malformed in [
        op(ChcOp::BvAdd, vec![expr(&x)]),
        op(ChcOp::BvSub, vec![expr(&x), ChcExpr::Bool(true)]),
        op(ChcOp::BvAdd, vec![expr(&x), ChcExpr::BitVec(1, 2)]),
        op(ChcOp::BvSub, vec![expr(&var("x", 2)), expr(&x)]),
        op(
            ChcOp::BvAdd,
            vec![expr(&var("bad", 0)), ChcExpr::BitVec(0, 0)],
        ),
        op(
            ChcOp::BvSub,
            vec![expr(&var("bad", 129)), ChcExpr::BitVec(0, 129)],
        ),
        op(ChcOp::BvAdd, vec![expr(&x), ChcExpr::BitVec(8, 3)]),
    ] {
        let binding = eq(expr(&r), malformed);
        declined(&binding, std::slice::from_ref(&r));
        declined(
            &op(
                ChcOp::Or,
                vec![
                    ChcExpr::Bool(true),
                    op(ChcOp::And, vec![ChcExpr::Bool(false), binding]),
                ],
            ),
            std::slice::from_ref(&r),
        );
    }
}
