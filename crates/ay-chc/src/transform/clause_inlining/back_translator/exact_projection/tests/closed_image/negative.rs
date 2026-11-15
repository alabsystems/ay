// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn assert_closed_matches_existential_locals(formula: &ChcExpr, keep: &[ChcVar]) {
    let projected = closed(formula, keep);
    for a in 0..16 {
        let exists = (0..16).any(|local| {
            (0..16).any(|other| {
                oracle::truth(formula, &[("a", a), ("local", local), ("other", other)])
            })
        });
        assert_eq!(oracle::truth(&projected, &[("a", a)]), exists, "a={a}");
    }
}

#[test]
fn target_containing_any_uneliminated_local_is_not_closed() {
    let local = var("local", 4);
    let other = var("other", 4);
    let a = var("a", 4);
    // The target is not closed, but inversion can eliminate its independent
    // local without pretending that the unsigned-image rule applies.
    assert_closed_matches_existential_locals(
        &eq(
            op(ChcOp::BvAdd, vec![expr(&other), expr(&a)]),
            observation(&local, ChcOp::BvLShr, 1),
        ),
        std::slice::from_ref(&a),
    );
    declined(
        &eq(
            op(ChcOp::BvSub, vec![expr(&a), expr(&local)]),
            observation(&local, ChcOp::BvLShr, 1),
        ),
        std::slice::from_ref(&a),
    );
    // Resolving a local alias must not hide an indirect self-dependency in
    // the proposed image target.
    declined(
        &op(
            ChcOp::And,
            vec![
                eq(
                    op(ChcOp::BvAdd, vec![expr(&other), expr(&a)]),
                    observation(&local, ChcOp::BvLShr, 1),
                ),
                eq(expr(&other), op(ChcOp::BvSub, vec![expr(&a), expr(&local)])),
            ],
        ),
        std::slice::from_ref(&a),
    );
    declined(
        &op(
            ChcOp::And,
            vec![
                eq(expr(&other), observation(&local, ChcOp::BvLShr, 1)),
                eq(expr(&local), op(ChcOp::BvAdd, vec![expr(&other), expr(&a)])),
            ],
        ),
        &[a],
    );
}

#[test]
fn equality_elimination_can_close_a_target_before_its_image_rule() {
    let local = var("local", 3);
    let alias = var("alias", 3);
    let a = var("a", 3);
    let b = var("b", 3);
    let formula = op(
        ChcOp::And,
        vec![
            eq(
                op(ChcOp::BvAdd, vec![expr(&alias), expr(&a)]),
                observation(&local, ChcOp::BvLShr, 1),
            ),
            eq(expr(&alias), expr(&b)),
        ],
    );
    let projected = closed(&formula, &[a, b]);
    for a in 0..8 {
        for b in 0..8 {
            assert_eq!(
                oracle::truth(&projected, &[("a", a), ("b", b)]),
                (a + b) % 8 < 4
            );
        }
    }
}

#[test]
fn constant_target_does_not_erase_raw_or_differently_spelled_uses() {
    let local = var("local", 4);
    let a = var("a", 4);
    let formula = eq(ChcExpr::BitVec(0, 4), observation(&local, ChcOp::BvLShr, 1));
    for side in [
        op(ChcOp::BvULt, vec![expr(&local), expr(&a)]),
        eq(expr(&a), observation(&local, ChcOp::BvLShr, 2)),
        eq(expr(&a), observation(&local, ChcOp::BvUDiv, 2)),
    ] {
        declined(
            &op(ChcOp::And, vec![formula.clone(), side]),
            std::slice::from_ref(&a),
        );
    }
    let fixed_local = eq(
        expr(&a),
        op(ChcOp::BvAdd, vec![expr(&local), ChcExpr::BitVec(1, 4)]),
    );
    assert_closed_matches_existential_locals(&op(ChcOp::And, vec![formula, fixed_local]), &[a]);
}

#[test]
fn malformed_closed_terms_and_zero_division_still_decline_in_dead_arms() {
    let local = var("local", 4);
    let a = var("a", 4);
    let observed = observation(&local, ChcOp::BvLShr, 1);
    for target in [
        ChcExpr::BitVec(0, 3),
        ChcExpr::BitVec(16, 4),
        ChcExpr::Bool(false),
        op(ChcOp::BvAdd, vec![expr(&a)]),
        op(ChcOp::BvAdd, vec![expr(&a), ChcExpr::BitVec(1, 3)]),
    ] {
        let bad = eq(target, observed.clone());
        declined(&bad, std::slice::from_ref(&a));
        declined(
            &op(
                ChcOp::Or,
                vec![
                    ChcExpr::Bool(true),
                    op(ChcOp::And, vec![ChcExpr::Bool(false), bad]),
                ],
            ),
            std::slice::from_ref(&a),
        );
    }
    declined(
        &eq(
            ChcExpr::BitVec(15, 4),
            observation(&local, ChcOp::BvUDiv, 0),
        ),
        &[],
    );
}

#[test]
fn unsupported_alternative_cannot_publish_a_constant_image_prefix() {
    let local = var("local", 4);
    let other = var("other", 4);
    let a = var("a", 4);
    let good = eq(ChcExpr::BitVec(0, 4), observation(&local, ChcOp::BvLShr, 1));
    let invertible = eq(
        op(ChcOp::BvAdd, vec![expr(&other), expr(&a)]),
        observation(&local, ChcOp::BvLShr, 1),
    );
    for alternatives in [
        vec![good.clone(), invertible.clone()],
        vec![invertible, good.clone()],
    ] {
        assert_closed_matches_existential_locals(
            &op(ChcOp::Or, alternatives),
            std::slice::from_ref(&a),
        );
    }
    let bad = op(ChcOp::BvULt, vec![expr(&local), expr(&a)]);
    for alternatives in [vec![good.clone(), bad.clone()], vec![bad, good]] {
        declined(&op(ChcOp::Or, alternatives), std::slice::from_ref(&a));
    }
}
