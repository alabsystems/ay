// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn raw_local_constraints_and_mixed_observations_cannot_be_erased() {
    let local = var("local", 4);
    let extra = var("extra", 4);
    let (formula, mut keep) = binding(4, 1);
    keep.push(extra.clone());
    for side in [
        op(ChcOp::BvULt, vec![expr(&local), ChcExpr::BitVec(3, 4)]),
        eq(expr(&extra), shift(&local, 2)),
        eq(expr(&extra), quotient(&local, 2)),
        eq(expr(&extra), quotient(&local, 3)),
        eq(
            expr(&extra),
            op(ChcOp::BvAShr, vec![expr(&local), ChcExpr::BitVec(1, 4)]),
        ),
    ] {
        declined(&op(ChcOp::And, vec![formula.clone(), side]), &keep);
    }
    let fixed_local = op(
        ChcOp::And,
        vec![
            formula,
            eq(
                expr(&extra),
                op(ChcOp::BvAdd, vec![expr(&local), ChcExpr::BitVec(1, 4)]),
            ),
        ],
    );
    let projected = closed(&fixed_local, &keep);
    for result in 0..16 {
        for extra in 0..16 {
            let exists = (0..16).any(|local| {
                oracle::truth(
                    &fixed_local,
                    &[("result", result), ("extra", extra), ("local", local)],
                )
            });
            assert_eq!(
                oracle::truth(&projected, &[("result", result), ("extra", extra)]),
                exists,
                "result={result}, extra={extra}"
            );
        }
    }
    // Even two different overshift constants retain their source identity.
    let (overshift, _) = binding(4, 4);
    declined(
        &op(
            ChcOp::And,
            vec![overshift, eq(expr(&extra), shift(&local, 15))],
        ),
        &keep,
    );
}

#[test]
fn nonconstant_left_arithmetic_and_nested_shift_inputs_decline() {
    let local = var("local", 4);
    let amount = var("amount", 4);
    let (_, keep) = binding(4, 1);
    for unsupported in [
        op(ChcOp::BvLShr, vec![expr(&local), expr(&amount)]),
        op(ChcOp::BvShl, vec![expr(&local), ChcExpr::BitVec(1, 4)]),
        op(ChcOp::BvAShr, vec![expr(&local), ChcExpr::BitVec(1, 4)]),
        op(
            ChcOp::BvLShr,
            vec![
                op(ChcOp::BvAdd, vec![expr(&local), ChcExpr::BitVec(1, 4)]),
                ChcExpr::BitVec(1, 4),
            ],
        ),
    ] {
        declined(&eq(expr(&keep[0]), unsupported), &keep);
    }
}

#[test]
fn malformed_source_is_checked_before_dead_branch_or_overshift_elimination() {
    let local = var("local", 4);
    let (good, keep) = binding(4, 15);
    for malformed in [
        op(ChcOp::BvLShr, vec![]),
        op(ChcOp::BvLShr, vec![expr(&local)]),
        op(ChcOp::BvLShr, vec![expr(&local), ChcExpr::BitVec(1, 3)]),
        op(ChcOp::BvLShr, vec![expr(&local), ChcExpr::BitVec(16, 4)]),
        op(ChcOp::BvLShr, vec![expr(&local), ChcExpr::Bool(true)]),
        op(
            ChcOp::BvLShr,
            vec![expr(&local), ChcExpr::BitVec(1, 4), ChcExpr::BitVec(1, 4)],
        ),
    ] {
        let bad = eq(expr(&keep[0]), malformed);
        declined(&bad, &keep);
        declined(
            &op(
                ChcOp::Or,
                vec![
                    good.clone(),
                    op(ChcOp::And, vec![ChcExpr::Bool(false), bad]),
                ],
            ),
            &keep,
        );
    }
    for width in [0, 129] {
        let (formula, keep) = binding(width, 1);
        declined(&formula, &keep);
    }
    let wrong_keep = vec![ChcVar::new("result", ChcSort::Bool)];
    declined(&good, &wrong_keep);
}

#[test]
fn one_unsupported_alternative_cannot_publish_a_closed_prefix() {
    let (good, keep) = binding(4, 1);
    let local = var("local", 4);
    let unsupported = eq(
        expr(&keep[0]),
        op(ChcOp::BvAShr, vec![expr(&local), ChcExpr::BitVec(1, 4)]),
    );
    for alternatives in [
        vec![good.clone(), unsupported.clone()],
        vec![unsupported, good],
    ] {
        declined(&op(ChcOp::Or, alternatives), &keep);
    }
}
