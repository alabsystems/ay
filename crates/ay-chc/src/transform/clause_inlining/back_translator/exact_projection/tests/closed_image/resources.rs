// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::resources::{assert_numeric_boundaries, assert_poll_boundaries};
use super::*;

#[test]
fn closed_term_admission_and_replacement_share_every_poll_and_numeric_limit() {
    let local = var("local", 4);
    let a = var("a", 4);
    let b = var("b", 4);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let target = op(
        ChcOp::Ite,
        vec![
            expr(&flag),
            op(ChcOp::BvAdd, vec![expr(&a), expr(&b)]),
            ChcExpr::BitVec(0, 4),
        ],
    );
    let formula = op(
        ChcOp::And,
        vec![
            expr(&flag),
            op(
                ChcOp::Or,
                vec![
                    eq(target, observation(&local, ChcOp::BvLShr, 1)),
                    eq(
                        ChcExpr::BitVec(1, 4),
                        observation(&local, ChcOp::BvLShr, 15),
                    ),
                ],
            ),
        ],
    );
    let keep = [a, b, flag];
    assert_poll_boundaries(&formula, &keep);
    assert_numeric_boundaries(&formula, &keep);
    let projected = closed(&formula, &keep);
    for a in 0..16 {
        for b in 0..16 {
            for flag in 0..2 {
                // Second alternative's image target1 is impossible, but that
                // fact cannot erase the shared guard or the first alternative.
                assert_eq!(
                    oracle::truth(&projected, &[("a", a), ("b", b), ("flag", flag)]),
                    flag == 1 && (a + b) % 16 < 8
                );
            }
        }
    }
}

#[test]
fn constant_images_including_impossible_ones_observe_every_stop_boundary() {
    let local = var("local", 128);
    for target in [0, u128::MAX] {
        let formula = eq(
            ChcExpr::BitVec(target, 128),
            observation(&local, ChcOp::BvLShr, u128::MAX),
        );
        assert_poll_boundaries(&formula, &[]);
        assert_numeric_boundaries(&formula, &[]);
        let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
        assert!(matches!(project(&formula, &[]), Projection::Stopped));
    }
}
