// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::resources::{assert_numeric_boundaries, assert_poll_boundaries};
use super::*;
use std::sync::atomic::AtomicBool;
use std::time::Duration;

fn branches() -> (ChcExpr, Vec<ChcVar>) {
    let (binding, mut keep) = fixture(4, CarryOperand::Left);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let formula = op(
        ChcOp::And,
        vec![
            expr(&flag),
            op(
                ChcOp::Or,
                vec![
                    binding,
                    op(
                        ChcOp::And,
                        vec![expr(&keep[1]), eq(expr(&keep[0]), ChcExpr::BitVec(15, 4))],
                    ),
                ],
            ),
        ],
    );
    keep.push(flag);
    (formula, keep)
}

#[test]
fn joint_image_shares_every_poll_and_numeric_boundary_across_branches() {
    let (formula, keep) = branches();
    assert_poll_boundaries(&formula, &keep);
    assert_numeric_boundaries(&formula, &keep);
    let projected = closed(&formula, &keep);
    for sum in 0..16 {
        for carry in 0..2 {
            for flag in 0..2 {
                // The second disjunct deliberately supplies the first image's
                // sole missing pair. Its shared flag must constrain both arms.
                assert_eq!(
                    oracle::truth(
                        &projected,
                        &[("sum", sum), ("carry", carry), ("flag", flag)]
                    ),
                    flag == 1
                );
            }
        }
    }
}

#[test]
fn joint_image_branch_and_depth_allowances_do_not_reset() {
    let (formula, keep) = branches();
    for (branches, expected) in [(1, false), (2, true)] {
        let mut scope = Scope::new(
            Limits {
                branches,
                ..Limits::default()
            },
            &|| true,
        );
        let result = run(&formula, &keep, &mut scope);
        assert_eq!(matches!(result, Projection::Closed(_)), expected);
        if !expected {
            assert!(matches!(result, Projection::Stopped));
        }
    }
    let mut scope = Scope::new(
        Limits {
            depth: 1,
            ..Limits::default()
        },
        &|| true,
    );
    assert!(matches!(
        run(&formula, &keep, &mut scope),
        Projection::Stopped
    ));
}

#[test]
fn joint_image_observes_ambient_deadline_cancellation_interrupt_and_memory() {
    let (formula, keep) = fixture(4, CarryOperand::Left);
    {
        let _deadline = crate::smt::ScopedSmtDeadline::install(Duration::ZERO);
        assert!(matches!(project(&formula, &keep), Projection::Stopped));
    }
    {
        let token = crate::CancellationToken::new();
        token.cancel();
        let _lane = crate::smt::ScopedLaneCancellation::install(token, None);
        assert!(matches!(project(&formula, &keep), Projection::Stopped));
    }
    {
        let _lane = crate::smt::ScopedLaneCancellation::install(
            crate::CancellationToken::new(),
            Some(Arc::new(AtomicBool::new(true))),
        );
        assert!(matches!(project(&formula, &keep), Projection::Stopped));
    }
    let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
    assert!(matches!(project(&formula, &keep), Projection::Stopped));
}
