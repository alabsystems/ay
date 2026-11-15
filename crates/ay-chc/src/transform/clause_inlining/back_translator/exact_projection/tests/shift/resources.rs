// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::resources::{assert_numeric_boundaries, assert_poll_boundaries};
use super::*;
use std::sync::atomic::AtomicBool;
use std::time::Duration;

fn branches(amount: u128) -> (ChcExpr, Vec<ChcVar>) {
    let (formula, mut keep) = binding(4, amount);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let alternative = eq(expr(&keep[0]), ChcExpr::BitVec(15, 4));
    keep.push(flag.clone());
    (
        op(
            ChcOp::And,
            vec![expr(&flag), op(ChcOp::Or, vec![formula, alternative])],
        ),
        keep,
    )
}

#[test]
fn shift_images_keep_one_poll_work_growth_and_node_scope_across_branches() {
    for amount in [0, 1, 4, 15] {
        let (formula, keep) = branches(amount);
        assert_poll_boundaries(&formula, &keep);
        assert_numeric_boundaries(&formula, &keep);
        let projected = closed(&formula, &keep);
        for result in 0..16 {
            for flag in 0..2 {
                let expected = flag == 1
                    && (result == 15 || (0..16).any(|x| shifted_value(x, amount, 4) == result));
                assert_eq!(
                    oracle::truth(&projected, &[("result", result), ("flag", flag)]),
                    expected
                );
            }
        }
    }
}

#[test]
fn shift_branch_and_depth_allowances_do_not_reset() {
    let (formula, keep) = branches(1);
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
fn maximum_width_overshift_observes_all_ambient_stop_controls() {
    let (formula, keep) = binding(128, u128::MAX);
    assert_poll_boundaries(&formula, &keep);
    assert_numeric_boundaries(&formula, &keep);
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
