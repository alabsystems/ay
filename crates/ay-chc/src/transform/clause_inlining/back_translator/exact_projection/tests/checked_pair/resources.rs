// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::resources::{assert_numeric_boundaries, assert_poll_boundaries};
use super::*;
use std::sync::atomic::AtomicBool;
use std::time::Duration;

fn branches(arithmetic: Arithmetic, polarity: Polarity) -> (ChcExpr, Vec<ChcVar>) {
    let (binding, mut keep) = fixture(arithmetic, 2, polarity, Orientation::Forward);
    let shared = ChcVar::new("shared", ChcSort::Bool);
    let (result, canonical_flag) = match arithmetic {
        Arithmetic::Difference => (0, true),
        Arithmetic::Product => (3, false),
    };
    let missing_flag = match polarity {
        Polarity::Direct => canonical_flag,
        Polarity::Complement => !canonical_flag,
    };
    let missing = op(
        ChcOp::And,
        vec![
            eq(expr(&keep[0]), ChcExpr::BitVec(result, 2)),
            eq(expr(&keep[1]), ChcExpr::Bool(missing_flag)),
        ],
    );
    let formula = op(
        ChcOp::And,
        vec![expr(&shared), op(ChcOp::Or, vec![binding, missing])],
    );
    keep.push(shared);
    (formula, keep)
}

#[test]
fn both_rules_and_polarities_share_every_poll_and_numeric_limit_across_branches() {
    for arithmetic in [Arithmetic::Difference, Arithmetic::Product] {
        for polarity in [Polarity::Direct, Polarity::Complement] {
            let (formula, keep) = branches(arithmetic, polarity);
            assert_poll_boundaries(&formula, &keep);
            assert_numeric_boundaries(&formula, &keep);
            let projected = closed(&formula, &keep);
            for result in 0..4 {
                for flag in 0..2 {
                    for shared in 0..2 {
                        // The other branch supplies exactly the forbidden pair.
                        assert_eq!(
                            oracle::truth(
                                &projected,
                                &[("result", result), ("flag", flag), ("shared", shared)]
                            ),
                            shared == 1
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn product_one_bit_and_unrestricted_images_still_observe_every_boundary() {
    for width in [1, 3] {
        for polarity in [Polarity::Direct, Polarity::Complement] {
            let (formula, keep) =
                fixture(Arithmetic::Product, width, polarity, Orientation::Reverse);
            assert_poll_boundaries(&formula, &keep);
            assert_numeric_boundaries(&formula, &keep);
        }
    }
}

#[test]
fn branch_depth_deadline_cancellation_interrupt_and_memory_stops_are_terminal() {
    for arithmetic in [Arithmetic::Difference, Arithmetic::Product] {
        let (formula, keep) = branches(arithmetic, Polarity::Complement);
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
}
