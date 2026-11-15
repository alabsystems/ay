// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

fn fixture() -> (ChcExpr, Vec<ChcVar>) {
    let x = var("x", 4);
    let a = var("a", 4);
    (eq(expr(&a), quotient(&x, 2)), vec![a])
}

fn scoped(formula: &ChcExpr, keep: &[ChcVar], limits: Limits) -> Projection {
    run(formula, keep, &mut Scope::new(limits, &|| true))
}

#[test]
fn every_observed_poll_can_stop_once_without_publishing_a_candidate() {
    let (binding, mut keep) = fixture();
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let formula = op(
        ChcOp::And,
        vec![
            expr(&flag),
            op(
                ChcOp::Or,
                vec![binding, eq(expr(&keep[0]), ChcExpr::BitVec(15, 4))],
            ),
        ],
    );
    keep.push(flag);
    assert_poll_boundaries(&formula, &keep);
}

pub(super) fn assert_poll_boundaries(formula: &ChcExpr, keep: &[ChcVar]) {
    let polls = Cell::new(0);
    let open = || {
        polls.set(polls.get() + 1);
        true
    };
    assert!(matches!(
        run(formula, keep, &mut Scope::new(Limits::default(), &open)),
        Projection::Closed(_)
    ));
    let total = polls.get();
    for stop_at in 1..=total {
        let seen = Cell::new(0);
        let open = || {
            seen.set(seen.get() + 1);
            seen.get() != stop_at
        };
        assert!(
            matches!(
                run(formula, keep, &mut Scope::new(Limits::default(), &open)),
                Projection::Stopped
            ),
            "poll {stop_at}/{total}"
        );
        assert_eq!(seen.get(), stop_at, "a stopped scope resumed polling");
    }
}

#[test]
fn exact_and_short_cumulative_work_growth_and_node_allowances() {
    let (formula, keep) = fixture();
    assert_numeric_boundaries(&formula, &keep);
}

pub(super) fn assert_numeric_boundaries(formula: &ChcExpr, keep: &[ChcVar]) {
    let full = Limits::default();
    let mut scope = Scope::new(full, &|| true);
    assert!(matches!(
        run(formula, keep, &mut scope),
        Projection::Closed(_)
    ));
    let work = full.work - scope.remaining.work;
    for amount in 0..work {
        assert!(
            matches!(
                scoped(
                    formula,
                    keep,
                    Limits {
                        work: amount,
                        ..full
                    }
                ),
                Projection::Stopped
            ),
            "work allowance {amount}"
        );
    }
    assert!(matches!(
        scoped(formula, keep, Limits { work, ..full }),
        Projection::Closed(_)
    ));
    let growth = full.growth - scope.remaining.growth;
    let nodes = full.nodes - scope.remaining.nodes;
    for limits in [
        Limits { growth: 0, ..full },
        Limits {
            growth: growth - 1,
            ..full
        },
        Limits {
            nodes: nodes - 1,
            ..full
        },
    ] {
        assert!(matches!(scoped(formula, keep, limits), Projection::Stopped));
    }
    assert!(matches!(
        scoped(
            formula,
            keep,
            Limits {
                growth,
                nodes,
                ..full
            }
        ),
        Projection::Closed(_)
    ));
}

#[test]
fn distribution_uses_one_branch_and_growth_ledger() {
    let (binding, keep) = fixture();
    let alternatives = op(ChcOp::Or, vec![binding.clone(), binding.clone(), binding]);
    let full = Limits::default();
    assert!(matches!(
        scoped(
            &alternatives,
            &keep,
            Limits {
                branches: 3,
                ..full
            }
        ),
        Projection::Closed(_)
    ));
    assert!(matches!(
        scoped(
            &alternatives,
            &keep,
            Limits {
                branches: 2,
                ..full
            }
        ),
        Projection::Stopped
    ));
    let mut scope = Scope::new(full, &|| true);
    assert!(matches!(
        run(&alternatives, &keep, &mut scope),
        Projection::Closed(_)
    ));
    let consumed = full.growth - scope.remaining.growth;
    assert!(matches!(
        scoped(
            &alternatives,
            &keep,
            Limits {
                growth: consumed - 1,
                ..full
            }
        ),
        Projection::Stopped
    ));
    let deeper = op(ChcOp::Not, vec![op(ChcOp::Not, vec![alternatives])]);
    assert!(matches!(
        scoped(&deeper, &keep, Limits { depth: 1, ..full }),
        Projection::Stopped
    ));
}

#[test]
fn stopped_scope_cannot_recover_as_a_decline_or_closed_fact_fallback() {
    let (formula, keep) = fixture();
    let open = Cell::new(false);
    let callback = || open.get();
    let mut scope = Scope::new(Limits::default(), &callback);
    assert!(matches!(
        run(&formula, &keep, &mut scope),
        Projection::Stopped
    ));
    open.set(true);
    assert!(matches!(
        run(&ChcExpr::Bool(true), &[], &mut scope),
        Projection::Stopped
    ));
    let _deadline = crate::smt::ScopedSmtDeadline::install(Duration::ZERO);
    assert!(matches!(project(&formula, &keep), Projection::Stopped));
    let interp = crate::PredicateInterpretation::new(keep, formula);
    assert!(
        super::super::super::InliningBackTranslator::close_synthesized_interpretation(interp)
            .is_none()
    );
}

#[test]
fn ambient_cancellation_interrupt_and_zero_memory_are_terminal() {
    let (formula, keep) = fixture();
    let token = crate::CancellationToken::new();
    token.cancel();
    {
        let _lane = crate::smt::ScopedLaneCancellation::install(token, None);
        assert!(matches!(project(&formula, &keep), Projection::Stopped));
    }
    {
        let flag = Arc::new(AtomicBool::new(true));
        let _lane = crate::smt::ScopedLaneCancellation::install(
            crate::CancellationToken::new(),
            Some(flag.clone()),
        );
        assert!(matches!(project(&formula, &keep), Projection::Stopped));
        flag.store(false, Ordering::Relaxed);
        assert!(matches!(project(&formula, &keep), Projection::Closed(_)));
    }
    let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
    assert!(matches!(project(&formula, &keep), Projection::Stopped));
}

#[test]
fn oversized_names_and_branch_products_refuse_before_unbounded_growth() {
    let huge = var(&"x".repeat(4096), 4);
    let a = var("a", 4);
    let formula = eq(expr(&a), quotient(&huge, 2));
    assert!(matches!(
        scoped(
            &formula,
            &[a],
            Limits {
                work: 100,
                ..Limits::default()
            }
        ),
        Projection::Stopped
    ));
    let terms: Vec<_> = (0..7)
        .map(|i| {
            op(
                ChcOp::Or,
                vec![
                    eq(expr(&var(&format!("local_{i}"), 2)), ChcExpr::BitVec(0, 2)),
                    ChcExpr::Bool(false),
                ],
            )
        })
        .collect();
    // Even false alternatives consume the shared expansion bound: the limit
    // cannot reset when a cheap branch is discharged.
    assert!(matches!(
        scoped(
            &op(ChcOp::And, terms[..2].to_vec()),
            &[],
            Limits {
                branches: 4,
                ..Limits::default()
            }
        ),
        Projection::Closed(_)
    ));
    assert!(matches!(
        scoped(
            &op(ChcOp::And, terms),
            &[],
            Limits {
                branches: 4,
                ..Limits::default()
            }
        ),
        Projection::Stopped
    ));
}
