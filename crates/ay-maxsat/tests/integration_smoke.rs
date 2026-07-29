// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use ay_maxsat::{MaxSatResult, MaxSatSolver};

#[test]
fn weighted_partial_instance_returns_expected_cost() {
    let mut solver = MaxSatSolver::new();

    // Hard requirement: x1 must be true.
    solver.add_hard_clause(vec![1]);

    // Weighted soft preferences.
    solver.add_soft_clause(vec![1], 10);
    solver.add_soft_clause(vec![-1], 3);
    solver.add_soft_clause(vec![2], 2);

    match solver.solve() {
        MaxSatResult::Optimal { cost, .. } => assert_eq!(cost, 3),
        other => panic!("expected Optimal result, got {other:?}"),
    }
}

#[test]
fn conflicting_hard_clauses_are_unsatisfiable() {
    let mut solver = MaxSatSolver::new();
    solver.add_hard_clause(vec![1]);
    solver.add_hard_clause(vec![-1]);

    assert!(matches!(solver.solve(), MaxSatResult::Unsatisfiable));
}

/// A supplied deadline changes *scheduling*, never the answer.
///
/// The engine was historically budget-blind (`should_stop` says whether to stop
/// now, never how much budget remains), which forced every internal policy to
/// be a fixed constant tuned at one timeout. `set_deadline` closes that gap, so
/// the invariant worth pinning is that the reported optimum is identical with
/// and without it — including with the descent levers the deadline feeds.
#[test]
fn a_supplied_deadline_does_not_change_the_optimum() {
    fn build() -> MaxSatSolver {
        let mut s = MaxSatSolver::new();
        s.add_hard_clause(vec![1, 2, 3]);
        s.add_hard_clause(vec![-1, -2]);
        s.add_hard_clause(vec![-2, -3]);
        for (lits, w) in [
            (vec![-1], 5u64),
            (vec![-2], 4),
            (vec![-3], 3),
            (vec![2, 3], 7),
            (vec![1, -3], 2),
        ] {
            s.add_soft_clause(lits, w);
        }
        s
    }

    let blind = match build().solve() {
        MaxSatResult::Optimal { cost, .. } => cost,
        other => panic!("expected Optimal, got {other:?}"),
    };

    let mut timed = build();
    timed.set_deadline(Some(
        std::time::Instant::now() + std::time::Duration::from_secs(120),
    ));
    match timed.solve_interruptible(&|| false, &mut |_| {}) {
        MaxSatResult::Optimal { cost, .. } => assert_eq!(
            cost, blind,
            "deadline-aware scheduling changed the reported optimum"
        ),
        other => panic!("expected Optimal, got {other:?}"),
    }

    // `None` must restore the exact budget-blind path.
    let mut cleared = build();
    cleared.set_deadline(None);
    match cleared.solve_interruptible(&|| false, &mut |_| {}) {
        MaxSatResult::Optimal { cost, .. } => assert_eq!(cost, blind),
        other => panic!("expected Optimal, got {other:?}"),
    }
}
