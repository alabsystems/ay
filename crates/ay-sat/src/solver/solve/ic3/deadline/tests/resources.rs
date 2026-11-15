// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

#[test]
fn original_callback_refuses_empty_and_conflict_before_native_evidence() {
    let mut conflict = unit_solver();
    conflict.add_clause(vec![Literal::negative(Variable::new(0))]);
    let mut empty = Solver::new(1);
    empty.set_ic3_mode();
    for mut solver in [conflict, empty] {
        let calls = Cell::new(0);
        let result = solver.solve_incremental_ic3_interruptible(&[], || {
            calls.set(calls.get() + 1);
            true
        });
        assert!(matches!(result.into_inner(), AssumeResult::Unknown));
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::Interrupted)
        );
        assert_eq!(calls.get(), 1);
    }
}

#[test]
fn original_callback_is_sampled_with_the_same_256_iteration_wall_poll() {
    let solver = unit_solver();
    let stopped = Cell::new(false);
    let calls = Cell::new(0);
    let stop = || {
        calls.set(calls.get() + 1);
        stopped.get()
    };
    let mut poll = DeadlinePoll::new();
    assert_eq!(poll.check_controlled(&solver, &stop), None);
    stopped.set(true);
    for _ in 0..DEADLINE_INTERVAL - 1 {
        assert_eq!(poll.check_controlled(&solver, &stop), None);
    }
    assert_eq!(calls.get(), 1);
    assert_eq!(
        poll.check_controlled(&solver, &stop),
        Some(SatUnknownReason::Interrupted)
    );
    assert_eq!(calls.get(), 2);
}

#[test]
fn callback_refusal_inside_setup_is_sticky_through_original_cleanup() {
    let calls = Cell::new(0);
    let mut solver = unit_solver();
    let result = solver.solve_incremental_ic3_interruptible(&[], || {
        calls.set(calls.get() + 1);
        calls.get() == 2
    });
    assert!(matches!(result.into_inner(), AssumeResult::Unknown));
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::Interrupted)
    );
    assert_eq!(calls.get(), 2);
}

#[test]
fn post_cleanup_callback_discards_genuine_sat_and_unsat_origin_data() {
    for assumptions in [vec![], vec![Literal::negative(Variable::new(0))]] {
        let mut solver = unit_solver();
        let result = solver.solve_incremental_ic3(&assumptions).into_inner();
        assert!(matches!(
            result,
            AssumeResult::Sat(_) | AssumeResult::Unsat(..)
        ));
        assert!(matches!(
            solver.finish_ic3_query_controlled(result, &|| true),
            AssumeResult::Unknown
        ));
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::Interrupted)
        );
    }
}

#[test]
fn expired_original_deadline_retains_priority_over_new_callback() {
    let mut solver = unit_solver();
    solver.set_solve_deadline(Some(Instant::now()));
    let calls = Cell::new(0);
    assert!(matches!(
        solver
            .solve_incremental_ic3_interruptible(&[], || {
                calls.set(calls.get() + 1);
                true
            })
            .into_inner(),
        AssumeResult::Unknown
    ));
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::DeadlineExceeded)
    );
    assert_eq!(calls.get(), 0);
}

#[test]
fn inherited_deadline_interrupt_is_not_replaced_by_callback_plumbing() {
    let flag = Arc::new(AtomicBool::new(true));
    let mut solver = unit_solver();
    solver.set_deadline_interrupt_handle(Some(flag.clone()));
    assert!(matches!(
        solver
            .solve_incremental_ic3_interruptible(&[], || false)
            .into_inner(),
        AssumeResult::Unknown
    ));
    // An atomic deadline flag alone does not invent clock-expiry provenance.
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::Interrupted)
    );
    assert!(flag.load(Ordering::Relaxed));
}

#[test]
fn fresh_outer_query_preserves_formula_and_incremental_assumption_semantics() {
    let mut solver = unit_solver();
    assert!(matches!(
        solver
            .solve_incremental_ic3_interruptible(&[], || true)
            .into_inner(),
        AssumeResult::Unknown
    ));
    assert!(matches!(
        solver
            .solve_incremental_ic3_interruptible(&[], || false)
            .into_inner(),
        AssumeResult::Sat(_)
    ));
    assert!(matches!(
        solver
            .solve_incremental_ic3_interruptible(&[Literal::negative(Variable::new(0))], || false)
            .into_inner(),
        AssumeResult::Unsat(..)
    ));
    assert_eq!(solver.last_unknown_reason(), None);
}
