// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::{Literal, Variable};
use ay_core::time::Instant;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

fn future() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn unit_solver() -> Solver {
    let mut solver = Solver::new(1);
    solver.set_ic3_mode();
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
    solver
}

#[test]
fn deadline_sampling_is_bounded_without_an_interrupt_flag() {
    let mut solver = unit_solver();
    solver.set_solve_deadline(Some(future()));
    let mut poll = DeadlinePoll::new();
    assert_eq!(poll.check(&solver), None);
    // Advance only the deadline, deterministically, between active-loop polls.
    solver.set_solve_deadline(Some(Instant::now()));
    for _ in 0..DEADLINE_INTERVAL - 1 {
        assert_eq!(poll.check(&solver), None);
    }
    assert_eq!(
        poll.check(&solver),
        Some(SatUnknownReason::DeadlineExceeded)
    );
}

#[test]
fn first_search_poll_and_every_interrupt_poll_remain_immediate() {
    let mut solver = unit_solver();
    solver.set_solve_deadline(Some(Instant::now()));
    assert_eq!(
        DeadlinePoll::new().check(&solver),
        Some(SatUnknownReason::DeadlineExceeded)
    );
    solver.set_solve_deadline(None);
    let flag = Arc::new(AtomicBool::new(false));
    solver.set_interrupt(flag.clone());
    let mut poll = DeadlinePoll::new();
    assert_eq!(poll.check(&solver), None);
    flag.store(true, Ordering::Relaxed);
    assert_eq!(poll.check(&solver), Some(SatUnknownReason::Interrupted));
    // Once the atomic is set, even an unforced poll refines an expired deadline.
    solver.set_solve_deadline(Some(Instant::now()));
    assert_eq!(
        poll.check(&solver),
        Some(SatUnknownReason::DeadlineExceeded)
    );
}

#[test]
fn initial_unit_conflict_and_empty_formula_cannot_publish_after_expiry() {
    let mut contradictory = unit_solver();
    contradictory.add_clause(vec![Literal::negative(Variable::new(0))]);
    let mut empty = Solver::new(1);
    empty.set_ic3_mode();
    for mut solver in std::iter::once(contradictory).chain(std::iter::once(empty)) {
        solver.set_solve_deadline(Some(Instant::now()));
        assert!(matches!(
            solver.solve_incremental_ic3(&[]).into_inner(),
            AssumeResult::Unknown
        ));
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::DeadlineExceeded)
        );
    }
}

#[test]
fn after_cleanup_gate_discards_actual_sat_and_unsat_results() {
    let positive = Literal::positive(Variable::new(0));
    for assumptions in [vec![], vec![positive.negated()]] {
        let mut solver = unit_solver();
        solver.set_solve_deadline(Some(future()));
        let result = solver.solve_incremental_ic3(&assumptions).into_inner();
        assert!(matches!(
            result,
            AssumeResult::Sat(_) | AssumeResult::Unsat(..)
        ));
        // The result is genuine; only the post-cleanup admission clock expires.
        solver.set_solve_deadline(Some(Instant::now()));
        assert!(matches!(
            solver.finish_ic3_query(result),
            AssumeResult::Unknown
        ));
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::DeadlineExceeded)
        );
    }
}

#[test]
fn explicit_new_query_may_reset_interrupt_without_poisoning_the_formula() {
    let flag = Arc::new(AtomicBool::new(true));
    let mut solver = unit_solver();
    solver.set_interrupt(flag.clone());
    assert!(matches!(
        solver.solve_incremental_ic3(&[]).into_inner(),
        AssumeResult::Unknown
    ));
    flag.store(false, Ordering::Relaxed);
    let live = solver.solve_incremental_ic3(&[]).into_inner();
    assert!(matches!(live, AssumeResult::Sat(_)));
    assert_eq!(solver.last_unknown_reason(), None);
    // Learned/base clauses were not replaced by a spurious contradiction.
    let opposite = [Literal::negative(Variable::new(0))];
    assert!(matches!(
        solver.solve_incremental_ic3(&opposite).into_inner(),
        AssumeResult::Unsat(..)
    ));
}

#[test]
fn no_deadline_and_future_deadline_keep_sat_and_unsat_semantics() {
    for deadline in [None, Some(future())] {
        let mut solver = unit_solver();
        solver.set_solve_deadline(deadline);
        assert!(matches!(
            solver.solve_incremental_ic3(&[]).into_inner(),
            AssumeResult::Sat(_)
        ));
        let opposite = [Literal::negative(Variable::new(0))];
        assert!(matches!(
            solver.solve_incremental_ic3(&opposite).into_inner(),
            AssumeResult::Unsat(..)
        ));
    }
}

mod resources;
