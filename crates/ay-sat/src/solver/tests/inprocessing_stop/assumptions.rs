// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The assumption solve's incremental inprocessing round under the solve's
//! stop: the round polls it on entry and between its passes, and a stop it
//! sees ends the solve Unknown, even over an UNSAT the round then finds.

use super::*;

/// The assumption solve's incremental round polls the solve's stop: one
/// that fired ends the solve Unknown, though the round would have found
/// the empty clause right after its first poll. Before, the round polled
/// only the interrupt flags and the solve answered UNSAT.
#[test]
fn the_incremental_round_ends_the_solve_when_the_stop_fired() {
    let mut idle = solver_with_probe_roots(2);
    idle.mark_empty_clause();
    let polls = Cell::new(0_u32);
    let ended = idle.run_incremental_inprocessing_round_until(Some(&stop_at(&polls, u32::MAX)));
    assert!(matches!(ended, Some(AssumeResult::Unsat(..))), "{ended:?}");
    assert_eq!(polls.get(), 1, "polled on entry");
    let mut unpolled = solver_with_probe_roots(2);
    unpolled.mark_empty_clause();
    let ended = unpolled.run_incremental_inprocessing_round_until::<dyn Fn() -> bool>(None);
    assert!(matches!(ended, Some(AssumeResult::Unsat(..))), "{ended:?}");

    let mut stopped = solver_with_probe_roots(2);
    stopped.mark_empty_clause();
    let polls = Cell::new(0_u32);
    let ended = stopped.run_incremental_inprocessing_round_until(Some(&stop_at(&polls, 1)));
    assert!(matches!(ended, Some(AssumeResult::Unknown)), "{ended:?}");
    assert_eq!(polls.get(), 1);
    assert_eq!(
        stopped.last_unknown_reason(),
        Some(SatUnknownReason::Interrupted)
    );
    assert!(
        !stopped.cold.inprocessing_caller_stop,
        "the round took the latch"
    );
}

/// `(a v b v c)`, `(-a v d)`, `(-b v e)`, `(-d v -e v f)`, after one
/// assumption solve; `open` makes the next assumption solve's incremental
/// inprocessing round due.
fn assumption_round_solver(open: bool) -> Solver {
    let mut solver: Solver = Solver::new(6);
    let pos = |v: u32| Literal::positive(Variable(v));
    let neg = |v: u32| Literal::negative(Variable(v));
    solver.add_clause(vec![pos(0), pos(1), pos(2)]);
    solver.add_clause(vec![neg(0), pos(3)]);
    solver.add_clause(vec![neg(1), pos(4)]);
    solver.add_clause(vec![neg(3), neg(4), pos(5)]);
    assert!(solver.solve_with_assumptions(&[pos(5)]).is_sat());
    if open {
        solver.cold.lifetime_conflicts = 100;
        solver.cold.next_inprobe_conflict = 0;
        solver.cold.last_inprobe_reduction = 0;
    }
    solver
}

/// Through `solve_with_assumptions_interruptible`: the incremental round the
/// solve runs polls the solve's stop on entry and between its passes, and a
/// stop that fires at any of those polls ends the solve Unknown there. With
/// the round not due the solve polls only on entry and answers SAT (the
/// negative twin). Before, the assumption path ran the round with no stop,
/// so the open solve polled no more than the closed one and answered SAT.
#[test]
fn a_stop_ends_solve_with_assumptions_at_its_incremental_round() {
    let assumption = [Literal::positive(Variable(5))];
    let idle_polls = |open: bool| {
        let mut solver = assumption_round_solver(open);
        let polls = Cell::new(0_u32);
        let result =
            solver.solve_with_assumptions_interruptible(&assumption, stop_at(&polls, u32::MAX));
        assert!(result.is_sat(), "open {open}");
        polls.get()
    };
    let closed = idle_polls(false);
    let open = idle_polls(true);
    assert!(
        open > closed + 1,
        "the round polls the stop on entry and between passes: {open} vs {closed}"
    );

    let mut not_due = assumption_round_solver(false);
    let polls = Cell::new(0_u32);
    let result =
        not_due.solve_with_assumptions_interruptible(&assumption, stop_at(&polls, closed + 1));
    assert!(result.is_sat(), "no round, no later poll");

    for fire_at in closed + 1..=open {
        let mut solver = assumption_round_solver(true);
        let polls = Cell::new(0_u32);
        let result =
            solver.solve_with_assumptions_interruptible(&assumption, stop_at(&polls, fire_at));
        assert!(
            !result.is_sat() && !result.is_unsat(),
            "{fire_at}: the stop fired in the round"
        );
        assert_eq!(polls.get(), fire_at, "not polled again");
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::Interrupted)
        );
    }
}
