// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::atomic::Ordering;
use std::time::Duration;

use ay_sat::SatUnknownReason;

use super::*;

fn unknown_reason(solver: &mut SatSolver) -> Option<SatUnknownReason> {
    assert!(matches!(solver.solve().into_inner(), SatResult::Unknown));
    solver.last_unknown_reason()
}

#[test]
fn deadline_timer_never_writes_the_callers_flag_8961() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let mut solver = SatSolver::new(1);
    let _stop = install_sat_stop(
        &mut solver,
        Some(Arc::clone(&interrupt)),
        Some(Instant::now()),
    );
    assert!(
        !interrupt.load(Ordering::Relaxed),
        "the deadline timer must not set the reusable API interrupt flag"
    );
}

#[test]
fn expired_deadline_keeps_timeout_provenance() {
    let mut solver = SatSolver::new(1);
    let _stop = install_sat_stop(
        &mut solver,
        Some(Arc::new(AtomicBool::new(true))),
        Some(Instant::now()),
    );
    assert_eq!(
        unknown_reason(&mut solver),
        Some(SatUnknownReason::DeadlineExceeded)
    );
}

#[test]
fn reused_solver_rebinds_query_controls() {
    let mut solver = SatSolver::new(1);
    {
        let _stop = install_sat_stop(&mut solver, Some(Arc::new(AtomicBool::new(true))), None);
        assert_eq!(
            unknown_reason(&mut solver),
            Some(SatUnknownReason::Interrupted)
        );
    }
    {
        let _stop = install_sat_stop(&mut solver, None, Some(Instant::now()));
        assert_eq!(
            unknown_reason(&mut solver),
            Some(SatUnknownReason::DeadlineExceeded)
        );
    }
    // The earlier query's raised deadline flag is dropped with its deadline.
    let _stop = install_sat_stop(&mut solver, None, None);
    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));
}

/// The passes that poll only the solver's interrupt flags see a passed
/// deadline through the deadline flag, not the clock. With the clock-read
/// deadline taken away, the flag alone still stops the solve.
#[test]
fn a_passed_deadline_raises_the_solvers_deadline_flag() {
    let mut solver = SatSolver::new(1);
    let _stop = install_sat_stop(&mut solver, None, Some(Instant::now()));
    solver.set_solve_deadline(None);
    assert_eq!(
        unknown_reason(&mut solver),
        Some(SatUnknownReason::Interrupted)
    );
}

/// The caller's flag stays live while a deadline is armed: one raised after
/// the stop was installed still reaches the passes.
#[test]
fn the_callers_flag_stays_live_beside_an_armed_deadline() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let mut solver = SatSolver::new(1);
    let _stop = install_sat_stop(
        &mut solver,
        Some(Arc::clone(&interrupt)),
        Some(Instant::now() + Duration::from_secs(3600)),
    );
    interrupt.store(true, Ordering::Relaxed);
    assert_eq!(
        unknown_reason(&mut solver),
        Some(SatUnknownReason::Interrupted)
    );
}

/// The FP lanes' search: only the forwarded stop can end it, since the lane
/// poll here never asks to stop.
#[test]
fn query_search_carries_the_query_interrupt_and_deadline() {
    let mut executor = Executor::new();
    let mut solver = SatSolver::new(1);

    executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);
    let result = executor.solve_sat_under_query_stop(&mut solver, || false);
    assert!(matches!(result, SatResult::Unknown));
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::Interrupted)
    );

    executor.set_solve_controls(None, Some(Instant::now()));
    let result = executor.solve_sat_under_query_stop(&mut solver, || false);
    assert!(matches!(result, SatResult::Unknown));
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::DeadlineExceeded)
    );

    // Rebound for a query with neither, the same solver answers.
    executor.set_solve_controls(None, None);
    let result = executor.solve_sat_under_query_stop(&mut solver, || false);
    assert!(matches!(result, SatResult::Sat(_)));
    assert_eq!(searches::take().len(), 3);
}
