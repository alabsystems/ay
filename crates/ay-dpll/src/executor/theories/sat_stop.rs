// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One query's stop, handed to a bit-blast SAT solver (BV and FP lanes).

use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use ay_core::time::Instant;
use ay_sat::{SatResult, Solver as SatSolver};

use super::super::Executor;
use crate::executor::solve_deadline::DeadlineAlarm;

/// Keeps a solver's deadline alarm armed; dropping it stops the alarm's
/// timer.
#[must_use = "the deadline timer stops when the guard is dropped"]
pub(super) struct SatStopGuard {
    _alarm: Option<DeadlineAlarm>,
}

/// Hand a bit-blast SAT solver one query's stop: the caller's interrupt flag,
/// the solve deadline, and a SAT-local flag that a timer raises at that
/// deadline (#8554, #8782; the timer is a [`DeadlineAlarm`]).
///
/// A `should_stop` closure reaches only the search loop and the gaps between
/// preprocessing passes. Inside a pass the solver polls its own interrupt
/// flags, which never read the clock, and only some passes also check the
/// deadline; the timer's flag stops the rest at their next poll. The deadline
/// keeps such a stop reported as `DeadlineExceeded`. The timer writes only its
/// own flag, never the caller's, which API callers reuse across checks
/// (#8961), and the caller's flag stays visible to the passes throughout.
///
/// Absent controls are rebound too, so a persistent solver carries no earlier
/// query's flag or deadline into this one.
pub(super) fn install_sat_stop(
    solver: &mut SatSolver,
    interrupt: Option<Arc<AtomicBool>>,
    deadline: Option<Instant>,
) -> SatStopGuard {
    solver.set_interrupt_handle(interrupt);
    solver.set_solve_deadline(deadline);
    let Some(deadline) = deadline else {
        solver.set_deadline_interrupt_handle(None);
        return SatStopGuard { _alarm: None };
    };
    let alarm = DeadlineAlarm::arm(deadline);
    solver.set_deadline_interrupt_handle(Some(alarm.flag()));
    SatStopGuard {
        _alarm: Some(alarm),
    }
}

impl Executor {
    /// Run one bit-blast SAT search under this query's stop
    /// (`install_sat_stop`), with `should_stop` as the lane's own poll. The
    /// FP lanes search through here.
    pub(in crate::executor) fn solve_sat_under_query_stop(
        &self,
        solver: &mut SatSolver,
        should_stop: impl Fn() -> bool,
    ) -> SatResult {
        let interrupt = self.solve_interrupt.clone();
        let deadline = self.solve_deadline.get();
        #[cfg(test)]
        searches::record(interrupt.clone(), deadline, solver);
        let _stop = install_sat_stop(solver, interrupt, deadline);
        #[cfg(test)]
        let should_stop = super::slow_host::slow_poll(should_stop);
        solver.solve_interruptible(should_stop).into_inner()
    }
}

/// The stops the SAT searches on this thread ran under, for tests that check
/// a lane searches through `solve_sat_under_query_stop`.
#[cfg(test)]
pub(in crate::executor) mod searches {
    use std::cell::RefCell;

    use super::*;

    /// One search's stop, and the counts it was armed with.
    pub(in crate::executor) struct SearchStop {
        pub(in crate::executor) interrupt: Option<Arc<AtomicBool>>,
        pub(in crate::executor) deadline: Option<Instant>,
        /// The solver's conflict and decision budgets (absolute targets).
        pub(in crate::executor) conflict_budget: Option<u64>,
        pub(in crate::executor) decision_budget: Option<u64>,
        /// Whether its inner schedules were counted work
        /// (`SatSolver::deterministic_inproc`).
        pub(in crate::executor) counted: bool,
    }

    thread_local! {
        static SEARCHES: RefCell<Vec<SearchStop>> = const { RefCell::new(Vec::new()) };
    }

    pub(super) fn record(
        interrupt: Option<Arc<AtomicBool>>,
        deadline: Option<Instant>,
        solver: &SatSolver,
    ) {
        SEARCHES.with(|searches| {
            searches.borrow_mut().push(SearchStop {
                interrupt,
                deadline,
                conflict_budget: solver.conflict_budget(),
                decision_budget: solver.decision_budget(),
                counted: solver.deterministic_inproc(),
            });
        });
    }

    /// The searches recorded since the last call, oldest first.
    pub(in crate::executor) fn take() -> Vec<SearchStop> {
        SEARCHES.with(|searches| searches.take())
    }
}

#[cfg(test)]
#[path = "sat_stop/tests.rs"]
mod tests;
