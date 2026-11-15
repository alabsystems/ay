// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A counted allowance for the executor runs of the checks on this thread.
//!
//! A wall budget makes a check's answer a function of host load: the same
//! executor run settles inside it on an idle machine and not on a loaded one.
//! While a [`ScopedExecutorWork`] is installed, every executor run a check on
//! this thread makes draws on one allowance of work units (CDCL conflicts plus
//! DPLL(T) split-loop round trips) and of round trips. A run enters what is
//! left as the work ceiling and grant the executor polls
//! (`ay_core::resource::enter_work_ceiling`, `enter_work_grant`). Once the
//! allowance is spent, the next run answers `Unknown` without starting, as
//! after an expired deadline.
//!
//! The count stops executor SEARCH, at the same count on every host: every
//! SAT solve the run makes on this thread, certification's included, charges
//! its conflicts at its stop polls and at its end (`ay-sat`'s
//! `solver/work_report.rs`). It does not stop the phases that charge no unit:
//! preprocessing, encoding, proof bookkeeping, and certification's work
//! outside its SAT searches. And a search reads the ceiling only at its
//! polls, so a run overshoots the allowance before it stops. The caller keeps
//! a wall for both
//! (`pdr::verification::model::counted`). The remainder is read from this
//! thread's work counter, so work done on executor worker threads is not
//! charged to it.
//!
//! The internal DPLL(T) attempts a check makes around its executor keep their
//! wall slices, narrowed to [`ExecutorWork::internal_slice`]. Once the
//! allowance is spent, or when the executor declines a query (nonlinear
//! integer arithmetic, an admission refusal), those slices alone decide the
//! check, as they did before. [`ScopedExecutorWork::lift`] runs a check that
//! can only refuse outside the allowance, on its own budget.

use std::cell::Cell;
use std::time::Duration;

/// The allowance of the executor runs on this thread.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ExecutorWork {
    /// Work units left (conflicts plus round trips).
    pub(crate) units: u64,
    /// Split-loop round trips left.
    pub(crate) round_trips: u64,
    /// The widest internal pre-slice a check takes before its executor.
    pub(crate) internal_slice: Duration,
}

thread_local! {
    static ALLOWANCE: Cell<Option<ExecutorWork>> = const { Cell::new(None) };
}

/// Keeps an allowance installed on this thread; dropping it restores the
/// previous one.
#[must_use = "the allowance is lifted when this scope is dropped"]
pub(crate) struct ScopedExecutorWork {
    prev: Option<ExecutorWork>,
}

impl ScopedExecutorWork {
    pub(crate) fn install(work: ExecutorWork) -> Self {
        let prev = ALLOWANCE.with(|cell| cell.replace(Some(work)));
        Self { prev }
    }

    /// Lift any installed allowance until the returned scope drops. For a
    /// check that can only refuse (the #6787 executor cross-check): it keeps
    /// its own budget, whatever the rule around it has spent.
    pub(crate) fn lift() -> Self {
        let prev = ALLOWANCE.with(|cell| cell.replace(None));
        Self { prev }
    }
}

impl Drop for ScopedExecutorWork {
    fn drop(&mut self) {
        let prev = self.prev;
        // `try_with`: never panic in a destructor, even during thread teardown.
        let _ = ALLOWANCE.try_with(|cell| cell.set(prev));
    }
}

/// Whether the allowance installed on this thread is spent.
pub(crate) fn executor_work_spent() -> bool {
    ALLOWANCE
        .with(Cell::get)
        .is_some_and(|work| work.units == 0 || work.round_trips == 0)
}

/// `slice`, narrowed to the installed allowance's pre-slice width.
pub(crate) fn narrow_internal_slice(slice: Duration) -> Duration {
    ALLOWANCE
        .with(Cell::get)
        .map_or(slice, |work| slice.min(work.internal_slice))
}

/// One executor run's draw on the installed allowance.
pub(crate) enum ExecutorDraw {
    /// No allowance is installed: the run is bounded by its wall alone.
    Unmetered,
    /// The allowance is spent: the run must answer `Unknown` without starting.
    Spent,
    /// The run is entered under what the allowance has left, and charges it
    /// what it spends when this is dropped.
    Open(OpenDraw),
}

/// An executor run entered under the allowance's work ceiling and grant.
pub(crate) struct OpenDraw {
    // Declared before `units` so it is dropped first: it was entered last.
    round_trips: ay_core::resource::WorkGrantScope,
    units: ay_core::resource::WorkCeilingScope,
    units_before: u64,
}

/// Open the draw of one executor run on this thread.
pub(crate) fn draw_executor_work() -> ExecutorDraw {
    match ALLOWANCE.with(Cell::get) {
        None => ExecutorDraw::Unmetered,
        Some(work) if work.units == 0 || work.round_trips == 0 => ExecutorDraw::Spent,
        Some(work) => {
            let units_before = ay_core::resource::thread_work_units();
            let units = ay_core::resource::enter_work_ceiling(Some(work.units));
            ExecutorDraw::Open(OpenDraw {
                round_trips: ay_core::resource::enter_work_grant(work.round_trips),
                units,
                units_before,
            })
        }
    }
}

impl Drop for OpenDraw {
    fn drop(&mut self) {
        let spent_units = ay_core::resource::thread_work_units().saturating_sub(self.units_before);
        let units_spent = self.units.spent();
        let spent_round_trips = self.round_trips.spent_round_trips();
        let _ = ALLOWANCE.try_with(|cell| {
            if let Some(mut work) = cell.get() {
                work.units = if units_spent {
                    0
                } else {
                    work.units.saturating_sub(spent_units)
                };
                // A grant is spent once MORE than it allows is counted.
                work.round_trips = work.round_trips.saturating_sub(spent_round_trips);
                cell.set(Some(work));
            }
        });
    }
}

#[cfg(test)]
#[path = "executor_work_tests.rs"]
mod tests;
