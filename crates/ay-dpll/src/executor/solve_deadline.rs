// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Live, shared solve-deadline cell (#quantifier-determinism).
//!
//! `Executor::solve_deadline` used to be a plain `Option<Instant>` that stop
//! closures captured BY VALUE at construction. The quantified-solve wall-clock
//! backstop (`Executor::install_quantifier_deadline_backstop`) extends the
//! deadline MID-CALL, so any stop closure built before the install kept
//! polling the stale nominal deadline and stopped the solve at the
//! pre-extension wall — silently defeating the determinism goal (observed in
//! the deductive-checks bump triage: a solve stopped at exactly the nominal 300s
//! despite `backstop installed: remaining=110s extra=180s`).
//!
//! This cell is the single LIVE source of truth for the executor's deadline:
//! stop closures capture a cheap [`SolveDeadlineCell`] handle (`Clone` shares
//! the same cell) and decode at poll time, so mid-call installs, backstop
//! extensions, alternation-validation sub-deadline tightenings, and per-call
//! restores are all visible to every closure regardless of when it was built.
//!
//! VERDICT SAFETY: the cell only changes WHEN a solve observes its deadline,
//! never a verdict — every deadline break in the pipeline routes to
//! fail-closed `Unknown(Timeout/QuantifierRoundLimit/...)`, and later stops
//! (extension visible) can only allow deterministic work to converge to a
//! genuine Sat/Unsat; earlier stops (tightening visible) can only degrade to
//! Unknown.
//!
//! Lock discipline: the mutex is held only for a `Copy` read/write of an
//! `Option<Instant>` — no user code runs under the lock, so poisoning is
//! impossible in practice; reads fall back to the poisoned value anyway.

use ay_core::time::Instant;
use std::sync::{Arc, Mutex};

/// Shared live view of the executor's solve deadline.
///
/// `Clone` yields a HANDLE to the same cell (deliberate: closures and
/// watchdog threads capture clones and observe live updates). To snapshot a
/// value (e.g. save/restore around a sub-solve window), use [`Self::get`].
#[derive(Debug, Clone, Default)]
pub(crate) struct SolveDeadlineCell {
    cell: Arc<Mutex<Option<Instant>>>,
}

impl SolveDeadlineCell {
    /// A fresh cell with no deadline installed.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Read the current deadline (value snapshot at THIS instant).
    pub(crate) fn get(&self) -> Option<Instant> {
        match self.cell.lock() {
            Ok(guard) => *guard,
            Err(poisoned) => *poisoned.into_inner(),
        }
    }

    /// Install/replace/clear the deadline. Visible immediately to every
    /// handle cloned from this cell.
    pub(crate) fn set(&self, deadline: Option<Instant>) {
        match self.cell.lock() {
            Ok(mut guard) => *guard = deadline,
            Err(poisoned) => *poisoned.into_inner() = deadline,
        }
    }

    /// Live poll: is a deadline installed AND already passed?
    pub(crate) fn expired(&self) -> bool {
        self.get().is_some_and(|dl| Instant::now() >= dl)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn handles_share_live_updates() {
        let cell = SolveDeadlineCell::new();
        let handle = cell.clone();
        assert_eq!(handle.get(), None);
        assert!(!handle.expired());
        let past = Instant::now() - Duration::from_millis(1);
        cell.set(Some(past));
        assert_eq!(handle.get(), Some(past));
        assert!(handle.expired());
        let future = Instant::now() + Duration::from_secs(60);
        cell.set(Some(future));
        assert!(!handle.expired());
        cell.set(None);
        assert_eq!(handle.get(), None);
        assert!(!handle.expired());
    }
}
