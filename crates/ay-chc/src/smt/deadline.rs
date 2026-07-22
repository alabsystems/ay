// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Thread-local SMT deadline: a hard wall-clock budget that every
//! `SmtContext::check_sat*` call on the current thread respects.
//!
//! Motivation (#lustre-latency): engine-level budgets (e.g. the adaptive
//! LIA/Farkas route's 3s) were enforced only at coarse loop boundaries.
//! A single helper such as `check_sat_with_ite_case_split_recursive` can
//! issue hundreds of SMT checks (8-way OR splits, depth 3 ⇒ up to 512
//! leaves) with no cancellation consultation, overrunning the budget by an
//! order of magnitude. Threading a token through every call site is
//! invasive and easy to miss; instead, the owning solver installs a scoped
//! deadline here and every SMT check on the thread clamps to it.
//!
//! Semantics:
//! - Nested installs never EXTEND an enclosing deadline (min is kept).
//! - With no deadline installed, behavior is unchanged.
//! - An expired deadline makes checks return `Unknown` immediately, which
//!   every caller already treats as a sound "give up" signal.

use ay_core::time::Instant;
use std::cell::Cell;
use std::time::Duration;

thread_local! {
    static THREAD_SMT_DEADLINE: Cell<Option<Instant>> = const { Cell::new(None) };
}

/// RAII guard for a thread-local SMT deadline scope.
pub(crate) struct ScopedSmtDeadline {
    prev: Option<Instant>,
}

impl ScopedSmtDeadline {
    /// Install a deadline `budget` from now. Nested scopes keep the
    /// earlier of the enclosing and the new deadline.
    pub(crate) fn install(budget: Duration) -> Self {
        Self::install_until(Instant::now() + budget)
    }

    /// Install an absolute deadline. Nested scopes keep the earlier of the
    /// enclosing and the new deadline.
    pub(crate) fn install_until(deadline: Instant) -> Self {
        let prev = THREAD_SMT_DEADLINE.with(Cell::get);
        let effective = match prev {
            Some(enclosing) => enclosing.min(deadline),
            None => deadline,
        };
        THREAD_SMT_DEADLINE.with(|cell| cell.set(Some(effective)));
        Self { prev }
    }
}

impl Drop for ScopedSmtDeadline {
    fn drop(&mut self) {
        let prev = self.prev;
        THREAD_SMT_DEADLINE.with(|cell| cell.set(prev));
    }
}

/// RAII guard that REPLACES (rather than tightens) the thread SMT deadline for
/// a bounded, terminal side-computation.
///
/// [`ScopedSmtDeadline`] deliberately only ever tightens, so nested code has no
/// way to obtain budget once an enclosing scope is exhausted. That is correct
/// for anything whose result feeds back into the enclosing engine's search: the
/// enclosing budget is what bounds that search.
///
/// It is WRONG for ground back-translation. That computation runs inside the
/// BMC probe's own deadline (`bmc/mod.rs` `BmcSolver::solve`), by which point
/// the probe has consumed nearly all of it, so every witness solve issued there
/// receives only the few-millisecond remainder no matter what it asks for —
/// which reads at the call site exactly like a theory failure. (It was misread
/// as one: see the note in `ground_derivation/complete.rs`.)
///
/// # Soundness
///
/// The enclosing deadline exists to bound WALL-CLOCK, not to protect any
/// verdict. Back-translation is terminal and verdict-neutral: its output is a
/// candidate ground environment handed to
/// [`crate::ground_derivation::validate_ground_derivation`], which re-evaluates
/// every ORIGINAL clause against it and remains the sole acceptance anchor.
/// Overrunning a wall-clock budget here can therefore only cost time; it can
/// never admit a wrong answer. The previous deadline is restored on drop, so
/// the enclosing engine's budget accounting resumes unchanged, and the
/// enclosing engine's `cancel_after` token is untouched so a true global
/// timeout still preempts.
///
/// Use ONLY for that purpose, and always with a hard cap.
pub(crate) struct ScopedSmtDeadlineOverride {
    prev: Option<Instant>,
}

impl ScopedSmtDeadlineOverride {
    /// Replace the thread deadline with `budget` from now, ignoring (but
    /// restoring) any enclosing deadline.
    pub(crate) fn install(budget: Duration) -> Self {
        let prev = THREAD_SMT_DEADLINE.with(Cell::get);
        THREAD_SMT_DEADLINE.with(|cell| cell.set(Some(Instant::now() + budget)));
        Self { prev }
    }
}

impl Drop for ScopedSmtDeadlineOverride {
    fn drop(&mut self) {
        let prev = self.prev;
        THREAD_SMT_DEADLINE.with(|cell| cell.set(prev));
    }
}

/// Remaining time before the thread's SMT deadline; `None` if unbounded.
pub(crate) fn smt_deadline_remaining() -> Option<Duration> {
    THREAD_SMT_DEADLINE
        .with(Cell::get)
        .map(|deadline| deadline.saturating_duration_since(Instant::now()))
}

/// True if a thread-local SMT deadline is installed and has passed.
pub(crate) fn smt_deadline_expired() -> bool {
    matches!(smt_deadline_remaining(), Some(remaining) if remaining.is_zero())
}

/// Clamp a per-check timeout to the thread deadline.
///
/// Returns `Err(())` when the deadline has already expired (callers should
/// return `SmtResult::Unknown`), otherwise the effective timeout to use
/// (`None` = unbounded, only when no deadline is installed either).
pub(crate) fn clamp_timeout_to_smt_deadline(
    timeout: Option<Duration>,
) -> Result<Option<Duration>, ()> {
    match smt_deadline_remaining() {
        None => Ok(timeout),
        Some(remaining) if remaining.is_zero() => Err(()),
        Some(remaining) => Ok(Some(match timeout {
            Some(t) => t.min(remaining),
            None => remaining,
        })),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_deadline_is_unbounded() {
        assert_eq!(smt_deadline_remaining(), None);
        assert!(!smt_deadline_expired());
        assert_eq!(
            clamp_timeout_to_smt_deadline(Some(Duration::from_secs(5))),
            Ok(Some(Duration::from_secs(5)))
        );
        assert_eq!(clamp_timeout_to_smt_deadline(None), Ok(None));
    }

    #[test]
    fn install_and_drop_restores() {
        {
            let _guard = ScopedSmtDeadline::install(Duration::from_secs(60));
            assert!(smt_deadline_remaining().is_some());
            assert!(!smt_deadline_expired());
        }
        assert_eq!(smt_deadline_remaining(), None);
    }

    #[test]
    fn nested_never_extends() {
        let _outer = ScopedSmtDeadline::install(Duration::from_millis(50));
        let outer_remaining = smt_deadline_remaining().unwrap();
        {
            let _inner = ScopedSmtDeadline::install(Duration::from_secs(60));
            // Inner scope must keep the tighter outer deadline.
            assert!(smt_deadline_remaining().unwrap() <= Duration::from_millis(50));
        }
        assert!(smt_deadline_remaining().unwrap() <= outer_remaining);
    }

    #[test]
    fn expired_deadline_clamps_to_err() {
        let _guard = ScopedSmtDeadline::install(Duration::ZERO);
        std::thread::sleep(Duration::from_millis(2));
        assert!(smt_deadline_expired());
        assert_eq!(
            clamp_timeout_to_smt_deadline(Some(Duration::from_secs(5))),
            Err(())
        );
    }

    #[test]
    fn clamp_caps_requested_timeout() {
        let _guard = ScopedSmtDeadline::install(Duration::from_millis(100));
        let clamped = clamp_timeout_to_smt_deadline(Some(Duration::from_secs(30)))
            .unwrap()
            .unwrap();
        assert!(clamped <= Duration::from_millis(100));
        let unbounded_clamped = clamp_timeout_to_smt_deadline(None).unwrap().unwrap();
        assert!(unbounded_clamped <= Duration::from_millis(100));
    }
}
