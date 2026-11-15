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

use crate::cancellation::CancellationToken;
use ay_core::time::Instant;
use std::cell::{Cell, RefCell};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::Duration;

thread_local! {
    static THREAD_SMT_DEADLINE: Cell<Option<Instant>> = const { Cell::new(None) };
    /// The cancellation of the portfolio lane that owns this thread, if any
    /// (see [`ScopedLaneCancellation`]).
    static THREAD_LANE_CANCELLATION: RefCell<Option<LaneCancellation>> =
        const { RefCell::new(None) };
}

struct LaneCancellation {
    token: CancellationToken,
    interrupt: Option<Arc<AtomicBool>>,
}

/// RAII guard binding a portfolio lane's cancellation to the current thread.
///
/// Engines poll their own token only at loop heads, and the SMT layer never
/// saw it: after a portfolio winner cancelled the losers, every SMT check a
/// loser issued still ran to its own per-check timeout (PDKind's reachability
/// interpolation, sanity BMC, `check_sat_10s` validations), so a loser kept a
/// validated verdict waiting for tens of seconds. With this guard installed, a
/// cancelled lane is an EXPIRED deadline for every check on the thread:
/// [`smt_deadline_remaining`] reports zero, so new checks answer `Unknown`
/// without starting, the internal DPLL(T) loop stops at its next iteration or
/// SAT interrupt poll, and the executor lane receives `interrupt` (a flag the
/// portfolio sets when it cancels its workers) as its interrupt handle.
///
/// SOUNDNESS: only ever turns a check into `Unknown` earlier, on a lane whose
/// result the portfolio no longer accepts.
pub(crate) struct ScopedLaneCancellation {
    prev: Option<LaneCancellation>,
}

impl ScopedLaneCancellation {
    /// Bind `token` (and optionally the portfolio-owned `interrupt` flag that
    /// is set whenever the lane's workers are cancelled) to this thread.
    /// Restores the previous binding on drop.
    pub(crate) fn install(token: CancellationToken, interrupt: Option<Arc<AtomicBool>>) -> Self {
        let prev = THREAD_LANE_CANCELLATION
            .with(|cell| cell.replace(Some(LaneCancellation { token, interrupt })));
        Self { prev }
    }
}

impl Drop for ScopedLaneCancellation {
    fn drop(&mut self) {
        let prev = self.prev.take();
        // `try_with`: never panic in a destructor, even during thread teardown.
        let _ = THREAD_LANE_CANCELLATION.try_with(|cell| {
            cell.replace(prev);
        });
    }
}

/// True when the portfolio lane owning this thread has been cancelled.
pub(crate) fn lane_cancelled() -> bool {
    THREAD_LANE_CANCELLATION
        .try_with(|cell| {
            cell.try_borrow()
                .ok()
                .and_then(|lane| lane.as_ref().map(|lane| lane.token.is_cancelled()))
                .unwrap_or(false)
        })
        .unwrap_or(false)
}

/// The cancellation token of the lane owning this thread, if any. A route that
/// builds a token for work it hands to another thread links this one, so the
/// work stops when the lane does (`AdaptivePortfolio::lane_token`).
pub(crate) fn current_lane_token() -> Option<CancellationToken> {
    THREAD_LANE_CANCELLATION
        .try_with(|cell| {
            cell.try_borrow()
                .ok()
                .and_then(|lane| lane.as_ref().map(|lane| lane.token.clone()))
        })
        .ok()
        .flatten()
}

/// The portfolio-owned interrupt flag of the lane owning this thread, for
/// solvers that take an interrupt handle (`ay_dpll::Executor::set_interrupt`).
/// Readers must never store to it.
pub(crate) fn lane_interrupt_flag() -> Option<Arc<AtomicBool>> {
    THREAD_LANE_CANCELLATION
        .try_with(|cell| {
            cell.try_borrow()
                .ok()
                .and_then(|lane| lane.as_ref().and_then(|lane| lane.interrupt.clone()))
        })
        .ok()
        .flatten()
}

/// Strict capture for cross-thread original owners; failure is not absence.
/// Existing lane getters retain their historical behavior.
pub(crate) fn try_lane_cancellation(
) -> Result<(Option<CancellationToken>, Option<Arc<AtomicBool>>), ()> {
    THREAD_LANE_CANCELLATION
        .try_with(|cell| {
            cell.try_borrow()
                .map(|lane| {
                    (
                        lane.as_ref().map(|lane| lane.token.clone()),
                        lane.as_ref().and_then(|lane| lane.interrupt.clone()),
                    )
                })
                .map_err(|_| ())
        })
        .map_err(|_| ())?
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
/// Ground back-translation can sit inside a narrower engine slice while its
/// authoritative caller still has acceptance budget. Its witness solve may
/// replace that inner deadline, but only with an absolute boundary already
/// clamped to the caller's remaining route budget.
///
/// # Soundness
///
/// The enclosing deadline exists to bound WALL-CLOCK, not to protect any
/// verdict. Back-translation is terminal and verdict-neutral: its output is a
/// candidate ground environment handed to
/// [`crate::ground_derivation::validate_ground_derivation`], which re-evaluates
/// every ORIGINAL clause against it and remains the sole acceptance anchor.
/// The previous deadline is restored on drop. The supplied replacement must
/// never exceed the authoritative caller deadline, and the landing checks
/// deadline/cancellation again before publishing its validated candidate.
///
/// Use ONLY for that purpose, and always with a hard cap.
pub(crate) struct ScopedSmtDeadlineOverride {
    prev: Option<Instant>,
}

impl ScopedSmtDeadlineOverride {
    /// Replace the thread deadline with the exact absolute boundary, ignoring
    /// (but restoring) any enclosing deadline. Callers must derive `deadline`
    /// from their own already-bounded route so this override never widens the
    /// authoritative solve window.
    pub(crate) fn install_until(deadline: Instant) -> Self {
        let prev = THREAD_SMT_DEADLINE.with(Cell::get);
        THREAD_SMT_DEADLINE.with(|cell| cell.set(Some(deadline)));
        Self { prev }
    }
}

impl Drop for ScopedSmtDeadlineOverride {
    fn drop(&mut self) {
        let prev = self.prev;
        THREAD_SMT_DEADLINE.with(|cell| cell.set(prev));
    }
}

/// The deadline every `check_sat` on this thread honours: the earlier of the
/// scoped SMT deadline and the thread-wide solve deadline
/// (`ScopedSolveDeadline`, installed per engine by the portfolio scheduler and
/// per proof run by the CLI).
///
/// Rung 0 (CHC-COMP 2026): the executor adapter already refused to start once
/// the solve deadline had passed, while the internal DPLL(T) loop clamped only
/// to the SMT deadline — so after an engine's budget expired the executor lane
/// was dead (676 of 2,257 executor-first attempts on metros_4 refused at
/// entry) and the internal lane kept answering, letting the engine spin between
/// cancellation polls. Folding the solve deadline in here makes the refusal
/// gate, the internal clamp and `is_cancelled` agree with the adapter.
pub(crate) fn effective_thread_deadline() -> Option<Instant> {
    [
        THREAD_SMT_DEADLINE.with(Cell::get),
        super::context::current_thread_solve_deadline(),
    ]
    .into_iter()
    .flatten()
    .min()
}

/// Remaining time before the thread's effective deadline; `None` if unbounded.
/// A cancelled portfolio lane ([`ScopedLaneCancellation`]) has none left.
pub(crate) fn smt_deadline_remaining() -> Option<Duration> {
    if lane_cancelled() {
        return Some(Duration::ZERO);
    }
    effective_thread_deadline().map(|deadline| deadline.saturating_duration_since(Instant::now()))
}

/// Return the exact route-scoped SMT deadline for child solver adapters.
/// Callers must still perform a landing check before publishing a verdict.
pub(crate) fn current_smt_deadline() -> Option<Instant> {
    THREAD_SMT_DEADLINE.with(Cell::get)
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
mod capture_tests {
    use super::*;

    #[test]
    fn a_borrowed_original_lane_refuses_owner_capture() {
        let mut original = ay_core::resource::ResourceGuard::new();
        original.set_deadline(Some(
            ay_core::time::Instant::now() + std::time::Duration::from_secs(20),
        ));
        THREAD_LANE_CANCELLATION.with(|cell| {
            let _borrowed = cell.borrow_mut();
            assert!(try_lane_cancellation().is_err());
            let owner = crate::engines::ExternalInvariantValidationOwner::capture(
                &original,
                &crate::PdrConfig::production(false),
            );
            assert_eq!(
                owner.check(),
                Some(crate::engines::ExternalInvariantValidation::Inconclusive)
            );
        });
        assert!(try_lane_cancellation().is_ok());
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
            let _guard = ScopedSmtDeadline::install(Duration::from_mins(1));
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
            let _inner = ScopedSmtDeadline::install(Duration::from_mins(1));
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

    #[test]
    fn cancelled_lane_is_an_expired_deadline_and_scope_restores() {
        let group = CancellationToken::new();
        let lane = group.child();
        let interrupt = group.interrupt_flag();
        {
            let _lane = ScopedLaneCancellation::install(lane, Some(interrupt.clone()));
            assert!(!lane_cancelled());
            assert!(!smt_deadline_expired());
            assert_eq!(clamp_timeout_to_smt_deadline(None), Ok(None));
            assert!(lane_interrupt_flag().is_some_and(|flag| Arc::ptr_eq(&flag, &interrupt)));

            // The portfolio cancels the worker group: every check on the lane
            // thread now sees an expired deadline, and the executor interrupt
            // handed out earlier observes the same cancellation.
            group.cancel();
            assert!(lane_cancelled());
            assert!(smt_deadline_expired());
            assert_eq!(smt_deadline_remaining(), Some(Duration::ZERO));
            assert_eq!(
                clamp_timeout_to_smt_deadline(Some(Duration::from_secs(5))),
                Err(())
            );
            assert!(interrupt.load(std::sync::atomic::Ordering::Relaxed));
        }
        // Leaving the lane scope restores the unbounded, uncancelled thread.
        assert!(!lane_cancelled());
        assert!(lane_interrupt_flag().is_none());
        assert!(!smt_deadline_expired());
    }

    #[test]
    fn lane_cancellation_is_thread_local() {
        let group = CancellationToken::new();
        let _lane = ScopedLaneCancellation::install(group.child(), None);
        group.cancel();
        assert!(smt_deadline_expired());
        let other = std::thread::spawn(|| (lane_cancelled(), smt_deadline_expired()))
            .join()
            .expect("probe thread");
        assert_eq!(other, (false, false));
    }
}
