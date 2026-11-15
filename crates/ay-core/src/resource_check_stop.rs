// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The stop of the check running on this thread (`ay_core::resource`).
//!
//! The process-wide cancel reaches every loop but fires only when the whole
//! run ends. A check's own limit -- `(set-option :timeout ..)` on one query of
//! a script, an embedder's interrupt -- lives on the executor, out of reach of
//! a theory loop that holds no handle on it. Measured: a QF_NRA query under a
//! 1 s per-check `:timeout` ran inside the multivariate witness search until
//! the `-T:20` watchdog's hard exit at 22 s.
//!
//! The stop is the thread's current GuardTree node (GT4, step S2): the
//! executor enters a Check node around every check-sat, with its interrupt
//! and its live deadline, so a loop deep inside a theory reads that node and
//! every node above it. A nested check-sat is a child of the node it runs in
//! and so obeys it too, except below a Certify node, which sees its
//! ancestors' cancels and not their deadlines (DR-39). Until S2 a nested
//! check replaced the stop of the check around it and was chained to
//! nothing (the development design notes §1.3).
//!
//! An embedder's explicit callback is an additional boundary, independent of
//! that tree. It remains observable under a certification node too. Capturing
//! it returns the exact callback, not an implicit closure over a search node:
//! doing the latter would defeat the tree's deliberate CancelOnly inheritance.

use super::process_cancelled;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

/// A check's stop as a poll: true once the check should end.
pub type CheckStop = Arc<dyn Fn() -> bool + Send + Sync>;

/// The whole answer of a check stop that reads nothing but flags
/// ([`enter_witnessed_check_stop`]): while the process cancel and every one
/// of these flags is down, the stop answers `false` and changes nothing.
///
/// A strict walk polls its captured stop at every checker offer (911 M on
/// the 44-bit division refutation `qb44`, 2026-10-31), and the engine's own
/// stops each poll the one they captured. A poller that holds the witness
/// reads these flags at every poll, exactly the reads the stop's own poll
/// makes, and calls the stop once one is raised. A stop that reads anything
/// else (a clock, a count, a lock, a callback) has no witness
/// (DR-AY-STOPPOLL-HOT-20261031).
#[derive(Clone)]
pub struct CheckStopWitness {
    flags: Arc<[Arc<AtomicBool>]>,
}

impl CheckStopWitness {
    /// The witness of a stop that reads exactly `flags` and the process
    /// cancel.
    #[must_use]
    pub fn new(flags: impl IntoIterator<Item = Arc<AtomicBool>>) -> Self {
        Self {
            flags: flags.into_iter().collect(),
        }
    }

    /// Whether the witnessed stop answers `false` now, changing nothing:
    /// the process cancel and every flag down, read with relaxed loads as the
    /// stop reads them.
    #[inline]
    #[must_use]
    pub fn quiet(&self) -> bool {
        !process_cancelled() && !self.flags.iter().any(|flag| flag.load(Ordering::Relaxed))
    }
}

/// An installed stop, and its witness when it has one.
struct Installed {
    stop: CheckStop,
    witness: Option<CheckStopWitness>,
}

thread_local! {
    /// The stop of the check running on this thread, installed by
    /// [`enter_check_stop`] for the extent of that check.
    static CHECK_STOP: std::cell::RefCell<Option<Installed>> =
        const { std::cell::RefCell::new(None) };
}

/// Restores the enclosing check's stop when dropped (a nested check-sat
/// installs its own for its extent).
#[must_use = "the check's stop is uninstalled when this scope is dropped"]
pub struct CheckStopScope {
    previous: Option<Installed>,
}

impl Drop for CheckStopScope {
    fn drop(&mut self) {
        let previous = self.previous.take();
        // The displaced callback can own arbitrary destructors, including a
        // nested check scope. Restore first, then release it without a TLS borrow.
        let displaced =
            CHECK_STOP.try_with(|cell| std::mem::replace(&mut *cell.borrow_mut(), previous));
        drop(displaced);
    }
}

/// Install `stop` as the stop of the check this thread runs until the
/// returned scope is dropped. This explicit boundary composes with, and cannot
/// replace or hide, the thread's current GuardTree node. The executor's own
/// interrupt and live deadline belong to that node, not to this callback.
pub fn enter_check_stop(stop: CheckStop) -> CheckStopScope {
    install(Installed {
        stop,
        witness: None,
    })
}

/// [`enter_check_stop`] for a stop whose whole answer is `witness`'s flags
/// ([`CheckStopWitness`]). Only the engine's own stops that read nothing
/// else are entered so; an embedder's callback is always opaque.
pub fn enter_witnessed_check_stop(stop: CheckStop, witness: CheckStopWitness) -> CheckStopScope {
    install(Installed {
        stop,
        witness: Some(witness),
    })
}

fn install(installed: Installed) -> CheckStopScope {
    let previous = CHECK_STOP
        .try_with(|cell| cell.borrow_mut().replace(installed))
        .ok()
        .flatten();
    CheckStopScope { previous }
}

/// Capture the exact current callback before moving work to another thread.
///
/// This only borrows the original stop authority through an Arc; it grants no
/// resources. Create and drop a new local scope on the receiving thread.
/// Transfer/enter the appropriate GuardTree node separately for work owned by it.
#[must_use]
pub fn current_check_stop() -> Result<Option<CheckStop>, CheckStopCaptureError> {
    CHECK_STOP
        .try_with(|cell| {
            cell.try_borrow()
                .map(|installed| installed.as_ref().map(|it| Arc::clone(&it.stop)))
                .map_err(|_| CheckStopCaptureError::Borrowed)
        })
        .map_err(|_| CheckStopCaptureError::Unavailable)?
}

/// [`current_check_stop`], and the captured stop's witness when it was
/// entered with one, read together.
pub fn current_check_stop_and_witness() -> (
    Result<Option<CheckStop>, CheckStopCaptureError>,
    Option<CheckStopWitness>,
) {
    let captured = CHECK_STOP
        .try_with(|cell| {
            cell.try_borrow()
                .map(|installed| {
                    installed
                        .as_ref()
                        .map(|it| (Arc::clone(&it.stop), it.witness.clone()))
                })
                .map_err(|_| CheckStopCaptureError::Borrowed)
        })
        .map_err(|_| CheckStopCaptureError::Unavailable)
        .and_then(|captured| captured);
    match captured {
        Ok(Some((stop, witness))) => (Ok(Some(stop)), witness),
        Ok(None) => (Ok(None), None),
        Err(error) => (Err(error), None),
    }
}

/// Failure to observe the caller's callback is NOT a healthy absence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum CheckStopCaptureError {
    /// Another active borrow prevents observing this thread's callback.
    #[error("the original check-stop callback is already borrowed")]
    Borrowed,
    /// The thread-local callback storage is no longer available.
    #[error("the original check-stop thread local is unavailable")]
    Unavailable,
}

/// Whether the check running on this thread should stop: the process-wide
/// cancel, or a stop of the thread's current node (its check's `:timeout`
/// and interrupt, a work ceiling or grant it runs under, an ancestor's
/// stop). Read without latching anything ([`super::Guard::poll`]), so a
/// deadline the executor moves later is read again at the next poll. The
/// same contract as [`process_cancelled`]: poll it only from a loop whose
/// early end is a sound "no answer". An explicitly installed callback is an
/// independent additional stop, including under a CancelOnly node.
#[must_use]
pub fn check_stop_requested() -> bool {
    super::with_current_guard(|guard| guard.poll().is_some()).unwrap_or_else(process_cancelled)
        || match current_check_stop() {
            // Both invocation and final Arc cleanup run outside the TLS borrow.
            // A callback may enter/restore a nested scope while being observed.
            Ok(Some(stop)) => stop(),
            Ok(None) => false,
            Err(_) => true,
        }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resource::{ChildSpec, DeadlineSource, Guard, LiveDeadline, NodeLabel};
    use crate::time::Instant;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;
    use std::time::Duration;

    #[test]
    fn a_borrowed_original_callback_is_capture_failure_not_healthy_absence() {
        CHECK_STOP.with(|cell| {
            let _borrowed = cell.borrow_mut();
            assert!(matches!(
                current_check_stop(),
                Err(CheckStopCaptureError::Borrowed)
            ));
        });
        assert!(current_check_stop().is_ok());
    }

    #[test]
    fn a_check_stop_is_seen_for_its_extent_and_nested_scopes_restore() {
        assert!(!check_stop_requested() || process_cancelled());
        let outer_flag = Arc::new(AtomicBool::new(false));
        let outer = Guard::root_child(
            ChildSpec::new(NodeLabel::Check).with_external(Arc::clone(&outer_flag)),
        );
        let outer_scope = outer.enter();
        assert!(!check_stop_requested());
        {
            let nested = outer.child(ChildSpec::new(NodeLabel::Check));
            nested.cancel();
            let _inner = nested.enter();
            assert!(check_stop_requested(), "the nested check's stop is seen");
        }
        assert!(!check_stop_requested(), "the enclosing stop is restored");
        outer_flag.store(true, Ordering::SeqCst);
        assert!(check_stop_requested(), "the stop is polled live");
        drop(outer_scope);
        assert!(!check_stop_requested(), "no stop once the check has ended");
    }

    #[test]
    fn a_moved_deadline_is_read_again_and_nothing_is_latched() {
        let cell = LiveDeadline::new(Some(Instant::now()));
        let check = Guard::root_child(
            ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Live(cell.clone())),
        );
        let _scope = check.enter();
        assert!(check_stop_requested(), "a passed deadline stops the check");
        cell.set(Some(Instant::now() + Duration::from_secs(3600)));
        assert!(
            !check_stop_requested(),
            "a restored deadline is read again: the poll latched nothing"
        );
        assert_eq!(check.stopped(), None);
    }
}

#[cfg(test)]
#[path = "resource_check_stop_composition_tests.rs"]
mod composition_tests;

#[cfg(test)]
#[path = "resource_check_stop_reentry_tests.rs"]
mod reentry_tests;

#[cfg(test)]
#[path = "resource_check_stop_witness_tests.rs"]
mod witness_tests;
