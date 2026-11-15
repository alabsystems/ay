// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Live, shared solve-deadline cell (#quantifier-determinism).
//!
//! Command entry plans one deadline for solving, certification and
//! publication, including an explicitly opted-in quantified allowance.
//! Search lanes can temporarily narrow the search cell alone. Stop closures
//! capture a cheap [`SolveDeadlineCell`] handle (`Clone` shares the same cell)
//! and read it live, so every local slice and restoration is visible even to
//! closures constructed before command entry.
//!
//! VERDICT SAFETY: the cell only changes WHEN a solve observes its deadline,
//! never a verdict — every deadline break in the pipeline routes to
//! fail-closed `Unknown(Timeout/QuantifierRoundLimit/...)`, and later stops
//! (extension visible) can only allow deterministic work to converge to a
//! genuine Sat/Unsat; earlier stops (tightening visible) can only degrade to
//! Unknown.
//!
//! The cell is ay-core's [`LiveDeadline`] (GuardTree step S2): one atomic
//! load or store, no lock, every instant read back exactly as it was set.
//! The executor's Check node reads its deadline from the same cell, so a
//! theory loop that polls `ay_core::resource::check_stop_requested` sees
//! every move the executor makes, as its stop closures do.
//!
//! A deadline share (GuardTree GT6, step S3) is a child node with a cell of
//! its own, and a slicer never writes the executor's deadline. While a share
//! is open on a cell ([`SolveDeadlineCell::open_share`]), the executor's
//! deadline IS the share's: every read returns it and every write moves it,
//! as when the slicer overwrote the cell, and when the share closes the
//! executor's own deadline, which nothing wrote, is back. A Check node opened
//! while a share is open (a fallback-chain attempt's check-sat) reads that
//! share's cell, which its call's writes move.
//!
//! A poll that runs at every callback of a hot walk reads the cell through
//! [`DeadlinePoll`] instead (`alarm.rs`): one atomic load of the cell's
//! generation and one of a flag a timer raises, not a clock read.

use ay_core::resource::LiveDeadline;
use ay_core::time::Instant;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

mod alarm;
pub(crate) use alarm::{DeadlineAlarm, DeadlinePoll};

mod command;
pub(crate) use command::{
    CommandDeadlineScope, CommandDeadlineState, DecisionDeadlinePlan, SolveCallDeadlineScope,
};

/// Shared live view of the executor's solve deadline.
///
/// `Clone` yields a HANDLE to the same cell (deliberate: closures and
/// watchdog threads capture clones and observe live updates). To snapshot a
/// value (e.g. save/restore around a sub-solve window), use [`Self::get`].
#[derive(Debug, Clone, Default)]
pub(crate) struct SolveDeadlineCell {
    cell: Arc<View>,
}

#[derive(Debug, Default)]
struct View {
    /// The executor's own deadline: the Check node's when no share is open
    /// around the check. A slicer never writes it (GT6).
    own: LiveDeadline,
    /// The cells of the deadline shares open on this view, innermost last.
    shares: Mutex<Vec<LiveDeadline>>,
    /// How many shares are open, read without the lock.
    open: AtomicUsize,
    /// Bumped by every write, and by every share opened or closed.
    generation: AtomicU64,
}

impl View {
    fn shares(&self) -> MutexGuard<'_, Vec<LiveDeadline>> {
        self.shares.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn moved(&self) {
        self.generation.fetch_add(1, Ordering::Release);
    }
}

impl SolveDeadlineCell {
    /// A fresh cell with no deadline installed.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Read the current deadline (value snapshot at THIS instant): the
    /// innermost open share's, else the executor's own.
    pub(crate) fn get(&self) -> Option<Instant> {
        #[cfg(test)]
        watched(&self.cell);
        if self.cell.open.load(Ordering::Acquire) == 0 {
            return self.cell.own.get();
        }
        self.current().get()
    }

    /// Install/replace/clear the deadline: the innermost open share's, else
    /// the executor's own. Visible immediately to every handle cloned from
    /// this cell, and to every node built on the cell it writes.
    pub(crate) fn set(&self, deadline: Option<Instant>) {
        if self.cell.open.load(Ordering::Acquire) == 0 {
            self.cell.own.set(deadline);
        } else {
            let shares = self.cell.shares();
            shares.last().unwrap_or(&self.cell.own).set(deadline);
        }
        self.cell.moved();
        #[cfg(test)]
        watched(&self.cell);
    }

    /// How many times the deadline has moved: bumped after every write, and
    /// whenever a share opens or closes, so a [`DeadlinePoll`] armed at one
    /// generation that reads a later one re-reads the cell.
    pub(crate) fn generation(&self) -> u64 {
        self.cell.generation.load(Ordering::Acquire)
    }

    /// Whether the deadline moved since [`Self::generation`] read
    /// `generation`, by a relaxed load: the per-offer check of a hot poll,
    /// which reads the cell itself once it sees a move.
    #[inline]
    pub(crate) fn moved_since(&self, generation: u64) -> bool {
        self.cell.generation.load(Ordering::Relaxed) != generation
    }

    /// The executor's own deadline cell. An open share does not move it.
    #[cfg(test)]
    pub(crate) fn live(&self) -> &LiveDeadline {
        &self.cell.own
    }

    /// The cell [`Self::get`] reads now, and every write moves: the innermost
    /// open share's, else the executor's own. A node built on it
    /// (`DeadlineSource::Live`) reads that cell for its life.
    pub(crate) fn current(&self) -> LiveDeadline {
        self.cell.shares().last().unwrap_or(&self.cell.own).clone()
    }

    /// Make `share`, a deadline share's own cell, this view's deadline until
    /// the returned scope drops (GT6, step S3).
    pub(crate) fn open_share(&self, share: LiveDeadline) -> OpenShare {
        let mut shares = self.cell.shares();
        shares.push(share.clone());
        self.cell.open.store(shares.len(), Ordering::Release);
        drop(shares);
        self.cell.moved();
        OpenShare {
            view: self.clone(),
            share,
        }
    }

    /// Live poll: is a deadline installed AND already passed, or has the
    /// polling thread reached the work ceiling installed on it
    /// (`ay_core::resource::enter_work_ceiling`)? Both end the work the same
    /// way: a fail-closed `Unknown`.
    pub(crate) fn expired(&self) -> bool {
        ay_core::resource::work_ceiling_reached()
            || self.get().is_some_and(|dl| Instant::now() >= dl)
    }
}

#[cfg(test)]
thread_local! {
    /// [`watch_for_testing`]'s observer on this thread.
    static WATCH: std::cell::RefCell<Option<Box<dyn FnMut(usize, &LiveDeadline)>>> =
        const { std::cell::RefCell::new(None) };
}

/// Hand the observer the number of shares open on `view` and the executor's
/// own cell (skipped when the observer itself reads a deadline).
#[cfg(test)]
fn watched(view: &View) {
    WATCH.with(|watch| {
        if let Ok(mut watch) = watch.try_borrow_mut() {
            if let Some(observer) = watch.as_mut() {
                observer(view.open.load(Ordering::Acquire), &view.own);
            }
        }
    });
}

/// Test hook: run `body` with `observer` called at every read of a deadline
/// view on this thread and after every write, with the number of shares open
/// on it and the executor's own cell.
#[cfg(test)]
pub(crate) fn watch_for_testing<R>(
    observer: impl FnMut(usize, &LiveDeadline) + 'static,
    body: impl FnOnce() -> R,
) -> R {
    WATCH.with(|watch| *watch.borrow_mut() = Some(Box::new(observer)));
    let result = body();
    WATCH.with(|watch| *watch.borrow_mut() = None);
    result
}

/// A deadline share's cell made a view's deadline
/// ([`SolveDeadlineCell::open_share`]); dropping it closes it there. It
/// removes ITS OWN entry, so a scope dropped out of order neither restores a
/// closed share nor hides an open one.
#[must_use = "the share is closed when this scope drops"]
pub(crate) struct OpenShare {
    view: SolveDeadlineCell,
    share: LiveDeadline,
}

impl Drop for OpenShare {
    fn drop(&mut self) {
        let view = &self.view.cell;
        let mut shares = view.shares();
        if let Some(at) = shares.iter().rposition(|cell| cell.is_same(&self.share)) {
            shares.remove(at);
        }
        view.open.store(shares.len(), Ordering::Release);
        drop(shares);
        view.moved();
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
        let past = Instant::now()
            .checked_sub(Duration::from_millis(1))
            .expect("1 millisecond must fit before the current test instant");
        cell.set(Some(past));
        assert_eq!(handle.get(), Some(past));
        assert!(handle.expired());
        let future = Instant::now() + Duration::from_mins(1);
        cell.set(Some(future));
        assert!(!handle.expired());
        cell.set(None);
        assert_eq!(handle.get(), None);
        assert!(!handle.expired());
    }
}
