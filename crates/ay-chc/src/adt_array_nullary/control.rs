// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One original owner for naming, search and ground-evidence construction.

use ay_core::resource::{CheckStop, CheckStopScope, Guard};
use ay_core::time::Instant;
use std::cell::RefCell;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

use crate::smt::deadline::{effective_thread_deadline, try_lane_cancellation};
use crate::smt::replay_control::ScopedReplayControl;
use crate::CancellationToken;

thread_local! {
    static POLLING: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
}

pub(super) struct Control {
    state: Arc<State>,
}

struct State {
    original: Option<CheckStop>,
    guard: Option<Guard>,
    lane: Option<CancellationToken>,
    interrupt: Option<Arc<AtomicBool>>,
    deadline: Instant,
    memory: crate::bmc::memory::Budget,
    stopped: AtomicBool,
    work: AtomicUsize,
    storage: AtomicUsize,
}

impl Control {
    pub(super) fn capture(budget: Duration) -> Option<Self> {
        let original = ay_core::resource::current_check_stop().ok()?;
        let guard = ay_core::resource::current_guard();
        let (lane, interrupt) = try_lane_cancellation().ok()?;
        let requested = Instant::now().checked_add(budget)?;
        let deadline = [
            Some(requested),
            effective_thread_deadline(),
            guard.as_ref().and_then(Guard::effective_deadline),
        ]
        .into_iter()
        .flatten()
        .min()?;
        let out = Self {
            state: Arc::new(State {
                original,
                guard,
                lane,
                interrupt,
                deadline,
                memory: crate::bmc::memory::Budget::capture(None, None),
                stopped: AtomicBool::new(false),
                work: AtomicUsize::new(0),
                storage: AtomicUsize::new(0),
            }),
        };
        out.poll()?;
        Some(out)
    }

    /// Install after the owner; restore callback/deadline TLS before dropping it.
    pub(super) fn enter(&self) -> (ScopedReplayControl, CheckStopScope) {
        let replay =
            ScopedReplayControl::install_until(self.state.deadline, self.state.lane.as_ref());
        let state = Arc::clone(&self.state);
        let callback = ay_core::resource::enter_check_stop(Arc::new(move || !state.poll()));
        (replay, callback)
    }

    pub(super) fn poll(&self) -> Option<()> {
        self.state.poll().then_some(())
    }

    pub(super) fn remaining(&self) -> Option<Duration> {
        self.poll()?;
        Some(
            self.state
                .deadline
                .saturating_duration_since(Instant::now()),
        )
    }

    pub(super) fn refuse<T>(&self) -> Option<T> {
        self.state.stopped.store(true, Ordering::Release);
        None
    }

    /// Cumulative logical construction bounds, not a fresh solver work grant.
    /// Original Guard clones debit the caller's node; storage is conservatively
    /// retained through this small optional route, including rejected candidates.
    pub(super) fn admit(&self, work: usize, bytes: usize) -> Option<()> {
        self.poll()?;
        let charged = self
            .state
            .work
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |old| {
                old.checked_add(work)
                    .filter(|total| *total <= crate::expr::MAX_PREPROCESSING_NODES)
            });
        let stored = self
            .state
            .storage
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |old| {
                old.checked_add(bytes).filter(|total| {
                    self.state
                        .memory
                        .term_limit()
                        .is_none_or(|limit| *total <= limit)
                })
            });
        if charged.is_err() || stored.is_err() {
            return self.refuse();
        }
        let Some(cost) = u64::try_from(work).ok() else {
            return self.refuse();
        };
        if self
            .state
            .guard
            .as_ref()
            .is_some_and(|guard| guard.tick(cost).is_err())
        {
            return self.refuse();
        }
        self.poll()
    }
}

impl State {
    fn outer_open(&self) -> bool {
        !self.stopped.load(Ordering::Acquire)
            && Instant::now() < self.deadline
            && self
                .guard
                .as_ref()
                .is_none_or(|guard| guard.poll().is_none())
            && !self
                .lane
                .as_ref()
                .is_some_and(CancellationToken::is_cancelled)
            && !self
                .interrupt
                .as_ref()
                .is_some_and(|flag| flag.load(Ordering::Acquire))
            && !ay_core::resource::process_cancelled()
            && self.memory.open()
    }

    fn poll(&self) -> bool {
        if !self.outer_open() {
            self.stopped.store(true, Ordering::Release);
            return false;
        }
        let identity = std::ptr::from_ref(self) as usize;
        let entered = POLLING
            .try_with(|active| {
                let Ok(mut active) = active.try_borrow_mut() else {
                    return false;
                };
                if active.contains(&identity) || active.try_reserve(1).is_err() {
                    return false;
                }
                active.push(identity);
                true
            })
            .unwrap_or(false);
        if !entered {
            self.stopped.store(true, Ordering::Release);
            return false;
        }
        let mut invocation = Invocation {
            state: self,
            identity,
            completed: false,
        };
        let requested = self.original.as_ref().is_some_and(|stop| stop());
        let open = !requested && self.outer_open();
        if !open {
            self.stopped.store(true, Ordering::Release);
        }
        invocation.completed = true;
        open
    }
}

struct Invocation<'a> {
    state: &'a State,
    identity: usize,
    completed: bool,
}

impl Drop for Invocation<'_> {
    fn drop(&mut self) {
        if !self.completed {
            self.state.stopped.store(true, Ordering::Release);
        }
        let restored = POLLING
            .try_with(|active| {
                let Ok(mut active) = active.try_borrow_mut() else {
                    return false;
                };
                if active.last() != Some(&self.identity) {
                    return false;
                }
                active.pop();
                true
            })
            .unwrap_or(false);
        if !restored {
            self.state.stopped.store(true, Ordering::Release);
        }
    }
}

#[cfg(test)]
mod tests;
