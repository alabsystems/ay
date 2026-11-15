// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A node's CPU slice (the development design notes §6): the CPU the thread
//! that entered the node spends inside it, read through that thread's
//! [`ThreadCpuClock`] from any thread.
//!
//! One thread at a time: the first entry captures its thread's clock, a
//! nested or concurrent entry while it is open adds nothing, and its exit
//! folds what it spent into the closed total. A worker node is entered once,
//! by its own thread (GT4); a worker that spawns compute threads gives each
//! one a child node (§6), so nothing a slice should count runs unmeasured.

use std::sync::{Mutex, MutexGuard, PoisonError};
use std::time::Duration;

use ay_sys::thread_clock::ThreadCpuClock;

#[derive(Debug)]
pub(super) struct CpuBudget {
    limit: Duration,
    /// The closed total and the open entry, read and moved together, so a
    /// read never misses an entry that is closing.
    state: Mutex<State>,
}

#[derive(Debug, Default)]
struct State {
    /// Nanoseconds spent by the entries that have exited; saturates at
    /// `u64::MAX` once one of them could not be measured.
    closed: u64,
    /// The open entry.
    open: Option<Mark>,
}

#[derive(Clone, Copy, Debug)]
enum Mark {
    /// The entering thread's clock and its reading at entry.
    Measured {
        clock: ThreadCpuClock,
        start: Duration,
    },
    /// The platform gave no clock for the entering thread.
    Unmeasurable,
}

impl Mark {
    /// Nanoseconds spent since entry; `None` when they cannot be read.
    fn spent_nanos(self) -> Option<u64> {
        match self {
            Self::Measured { clock, start } => clock
                .elapsed()
                .map(|now| u64::try_from(now.saturating_sub(start).as_nanos()).unwrap_or(u64::MAX)),
            Self::Unmeasurable => None,
        }
    }
}

impl CpuBudget {
    pub(super) fn new(limit: Duration) -> Self {
        Self {
            limit,
            state: Mutex::new(State::default()),
        }
    }

    fn state(&self) -> MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Start measuring the calling thread unless an entry is already open.
    /// True when this call opened it, so that its exit must close it.
    pub(super) fn enter(&self) -> bool {
        let mark = ThreadCpuClock::current()
            .and_then(|clock| clock.elapsed().map(|start| Mark::Measured { clock, start }))
            .unwrap_or(Mark::Unmeasurable);
        self.open(mark)
    }

    fn open(&self, mark: Mark) -> bool {
        let mut state = self.state();
        if state.open.is_some() {
            return false;
        }
        state.open = Some(mark);
        true
    }

    /// Close the open entry: what it spent joins the closed total.
    pub(super) fn exit(&self) {
        let mut state = self.state();
        if let Some(mark) = state.open.take() {
            let spent = mark.spent_nanos().unwrap_or(u64::MAX);
            state.closed = state.closed.saturating_add(spent);
        }
    }

    /// The CPU spent inside the node so far. A clock that cannot be read
    /// reads as unbounded, so the slice is spent (fail-closed: the stop is
    /// `unknown`, and a slice nobody can measure is not enforced by
    /// pretending it was not used).
    pub(super) fn spent(&self) -> Duration {
        let state = self.state();
        let open = state.open.map_or(Some(0), Mark::spent_nanos);
        Duration::from_nanos(open.map_or(u64::MAX, |open| state.closed.saturating_add(open)))
    }

    /// Whether the slice is spent (reaching it counts, as for an rlimit).
    pub(super) fn exceeded(&self) -> bool {
        self.spent() >= self.limit
    }

    /// Open an entry whose thread has no clock, as a platform without one
    /// would.
    #[cfg(test)]
    pub(super) fn enter_unmeasurable(&self) -> bool {
        self.open(Mark::Unmeasurable)
    }
}
