// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The dovetail's scheduling clock: CPU spent by the searching thread.
//!
//! The dovetail hands each candidate a slice that doubles on an inconclusive
//! probe and is capped by a fair share of what remains. Metered on the wall,
//! a slice is also spent while the scheduler runs other threads, so under CPU
//! contention every probe does less work per slice, candidates need more
//! doublings, and the fair shares shrink as the deadline nears. The derivation
//! that an idle machine refutes in the first half of the envelope then never
//! receives a slice long enough, and the same source flipped between Unsafe
//! and Unknown with the machine's load (measured: the filled-Vec depth-11
//! counterexample, found after 59 probes at load 40, was lost at load 60).
//!
//! Metered on this clock, every scheduling decision — slice sizes, retirement,
//! discovery quotas — is the idle machine's, only stretched in wall time. The
//! caller's wall deadline stays the backstop: contention can exhaust the
//! envelope, and then the search fails closed, but it no longer changes which
//! probes are run with which slices.
//!
//! This absorbs contention, not core speed. A core that needs more CPU for the
//! same probe buys less work with every slice, so on a slower core the schedule
//! is reshaped as it was on the wall under contention, and only the envelope
//! decides whether a costly derivation is reached
//! (`tests::a_slower_core_is_absorbed_only_by_an_envelope_sized_for_the_work`).

use std::time::Duration;

use ay_core::time::Instant;
use ay_sys::thread_clock::ThreadCpuClock;

use super::super::replay::Budget;

/// A source of monotone CPU readings for one thread.
pub(super) trait CpuSource {
    fn cpu(&self) -> Option<Duration>;
}

impl CpuSource for ThreadCpuClock {
    fn cpu(&self) -> Option<Duration> {
        self.elapsed()
    }
}

/// CPU time mapped onto the wall timeline at `origin`: the scheduling instant
/// is `origin` advanced by the CPU the thread has spent since.
pub(super) struct WorkClock<S> {
    origin: Instant,
    start: Duration,
    source: S,
}

impl<S: CpuSource> WorkClock<S> {
    pub(super) fn with_source(origin: Instant, source: S) -> Option<Self> {
        let start = source.cpu()?;
        Some(Self {
            origin,
            start,
            source,
        })
    }

    /// An unreadable clock falls back to the wall, which never runs slower.
    pub(super) fn now(&self) -> Instant {
        self.source
            .cpu()
            .and_then(|cpu| self.origin.checked_add(cpu.saturating_sub(self.start)))
            .unwrap_or_else(Instant::now)
    }

    /// The CPU reading at which a slice ending at scheduling instant `child`
    /// is spent.
    pub(super) fn work_until(&self, child: Instant) -> Option<Duration> {
        self.start
            .checked_add(child.saturating_duration_since(self.origin))
    }
}

/// The production clock of one search, or the wall where the platform has no
/// per-thread CPU accounting (the previous behaviour, unchanged).
pub(super) enum SearchClock {
    Work(WorkClock<ThreadCpuClock>),
    Wall,
}

impl SearchClock {
    /// Capture the calling thread, which must be the one that discovers and
    /// probes: the probes run on it, and the watchdog reads its clock.
    pub(super) fn start() -> Self {
        ThreadCpuClock::current()
            .and_then(|clock| WorkClock::with_source(Instant::now(), clock))
            .map_or(Self::Wall, Self::Work)
    }

    pub(super) fn now(&self) -> Instant {
        match self {
            Self::Work(clock) => clock.now(),
            Self::Wall => Instant::now(),
        }
    }

    /// The probe budget for a slice ending at scheduling instant `child`;
    /// `backstop` is the search's own wall deadline.
    pub(super) fn budget(&self, child: Instant, backstop: Instant) -> Budget {
        match self {
            Self::Work(clock) => clock
                .work_until(child)
                .map_or(Budget::wall(child), |until| {
                    Budget::work(backstop, clock.source, until)
                }),
            Self::Wall => Budget::wall(child),
        }
    }
}

#[cfg(test)]
mod tests;
