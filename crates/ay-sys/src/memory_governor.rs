// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Process memory governor: keep a parallel solve inside its memory budget by
//! shedding the lane that holds the heap, before the process is ended.
//!
//! The per-lane shares ([`crate::MemoryGroup`]) stop ONE runaway lane. They do
//! not stop several lanes growing together: on the CHC-COMP LRA-Lin memouts
//! (the development design notes at `9598c4206`) PDR x2, BMC and
//! PDKIND each expanded shared expression DAGs at the same time, each stayed
//! under half the budget, and the process went from 5 to 16 GiB in about two
//! seconds. The process-wide signals then ended every lane at once — the
//! 95 % advisory cancels the whole solve, and the harness's RSS watchdog
//! (20 ms polls, no grace) usually killed the process first, so lanes that
//! were still running cheaply lost their answers with it.
//!
//! The governor is polled every few milliseconds by the binary's memory
//! watchdog thread ([`MemoryGovernor::poll`]). Once the process's memory
//! pressure ([`crate::current_memory_pressure_bytes`]: footprint or resident
//! set, whichever an external judge would see as larger) crosses
//! [`SHED_PERCENT`] of the budget it
//! 1. returns freed heap pages to the OS ([`crate::purge_freed_heap_pages`]:
//!    the allocator keeps pages of cancelled work resident for a while), and
//! 2. if the pressure is still there, SHEDS the registered lane holding the
//!    most live heap ([`crate::shed_fattest_memory_group`]): its cancel flag is
//!    set and it reads as over its hard limit, so it stops at its next
//!    checkpoint or expression walk and frees what it built. The other lanes
//!    keep running. The next lane is shed only after the last one had
//!    [`SHED_SETTLE`] to unwind, or at once above [`URGENT_PERCENT`].
//!
//! The last running lane is never shed ([`KEEP_LANES`]); the process-wide
//! advisory remains the last resort for it. A shed lane only ever answers
//! `Unknown`, so no verdict can change.

use std::time::{Duration, Instant};

use crate::memory_group::{shed_fattest_memory_group, MemoryGroupUsage};

/// Share of the memory budget at which the governor starts shedding lanes.
pub const SHED_PERCENT: usize = 70;

/// Share above which the next lane is shed without waiting for the previous
/// shed to settle.
pub const URGENT_PERCENT: usize = 85;

/// Time a shed lane gets to unwind and free its heap before another lane is
/// shed (below [`URGENT_PERCENT`]).
pub const SHED_SETTLE: Duration = Duration::from_millis(100);

/// Minimum spacing between two heap purges under pressure.
pub const PURGE_INTERVAL: Duration = Duration::from_millis(50);

/// A lane holding less than this share of the budget is not shed: the
/// pressure is not its heap, and shedding it would lose its answer for
/// nothing.
pub const MIN_SHED_SHARE_PERCENT: usize = 5;

/// Lanes that always keep running.
pub const KEEP_LANES: usize = 1;

/// What one governor poll did.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GovernorEvent {
    /// Freed heap pages were returned to the OS.
    Purged {
        /// Pressure before the purge, in bytes.
        before: usize,
        /// Pressure after it.
        after: usize,
    },
    /// A lane was shed.
    Shed {
        /// The lane and the live heap it held.
        lane: MemoryGroupUsage,
        /// Pressure when it was shed, in bytes.
        pressure: usize,
    },
}

/// Governor state for one process budget. Polled from one thread.
#[derive(Debug)]
pub struct MemoryGovernor {
    limit: usize,
    last_shed: Option<Instant>,
    last_purge: Option<Instant>,
}

impl MemoryGovernor {
    /// A governor for a budget of `limit_bytes` (0 = none: every poll idles).
    #[must_use]
    pub fn new(limit_bytes: usize) -> Self {
        Self {
            limit: limit_bytes,
            last_shed: None,
            last_purge: None,
        }
    }

    /// One poll against the live process: read the pressure, purge and shed
    /// as the policy says. Returns what it did, in order.
    pub fn poll(&mut self) -> Vec<GovernorEvent> {
        let min_live = share_of(self.limit, MIN_SHED_SHARE_PERCENT);
        self.poll_with(
            Instant::now(),
            crate::current_memory_pressure_bytes,
            crate::purge_freed_heap_pages,
            || shed_fattest_memory_group(min_live, KEEP_LANES),
        )
    }

    /// [`MemoryGovernor::poll`] over injected signals (the policy, testable
    /// without a process under pressure).
    pub(crate) fn poll_with(
        &mut self,
        now: Instant,
        mut pressure: impl FnMut() -> usize,
        purge: impl FnOnce() -> bool,
        shed: impl FnOnce() -> Option<MemoryGroupUsage>,
    ) -> Vec<GovernorEvent> {
        let mut events = Vec::new();
        if self.limit == 0 {
            return events;
        }
        let shed_at = share_of(self.limit, SHED_PERCENT);
        let mut current = pressure();
        if current < shed_at {
            return events;
        }
        if self
            .last_purge
            .is_none_or(|last| now.saturating_duration_since(last) >= PURGE_INTERVAL)
        {
            self.last_purge = Some(now);
            if purge() {
                let before = current;
                current = pressure();
                events.push(GovernorEvent::Purged {
                    before,
                    after: current,
                });
                if current < shed_at {
                    return events;
                }
            }
        }
        let settling = self
            .last_shed
            .is_some_and(|last| now.saturating_duration_since(last) < SHED_SETTLE);
        if settling && current < share_of(self.limit, URGENT_PERCENT) {
            return events;
        }
        if let Some(lane) = shed() {
            self.last_shed = Some(now);
            events.push(GovernorEvent::Shed {
                lane,
                pressure: current,
            });
        }
        events
    }
}

/// `percent` % of `limit`, without overflow.
fn share_of(limit: usize, percent: usize) -> usize {
    limit / 100 * percent
}

#[cfg(test)]
#[path = "memory_governor_tests.rs"]
mod tests;
