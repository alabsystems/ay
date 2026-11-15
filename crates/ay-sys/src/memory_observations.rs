// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Diagnostic observations of [`crate::current_footprint_bytes`] attempts.
//!
//! Totals are monotone and local to the calling thread. Snapshot differences
//! include synchronous nested work on that thread, never another thread's
//! observations. They neither reset nor drain the totals. Attempts include
//! failed probes and the zero returned on unsupported platforms; they do not
//! promise that an operating-system call occurred. Elapsed time is zero on
//! platforms without a live footprint probe. Attempts and cumulative
//! nanoseconds saturate at [`u64::MAX`].
//!
//! These observations carry no resource allowance or proof authority and are
//! never consulted by memory limits or solver verdicts. Timing adds diagnostic
//! overhead; elapsed time includes any descheduling during an attempt. Nested
//! attempt durations overlap and must not be added as exclusive wall time.

use std::cell::Cell;
use std::marker::PhantomData;
use std::rc::Rc;
use std::time::Duration;
#[cfg(any(target_os = "macos", target_os = "linux"))]
use std::time::Instant;

#[derive(Clone, Copy, Debug, Default)]
struct Totals {
    attempts: u64,
    elapsed_nanos: u64,
}

thread_local! {
    static TOTALS: Cell<Totals> = const {
        Cell::new(Totals { attempts: 0, elapsed_nanos: 0 })
    };
}

/// One calling thread's cumulative footprint observations.
///
/// A snapshot cannot move to, or be shared with, another thread. Capture both
/// endpoints on the thread being measured; the resulting [`Delta`] is ordinary
/// diagnostic data that can be sent elsewhere.
#[derive(Clone, Debug)]
#[must_use]
pub struct Snapshot {
    totals: Totals,
    _thread_bound: PhantomData<Rc<()>>,
}

/// Diagnostic difference between two snapshots from the same thread.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[must_use]
pub struct Delta {
    /// Footprint attempts completed or unwound between the snapshots.
    pub attempts: u64,
    /// Time inside those attempts, including synchronous nested work.
    pub elapsed: Duration,
}

impl Snapshot {
    /// Capture the calling thread's totals without resetting them.
    pub fn capture() -> Self {
        Self {
            totals: TOTALS.try_with(Cell::get).unwrap_or_default(),
            _thread_bound: PhantomData,
        }
    }

    /// Compute an independent, saturating difference without changing either
    /// snapshot or the thread's totals. A reversed interval produces zero.
    pub fn since(&self, earlier: &Self) -> Delta {
        Delta {
            attempts: self.totals.attempts.saturating_sub(earlier.totals.attempts),
            elapsed: Duration::from_nanos(
                self.totals
                    .elapsed_nanos
                    .saturating_sub(earlier.totals.elapsed_nanos),
            ),
        }
    }
}

/// Observe the existing probe once, without retaining a TLS borrow across it.
pub(crate) fn observe<T>(probe: impl FnOnce() -> T) -> T {
    let _observation = Observation {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        started: Instant::now(),
    };
    probe()
}

struct Observation {
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    started: Instant,
}

impl Drop for Observation {
    fn drop(&mut self) {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        let elapsed_nanos = u64::try_from(self.started.elapsed().as_nanos()).unwrap_or(u64::MAX);
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        let elapsed_nanos = 0;
        let _ = TOTALS.try_with(|totals| {
            let previous = totals.get();
            totals.set(Totals {
                attempts: previous.attempts.saturating_add(1),
                elapsed_nanos: previous.elapsed_nanos.saturating_add(elapsed_nanos),
            });
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_probe_is_counted_without_changing_its_result() {
        let before = Snapshot::capture();
        let mut calls = 0;
        let value = observe(|| {
            calls += 1;
            0_usize
        });
        let after = Snapshot::capture();
        assert_eq!(value, 0);
        assert_eq!(calls, 1);
        assert_eq!(after.since(&before).attempts, 1);
    }

    #[test]
    fn unwinding_probe_is_counted() {
        let before = Snapshot::capture();
        let result = std::panic::catch_unwind(|| observe(|| panic!("probe failed")));
        assert!(result.is_err());
        assert_eq!(Snapshot::capture().since(&before).attempts, 1);
    }
}
