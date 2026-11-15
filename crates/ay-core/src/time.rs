// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Monotonic-clock shim (re-export of [`ay_sys::time`]).
//!
//! On native targets `Instant` is exactly `std::time::Instant`, so host codegen
//! is byte-identical. On `wasm32-unknown-unknown` it is `ay-sys`'s host-clock
//! shim. The implementation lives in `ay-sys` because it needs an `unsafe` FFI
//! call and `ay-core` is `#![forbid(unsafe_code)]`; this module simply re-exports
//! it so the rest of the workspace can write `ay_core::time::Instant`.

pub use ay_sys::time::Instant;

use std::cell::Cell;

/// When a poll that runs at every step of a hot loop reads the clock: at its
/// first poll, then once per `stride` polls (DR-34 in the development design notes).
///
/// `Instant::now` is a `clock_gettime` (`mach_absolute_time` on macOS), tens
/// of nanoseconds, and the strict checker's producer polls its deadlines at
/// every literal, hint and resolution step: read at each poll, the clock took
/// a quarter of a long proof replay (sampled 2026-10-09). A poll that reads
/// it once per `stride` sees a passed deadline within `stride` steps.
#[derive(Debug)]
pub struct ClockStride {
    stride: u32,
    polls: Cell<u32>,
}

impl ClockStride {
    /// Read the clock on the first poll and every `stride`-th after it (a
    /// `stride` of 0 or 1 reads it at every poll).
    #[must_use]
    pub const fn new(stride: u32) -> Self {
        Self {
            stride,
            polls: Cell::new(0),
        }
    }

    /// Whether this poll reads the clock.
    pub fn due(&self) -> bool {
        let polls = self.polls.get();
        let next = polls.saturating_add(1);
        self.polls.set(if next >= self.stride { 0 } else { next });
        polls == 0
    }
}

#[cfg(test)]
mod tests {
    use super::ClockStride;

    #[test]
    fn the_clock_is_read_at_the_first_poll_and_once_per_stride() {
        let stride = ClockStride::new(4);
        let due: Vec<bool> = (0..9).map(|_| stride.due()).collect();
        assert_eq!(
            due,
            [true, false, false, false, true, false, false, false, true]
        );
        let every = ClockStride::new(1);
        assert!((0..3).all(|_| every.due()));
        let zero = ClockStride::new(0);
        assert!((0..3).all(|_| zero.due()));
    }
}
