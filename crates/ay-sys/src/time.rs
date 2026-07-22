// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Monotonic-clock shim.
//!
//! On every native target this is a zero-cost re-export of
//! [`std::time::Instant`], so host codegen is byte-identical to using the std
//! type directly. On `wasm32-unknown-unknown` — where
//! `std::time::Instant::now()` panics (`time not implemented on this
//! platform`) — `Instant` is backed by an imported host clock
//! (`ay_wasm_now_ms`, wired to JavaScript's `performance.now()`) and
//! implements exactly the subset of the `std::time::Instant` API that the
//! workspace actually uses.
//!
//! It lives in `ay-sys` because it needs an `unsafe` FFI call to reach the host
//! clock, and `ay-sys` is the one workspace crate that permits `unsafe`. Other
//! crates reach it through the `ay_core::time` re-export.
//!
//! Durations always use [`std::time::Duration`], which is target-independent.

#[cfg(not(target_arch = "wasm32"))]
pub use std::time::Instant;

#[cfg(target_arch = "wasm32")]
pub use wasm_clock::Instant;

#[cfg(target_arch = "wasm32")]
mod wasm_clock {
    use std::ops::{Add, AddAssign, Sub, SubAssign};
    use std::time::Duration;

    // Host-provided monotonic clock, in fractional milliseconds (matches
    // JavaScript `performance.now()`). Imported from the `env` module so the
    // JS embedder supplies `{ env: { ay_wasm_now_ms } }`.
    #[link(wasm_import_module = "env")]
    extern "C" {
        fn ay_wasm_now_ms() -> f64;
    }

    /// A measurement of a monotonically non-decreasing clock, stored as
    /// nanoseconds since an arbitrary host epoch.
    ///
    /// API-compatible (for the subset the tree uses) with
    /// [`std::time::Instant`].
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
    pub struct Instant(u64);

    impl Instant {
        /// Returns the current instant, reading the host clock.
        #[inline]
        #[must_use]
        pub fn now() -> Self {
            // SAFETY: `ay_wasm_now_ms` is a pure host import that returns a
            // finite, monotonically non-decreasing millisecond count.
            let ms = unsafe { ay_wasm_now_ms() };
            let nanos = if ms.is_finite() && ms > 0.0 {
                (ms * 1_000_000.0) as u64
            } else {
                0
            };
            Instant(nanos)
        }

        /// Time elapsed since this instant was created.
        #[inline]
        #[must_use]
        pub fn elapsed(&self) -> Duration {
            Self::now().saturating_duration_since(*self)
        }

        /// Duration from `earlier` to `self`; saturates at zero if `earlier`
        /// is later than `self` (std panics — saturating is a strictly safer
        /// superset for our monotonic-deadline use).
        #[inline]
        #[must_use]
        pub fn duration_since(&self, earlier: Instant) -> Duration {
            Duration::from_nanos(self.0.saturating_sub(earlier.0))
        }

        /// Duration from `earlier` to `self`, saturating at zero.
        #[inline]
        #[must_use]
        pub fn saturating_duration_since(&self, earlier: Instant) -> Duration {
            Duration::from_nanos(self.0.saturating_sub(earlier.0))
        }

        /// Duration from `earlier` to `self`, or `None` if `earlier` is later.
        #[inline]
        #[must_use]
        pub fn checked_duration_since(&self, earlier: Instant) -> Option<Duration> {
            self.0.checked_sub(earlier.0).map(Duration::from_nanos)
        }

        /// `self + duration`, or `None` on overflow.
        #[inline]
        #[must_use]
        pub fn checked_add(&self, duration: Duration) -> Option<Instant> {
            let nanos = u64::try_from(duration.as_nanos()).ok()?;
            self.0.checked_add(nanos).map(Instant)
        }

        /// `self - duration`, or `None` on overflow.
        #[inline]
        #[must_use]
        pub fn checked_sub(&self, duration: Duration) -> Option<Instant> {
            let nanos = u64::try_from(duration.as_nanos()).ok()?;
            self.0.checked_sub(nanos).map(Instant)
        }
    }

    impl Add<Duration> for Instant {
        type Output = Instant;
        #[inline]
        fn add(self, rhs: Duration) -> Instant {
            self.checked_add(rhs)
                .expect("overflow when adding duration to instant")
        }
    }

    impl AddAssign<Duration> for Instant {
        #[inline]
        fn add_assign(&mut self, rhs: Duration) {
            *self = *self + rhs;
        }
    }

    impl Sub<Duration> for Instant {
        type Output = Instant;
        #[inline]
        fn sub(self, rhs: Duration) -> Instant {
            self.checked_sub(rhs)
                .expect("overflow when subtracting duration from instant")
        }
    }

    impl SubAssign<Duration> for Instant {
        #[inline]
        fn sub_assign(&mut self, rhs: Duration) {
            *self = *self - rhs;
        }
    }

    impl Sub<Instant> for Instant {
        type Output = Duration;
        #[inline]
        fn sub(self, rhs: Instant) -> Duration {
            self.saturating_duration_since(rhs)
        }
    }
}
