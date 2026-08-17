// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

impl std::fmt::Debug for MemoryPressure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MemoryPressure")
            .field("current_band", &self.current)
            .field("thresholds", &self.thresholds)
            .field("last_rss", &self.last_rss.load(Ordering::Relaxed))
            .field("last_budget", &self.last_budget.load(Ordering::Relaxed))
            .field("sample_count", &self.sample_count.load(Ordering::Relaxed))
            .field("red_samples", &self.red_samples.load(Ordering::Relaxed))
            .finish_non_exhaustive()
    }
}

impl Default for MemoryPressure {
    fn default() -> Self {
        Self::new()
    }
}

impl MemoryPressure {
    /// Construct with the production [`SystemSource`] and default thresholds.
    #[must_use]
    pub fn new() -> Self {
        Self::with_source(Box::new(SystemSource))
    }

    /// Construct with a caller-supplied source (used by tests).
    #[must_use]
    pub fn with_source(source: Box<dyn MemorySource>) -> Self {
        Self {
            source,
            thresholds: BandThresholds::default(),
            current: Band::Green,
            last_rss: AtomicUsize::new(0),
            last_budget: AtomicUsize::new(0),
            sample_count: AtomicU64::new(0),
            red_samples: AtomicU64::new(0),
        }
    }

    /// Construct with custom thresholds (tests and advanced tuning).
    #[must_use]
    pub fn with_thresholds(source: Box<dyn MemorySource>, thresholds: BandThresholds) -> Self {
        let mut mp = Self::with_source(source);
        mp.thresholds = thresholds;
        mp
    }

    /// Read current RSS from the source. Cheap (one syscall via ay-sys).
    #[must_use]
    pub fn read_rss(&self) -> usize {
        self.source.rss_bytes()
    }

    /// Effective budget: `min(rlimit, system_available * 0.75)` in bytes.
    ///
    /// Returns `usize::MAX` when no OS figure is available.
    #[must_use]
    pub fn budget(&self) -> usize {
        self.source.budget_bytes()
    }

    /// Current band, as of the most recent [`Self::sample`] call.
    #[inline]
    #[must_use]
    pub fn current_band(&self) -> Band {
        self.current
    }

    /// Most recently sampled RSS (0 before first `sample()`).
    #[inline]
    #[must_use]
    pub fn last_rss(&self) -> usize {
        self.last_rss.load(Ordering::Relaxed)
    }

    /// Most recently sampled budget (0 before first `sample()`).
    #[inline]
    #[must_use]
    pub fn last_budget(&self) -> usize {
        self.last_budget.load(Ordering::Relaxed)
    }

    /// Number of samples since construction.
    #[inline]
    #[must_use]
    pub fn sample_count(&self) -> u64 {
        self.sample_count.load(Ordering::Relaxed)
    }

    /// Number of Red-band samples since construction.
    #[inline]
    #[must_use]
    pub fn red_samples(&self) -> u64 {
        self.red_samples.load(Ordering::Relaxed)
    }

    /// Take a fresh reading, update the cached band, and return it.
    ///
    /// Notifies `observer` on transitions; pass `&mut ()` for polling-only
    /// callers (the unit impl is a no-op).
    pub fn sample_with(&mut self, observer: &mut dyn PressureObserver) -> Band {
        let rss = self.source.rss_bytes();
        let budget = self.source.budget_bytes();
        self.last_rss.store(rss, Ordering::Relaxed);
        self.last_budget.store(budget, Ordering::Relaxed);
        self.sample_count.fetch_add(1, Ordering::Relaxed);

        let new_band = classify_raw(rss, budget, self.thresholds, self.current);
        if new_band.is_red() {
            self.red_samples.fetch_add(1, Ordering::Relaxed);
        }
        if new_band != self.current {
            let old = self.current;
            self.current = new_band;
            observer.on_band_change(old, new_band);
        }
        new_band
    }

    /// Polling variant — no observer notified. Equivalent to
    /// `self.sample_with(&mut NoopObserver)`.
    pub fn sample(&mut self) -> Band {
        self.sample_with(&mut NoopObserver)
    }

    /// Build the graceful-abort payload for the Red band. Caller packages
    /// this into their crate's `SolveResult::Unknown` equivalent.
    ///
    /// `ay-core` does not depend on `SolveResult`, so the contract here is
    /// just the data tuple. See [`UnknownReason::MemoryPressure`].
    #[must_use]
    pub fn red_abort_reason(&self) -> UnknownReason {
        UnknownReason::MemoryPressure {
            rss_bytes: self.last_rss() as u64,
            budget_bytes: self.last_budget() as u64,
        }
    }
}
