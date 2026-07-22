// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Offline skip-rate accounting for the approximate BCP filter.
//!
//! This crate has no dependency on `ay-sat`, so the counter can be
//! driven by microbenches that replay a recorded trail.  The
//! feature-gated `ay-sat` observer records equivalent solver-level
//! counters rather than using this type directly.

/// Running totals for the filter: how many clauses were inspected and
/// how many were skipped because the filter proved they were not unit
/// and not falsified.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct FilterMetrics {
    /// Total number of `may_be_unit_or_falsified` probes.
    pub checked: u64,
    /// Number of probes that returned `false` (clause skipped).
    pub skipped: u64,
}

impl FilterMetrics {
    /// Fresh zeroed counter.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            checked: 0,
            skipped: 0,
        }
    }

    /// Record one probe outcome.  `skipped = true` means the filter
    /// returned `false` (clause was ruled out as definitely neither
    /// unit nor falsified).
    #[inline]
    pub fn record(&mut self, skipped: bool) {
        self.checked += 1;
        if skipped {
            self.skipped += 1;
        }
    }

    /// Fraction of probes that resulted in a skip.  Returns `None` when
    /// no probes have been recorded yet — a `0/0` would otherwise have
    /// to be reported as a finite number and falsely imply "0% skip
    /// rate."
    #[must_use]
    pub fn skip_rate(&self) -> Option<f64> {
        if self.checked == 0 {
            None
        } else {
            // Intentional integer-to-float cast: both values are bounded
            // by u64, and the ratio is always in [0.0, 1.0] so precision
            // loss is not a concern.
            #[allow(clippy::cast_precision_loss)]
            let rate = self.skipped as f64 / self.checked as f64;
            Some(rate)
        }
    }

    /// Merge another counter in-place — useful when aggregating across
    /// threads or benchmark runs.
    #[inline]
    pub fn merge(&mut self, other: Self) {
        self.checked = self.checked.saturating_add(other.checked);
        self.skipped = self.skipped.saturating_add(other.skipped);
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn skip_rate_is_none_when_empty() {
        assert_eq!(FilterMetrics::new().skip_rate(), None);
    }

    #[test]
    fn record_counts_skips_and_total() {
        let mut m = FilterMetrics::new();
        m.record(true);
        m.record(false);
        m.record(true);
        assert_eq!(m.checked, 3);
        assert_eq!(m.skipped, 2);
        assert!((m.skip_rate().unwrap() - 2.0 / 3.0).abs() < 1e-12);
    }

    #[test]
    fn merge_sums_both_counters() {
        let mut a = FilterMetrics::new();
        a.record(true);
        a.record(false);
        let mut b = FilterMetrics::new();
        b.record(true);
        a.merge(b);
        assert_eq!(a.checked, 3);
        assert_eq!(a.skipped, 2);
    }
}
