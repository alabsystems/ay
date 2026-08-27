// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test-only observations of the recursive case-split time budget.

#![cfg(test)]

use crate::pdr::solver::PdrSolver;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

const NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS: u64 = u64::MAX;
static LAST_CASE_SPLIT_TIMEOUT_MS: AtomicU64 = AtomicU64::new(NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS);
/// Thread SMT deadline remaining, observed at the same point as
/// [`LAST_CASE_SPLIT_TIMEOUT_MS`]. The per-check timeout alone does not bound
/// this recursion (it issues one check per LEAF), so the deadline is what
/// bounds the whole split; see `PdrSolver::try_verification_case_split`.
static LAST_CASE_SPLIT_DEADLINE_MS: AtomicU64 = AtomicU64::new(NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS);

pub(super) fn record_case_split_timeout_for_tests(timeout: Option<Duration>) {
    let encoded = match timeout {
        Some(timeout) => u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX - 1),
        None => NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS,
    };
    LAST_CASE_SPLIT_TIMEOUT_MS.store(encoded, Ordering::Relaxed);
    let deadline = match crate::smt::deadline::smt_deadline_remaining() {
        Some(remaining) => u64::try_from(remaining.as_millis()).unwrap_or(u64::MAX - 1),
        None => NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS,
    };
    LAST_CASE_SPLIT_DEADLINE_MS.store(deadline, Ordering::Relaxed);
}

impl PdrSolver {
    pub(in crate::pdr::solver) fn reset_case_split_timeout_observation_for_tests() {
        LAST_CASE_SPLIT_TIMEOUT_MS.store(NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS, Ordering::Relaxed);
    }

    /// Reset the thread-SMT-deadline observation recorded inside the case-split
    /// recursion.
    pub(in crate::pdr) fn reset_case_split_deadline_observation_for_tests() {
        LAST_CASE_SPLIT_DEADLINE_MS.store(NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS, Ordering::Relaxed);
    }

    /// Thread SMT deadline remaining as seen inside the case-split recursion,
    /// or `None` when no deadline was armed there.
    pub(in crate::pdr) fn observed_case_split_deadline_for_tests() -> Option<Duration> {
        match LAST_CASE_SPLIT_DEADLINE_MS.load(Ordering::Relaxed) {
            NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS => None,
            ms => Some(Duration::from_millis(ms)),
        }
    }
}
