// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_current_memory_returns_nonzero() {
    let bytes = current_memory_bytes();
    // On supported platforms, we should get a non-zero value
    // A typical Rust test process uses at least 1MB
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    assert!(
        bytes > 0,
        "Memory should be non-zero on supported platforms"
    );
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    assert!(
        bytes > 1024 * 1024,
        "Memory should be at least 1MB for a test process"
    );
}

#[test]
fn test_memory_exceeded_no_limit() {
    // No limit means never exceeded
    assert!(!memory_exceeded(None));
}

#[test]
fn test_memory_exceeded_huge_limit() {
    // 100GB limit should never be exceeded by a test
    assert!(!memory_exceeded(Some(100 * 1024 * 1024 * 1024)));
}

#[test]
fn test_memory_exceeded_tiny_limit() {
    // 1KB limit should always be exceeded by a running process
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    assert!(memory_exceeded(Some(1024)));
}

#[test]
fn stale_peak_does_not_exhaust_a_later_solver() {
    let current = observed_memory_bytes(64 * 1024 * 1024, || 2 * 1024 * 1024 * 1024);

    assert_eq!(current, 64 * 1024 * 1024);
    assert!(!memory_exceeded_at(Some(128 * 1024 * 1024), current));
}

#[test]
fn live_footprint_over_the_limit_still_exhausts_the_solver() {
    let current = observed_memory_bytes(192 * 1024 * 1024, || 2 * 1024 * 1024 * 1024);

    assert!(memory_exceeded_at(Some(128 * 1024 * 1024), current));
}

#[test]
fn peak_rss_is_the_conservative_fallback_when_live_measurement_fails() {
    let current = observed_memory_bytes(0, || 2 * 1024 * 1024 * 1024);

    assert_eq!(current, 2 * 1024 * 1024 * 1024);
    assert!(memory_exceeded_at(Some(128 * 1024 * 1024), current));
}

#[test]
fn probe_clone_budget_charges_the_clone_not_the_process() {
    let cap = 2 * 1024 * 1024 * 1024_usize; // a parsed `:max-memory 2048`
    let own = 64 * 1024_usize; // this solver's whole term universe

    // A probe whose own clone is KiB fits, however large the surrounding
    // process is — the process footprint is not an input at all.
    assert!(probe_clone_fits(own, Some(cap)));
    // No declared cap: nothing to charge against.
    assert!(probe_clone_fits(own, None));

    // Still fail-closed: a clone above half the declared cap is refused, and
    // the boundary itself is inclusive.
    assert!(probe_clone_fits(cap / 2, Some(cap)));
    assert!(!probe_clone_fits(cap / 2 + 1, Some(cap)));
}
