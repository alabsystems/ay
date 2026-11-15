// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use ay_chc::engines::ExternalInvariantValidation as Kind;
use std::time::Duration;

#[test]
fn every_original_row_deadline_is_the_exact_started_plus_nanosecond_cap() {
    let archive = super::super::tests::fixture();
    for case in R34Row::ALL {
        let row = &archive.capture.rows[case.index()];
        let config = preparation::config(&archive, row).unwrap();
        let original = super::super::tests::original();
        let original_end = original.effective_deadline();
        let started = Instant::now()
            .checked_sub(Duration::from_millis(1))
            .unwrap();
        let end = started
            .checked_add(Duration::from_nanos(row.timeout_ns))
            .unwrap();
        let owner = row_owner(&original, &config.to_pdr_config(), started, row.timeout_ns).unwrap();
        // Exact equality catches even a nanosecond spent between a remainder
        // sample and capture: that interval must never extend the row grant.
        assert_eq!(owner.deadline(), end, "{case:?}");
        assert_eq!(owner.check(), None);
        assert_eq!(original.effective_deadline(), original_end);
        assert!(
            original.ticks() >= 2,
            "owner must debit the original counter"
        );
    }
}

#[test]
fn earlier_caller_deadline_and_shared_preconsumed_ticks_are_not_regranted() {
    let started = Instant::now();
    let caller_end = started.checked_add(Duration::from_secs(2)).unwrap();
    let mut original = ResourceGuard::new();
    original.set_deadline(Some(caller_end));
    original.set_rlimit(Some(10));
    original.tick(7).unwrap();
    let mut validation = PdrConfig::production(false);
    validation.solve_timeout = Some(Duration::from_secs(5));
    let owner = row_owner(&original, &validation, started, 5_000_000_000).unwrap();
    assert_eq!(owner.deadline(), caller_end);
    assert_eq!(original.deadline(), Some(caller_end));
    assert_eq!(original.ticks(), 8);
    for _ in 0..4 {
        let _ = owner.check();
    }
    assert_eq!(owner.check(), Some(Kind::WorkLimit));
    let spent = original.ticks();
    assert!((8..=10).contains(&spent));
    assert_eq!(owner.check(), Some(Kind::WorkLimit));
    assert_eq!(original.ticks(), spent);
    assert_eq!(original.deadline(), Some(caller_end));
}

#[test]
fn preparation_that_spent_the_entire_row_clock_cannot_enter_execution() {
    let original = super::super::tests::original();
    let caller_end = original.deadline();
    let validation = PdrConfig::production(false);
    let started = Instant::now().checked_sub(Duration::from_secs(1)).unwrap();
    let owner = row_owner(&original, &validation, started, 622_866_572).unwrap();
    assert_eq!(
        owner.deadline(),
        started
            .checked_add(Duration::from_nanos(622_866_572))
            .unwrap()
    );
    assert_eq!(owner.check(), Some(Kind::Timeout));
    let mut entered = false;
    let result = owner
        .with_resources(|| {
            entered = true;
            Ok(())
        })
        .unwrap();
    assert_eq!(result, Err(Kind::Timeout));
    assert!(!entered);
    assert_eq!(original.ticks(), 0);
    assert_eq!(original.deadline(), caller_end);
}

#[test]
fn zero_row_cap_stays_expired_even_with_a_longer_validation_timeout() {
    let original = super::super::tests::original();
    let started = Instant::now();
    let mut validation = PdrConfig::production(false);
    validation.solve_timeout = Some(Duration::from_secs(60));
    let owner = row_owner(&original, &validation, started, 0).unwrap();
    assert_eq!(owner.deadline(), started);
    assert_eq!(owner.check(), Some(Kind::Timeout));
    assert_eq!(original.ticks(), 0);
}
