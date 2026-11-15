// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Instant, ReplayCancellation, ReplayLimit, ReplayLimitRefusal};
use std::{cell::Cell, time::Duration};

#[test]
fn diagnostic_legacy_admission_does_not_add_a_clock_observation() {
    assert_eq!(
        ReplayLimit::Legacy.check_diagnostic_with_clock(&mut || panic!("legacy clock sample")),
        Ok(())
    );
}

#[test]
fn diagnostic_entry_cancellation_precedes_clock_and_expiry() {
    let token = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    token.cancel();
    let limit = ReplayLimit::Cancellable {
        deadline: Instant::now(),
        cancellation: &cancellation,
    };
    assert_eq!(
        limit.check_diagnostic_with_clock(&mut || panic!("cancelled entry clock sample")),
        Err(ReplayLimitRefusal::InheritedCancellation)
    );
}

#[test]
fn diagnostic_late_cancellation_keeps_the_original_single_clock_sample() {
    let token = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    let now = Instant::now();
    let samples = Cell::new(0usize);
    let limit = ReplayLimit::Cancellable {
        deadline: now + Duration::from_secs(60),
        cancellation: &cancellation,
    };
    let result = limit.check_diagnostic_with_clock(&mut || {
        samples.set(samples.get() + 1);
        token.cancel();
        now
    });
    assert_eq!(result, Err(ReplayLimitRefusal::InheritedCancellation));
    assert_eq!(samples.get(), 1);
}

#[test]
fn diagnostic_expiry_precedes_postclock_cancel_without_changing_observation_order() {
    let token = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    let deadline = Instant::now() + Duration::from_secs(60);
    let samples = Cell::new(0usize);
    let limit = ReplayLimit::Cancellable {
        deadline,
        cancellation: &cancellation,
    };
    let result = limit.check_diagnostic_with_clock(&mut || {
        samples.set(samples.get() + 1);
        token.cancel();
        deadline
    });
    assert_eq!(result, Err(ReplayLimitRefusal::OriginalDeadline));
    assert_eq!(samples.get(), 1);
    token.reset();
    assert!(cancellation.is_cancelled());
}

#[test]
fn diagnostic_owner_intersection_preserves_both_ceilings_with_one_sample() {
    let now = Instant::now();
    let past = now - Duration::from_secs(1);
    let future = now + Duration::from_secs(60);
    for (limit, owner, expected) in [
        (
            ReplayLimit::Until(past),
            Some(future),
            Err(ReplayLimitRefusal::OriginalDeadline),
        ),
        (
            ReplayLimit::Until(future),
            Some(past),
            Err(ReplayLimitRefusal::OriginalDeadline),
        ),
        (
            ReplayLimit::Legacy,
            Some(past),
            Err(ReplayLimitRefusal::OriginalDeadline),
        ),
        (
            ReplayLimit::Until(now),
            Some(now),
            Err(ReplayLimitRefusal::OriginalDeadline),
        ),
        (ReplayLimit::Until(future), Some(future), Ok(())),
        (ReplayLimit::Legacy, Some(future), Ok(())),
    ] {
        let samples = Cell::new(0);
        let actual = limit.check_diagnostic_with_clock_and_owner(
            &mut || {
                samples.set(samples.get() + 1);
                now
            },
            owner,
        );
        assert_eq!(actual, expected);
        assert_eq!(samples.get(), 1);
    }
}

#[test]
fn diagnostic_owner_intersection_keeps_cancellation_observations_and_priority() {
    let now = Instant::now();
    let token = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    token.cancel();
    let limit = ReplayLimit::Cancellable {
        deadline: now,
        cancellation: &cancellation,
    };
    assert_eq!(
        limit.check_diagnostic_with_clock_and_owner(
            &mut || panic!("cancelled entry clock sample"),
            Some(now)
        ),
        Err(ReplayLimitRefusal::InheritedCancellation)
    );
    for expired in [false, true] {
        let token = crate::CancellationToken::new();
        let cancellation = ReplayCancellation::new(&token);
        let limit = ReplayLimit::Cancellable {
            deadline: if expired {
                now
            } else {
                now + Duration::from_secs(60)
            },
            cancellation: &cancellation,
        };
        let samples = Cell::new(0);
        let actual = limit.check_diagnostic_with_clock_and_owner(
            &mut || {
                samples.set(samples.get() + 1);
                token.cancel();
                now
            },
            Some(now),
        );
        assert_eq!(
            actual,
            Err(if expired {
                ReplayLimitRefusal::OriginalDeadline
            } else {
                ReplayLimitRefusal::InheritedCancellation
            })
        );
        assert_eq!(samples.get(), 1);
        token.reset();
        assert!(cancellation.is_cancelled());
    }
}
