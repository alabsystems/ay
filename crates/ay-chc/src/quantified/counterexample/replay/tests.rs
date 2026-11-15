// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::time::Duration;

#[test]
fn local_slice_expiry_is_retryable_without_stopping_siblings() {
    let token = CancellationToken::new();
    let outer = Instant::now() + Duration::from_secs(30);
    let control = SourceControl::new(outer, &token);
    for outcome in [Probe::Sat, Probe::Unsat, Probe::Inconclusive] {
        assert_eq!(
            finish(outcome, Budget::wall(Instant::now()), &control),
            Probe::Inconclusive
        );
        assert!(control.poll().is_some());
    }
    assert_eq!(
        finish(Probe::Sat, Budget::wall(outer), &control),
        Probe::Sat
    );
    assert_eq!(
        finish(Probe::Unsat, Budget::wall(outer), &control),
        Probe::Unsat
    );
    assert_eq!(
        finish(Probe::Inconclusive, Budget::wall(outer), &control),
        Probe::Inconclusive
    );
    assert_eq!(
        finish(Probe::Terminal, Budget::wall(Instant::now()), &control),
        Probe::Terminal
    );
}

#[test]
fn terminal_parent_controls_override_every_late_native_outcome_and_stay_sticky() {
    let token = CancellationToken::new();
    let outer = Instant::now() + Duration::from_secs(30);
    let control = SourceControl::new(outer, &token);
    token.cancel();
    for outcome in [
        Probe::Sat,
        Probe::Unsat,
        Probe::Inconclusive,
        Probe::Terminal,
    ] {
        assert_eq!(
            finish(outcome, Budget::wall(outer), &control),
            Probe::Terminal
        );
    }
    token.reset();
    assert_eq!(
        finish(Probe::Sat, Budget::wall(outer), &control),
        Probe::Terminal
    );
    let fresh = SourceControl::new(outer, &token);
    assert_eq!(finish(Probe::Sat, Budget::wall(outer), &fresh), Probe::Sat);
    assert!(fresh.bytes(usize::MAX).is_none());
    assert_eq!(
        finish(Probe::Sat, Budget::wall(outer), &fresh),
        Probe::Terminal
    );
}

#[test]
fn entry_refusals_do_not_start_a_solver_or_promote_inconclusive_to_sat() {
    let token = CancellationToken::new();
    let outer = Instant::now() + Duration::from_secs(30);
    let control = SourceControl::new(outer, &token);
    assert_eq!(
        probe(
            "invalid",
            Budget::wall(Instant::now()),
            None,
            &token,
            &control
        ),
        Probe::Inconclusive
    );
    assert!(control.poll().is_some());
    assert_eq!(
        probe("invalid", Budget::wall(outer), Some(0), &token, &control),
        Probe::Terminal
    );
    assert_eq!(
        probe("invalid", Budget::wall(outer), None, &token, &control),
        Probe::Inconclusive
    );
    assert!(!validate("invalid", outer, None, &token, &control));
}

/// A work-limited slice is spent by the probing thread's CPU, not by the wall:
/// with the backstop far away, an exhausted CPU allowance still makes a late
/// native outcome retryable, and an unexhausted one keeps it.
#[test]
fn work_limited_slices_expire_on_cpu_and_keep_the_wall_as_backstop() {
    let Some(clock) = ThreadCpuClock::current() else {
        return;
    };
    let token = CancellationToken::new();
    let outer = Instant::now() + Duration::from_secs(30);
    let control = SourceControl::new(outer, &token);
    let now = clock.elapsed().unwrap_or_default();
    let spent = Budget::work(outer, clock, now);
    let open = Budget::work(outer, clock, now + Duration::from_secs(600));
    let backstopped = Budget::work(Instant::now(), clock, now + Duration::from_secs(600));
    for outcome in [Probe::Sat, Probe::Unsat, Probe::Inconclusive] {
        assert_eq!(finish(outcome, spent, &control), Probe::Inconclusive);
        assert_eq!(finish(outcome, open, &control), outcome);
        assert_eq!(finish(outcome, backstopped, &control), Probe::Inconclusive);
    }
    assert_eq!(
        probe("invalid", spent, None, &token, &control),
        Probe::Inconclusive
    );
    assert!(
        control.poll().is_some(),
        "a spent slice never stops the search"
    );
}
