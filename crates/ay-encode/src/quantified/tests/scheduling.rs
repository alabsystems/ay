// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use schedule::Outcome;

#[test]
fn fair_share_reserves_replay_and_rolls_unused_time_forward() {
    let start = Instant::now();
    let time = Cell::new(Duration::ZERO);
    let clock = || start + time.get();
    let parent = CancellationToken::new();
    let control = control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
    let mut fake = Fake::new(&time, &parent, vec![Action::default(); 2]);
    let batch = schedule::run(obligations(), &control, Some(4096), &mut fake);
    assert!(batch.all_checked);
    assert_eq!(batch.rows.len(), 2);
    assert_eq!(batch.rows[0].obligation.id().label(), "error_p0");
    assert_eq!(batch.rows[1].obligation.id().label(), "error_p1");
    assert_eq!(
        fake.calls,
        vec![
            Call::Solve(Duration::from_secs(5), Some(4096)),
            Call::Replay(Duration::from_secs(8)),
            Call::Solve(Duration::from_millis(8500), Some(4096)),
            Call::Replay(Duration::from_secs(15)),
        ]
    );
}

#[test]
fn late_local_expiry_preserves_checked_prefix_and_never_refreshes_total_budget() {
    let start = Instant::now();
    let time = Cell::new(Duration::ZERO);
    let clock = || start + time.get();
    let parent = CancellationToken::new();
    let control = control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
    let mut fake = Fake::new(
        &time,
        &parent,
        vec![
            Action::default(),
            Action {
                replay_time: Duration::from_secs(16),
                ..Action::default()
            },
        ],
    );
    let batch = schedule::run(obligations(), &control, None, &mut fake);
    assert!(!batch.all_checked);
    assert!(matches!(&batch.rows[0].outcome, Outcome::CheckedSafe(_)));
    assert!(matches!(
        &batch.rows[1].outcome,
        Outcome::Unknown(QuantifiedQueryUnknownReason::BudgetExhausted)
    ));
}

#[test]
fn solve_or_replay_observation_stays_cancelled_across_parent_reset() {
    for action in [
        Action {
            candidate: Candidate::CancelReset,
            ..Action::default()
        },
        Action {
            replay: Replay::CancelReset,
            ..Action::default()
        },
    ] {
        let start = Instant::now();
        let time = Cell::new(Duration::ZERO);
        let clock = || start + time.get();
        let parent = CancellationToken::new();
        let control =
            control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
        let mut fake = Fake::new(&time, &parent, vec![action]);
        let batch = schedule::run(obligations(), &control, None, &mut fake);
        assert_eq!(batch.rows.len(), 2);
        assert!(!batch.all_checked);
        assert!(batch.rows.iter().all(|row| matches!(
            &row.outcome,
            Outcome::Unknown(QuantifiedQueryUnknownReason::Cancelled)
        )));
        assert_eq!(
            fake.calls
                .iter()
                .filter(|call| matches!(call, Call::Solve(..)))
                .count(),
            1
        );
        assert!(!parent.is_cancelled());
        let fresh =
            control::Control::new(clock(), Duration::from_secs(20), &parent, &clock).unwrap();
        let mut fresh_fake = Fake::new(&time, &parent, vec![Action::default(); 2]);
        assert!(schedule::run(obligations(), &fresh, None, &mut fresh_fake).all_checked);
    }
}

#[test]
fn ordinary_errors_and_unknowns_keep_all_later_rows_visible() {
    for action in [
        Action {
            candidate: Candidate::Unknown,
            ..Action::default()
        },
        Action {
            candidate: Candidate::Error,
            ..Action::default()
        },
        Action {
            replay: Replay::Rejected,
            ..Action::default()
        },
        Action {
            replay: Replay::Error,
            ..Action::default()
        },
    ] {
        let start = Instant::now();
        let time = Cell::new(Duration::ZERO);
        let clock = || start + time.get();
        let parent = CancellationToken::new();
        let control =
            control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
        let mut fake = Fake::new(&time, &parent, vec![action, Action::default()]);
        let batch = schedule::run(obligations(), &control, None, &mut fake);
        assert_eq!(batch.rows.len(), 2);
        assert!(!batch.all_checked);
        assert!(!matches!(&batch.rows[0].outcome, Outcome::CheckedSafe(_)));
        assert!(matches!(&batch.rows[1].outcome, Outcome::CheckedSafe(_)));
    }
}

#[test]
fn first_row_local_overrun_does_not_consume_a_fresh_batch_budget() {
    let start = Instant::now();
    let time = Cell::new(Duration::ZERO);
    let clock = || start + time.get();
    let parent = CancellationToken::new();
    let control = control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
    let mut fake = Fake::new(
        &time,
        &parent,
        vec![
            Action {
                solve_time: Duration::from_secs(11),
                ..Action::default()
            },
            Action::default(),
        ],
    );
    let batch = schedule::run(obligations(), &control, None, &mut fake);
    assert!(!batch.all_checked);
    assert!(matches!(
        &batch.rows[0].outcome,
        Outcome::Unknown(QuantifiedQueryUnknownReason::BudgetExhausted)
    ));
    assert!(matches!(&batch.rows[1].outcome, Outcome::CheckedSafe(_)));
    assert_eq!(
        fake.calls[1],
        Call::Solve(Duration::from_millis(4500), None)
    );
}

#[test]
fn expiry_at_every_clock_checkpoint_denies_aggregate_admission() {
    let run = |expire_at: usize| {
        let start = Instant::now();
        let time = Cell::new(Duration::ZERO);
        let polls = Cell::new(0usize);
        let expired = Cell::new(false);
        let armed = Cell::new(false);
        let clock = || {
            polls.set(polls.get() + 1);
            if armed.get() && polls.get() == expire_at {
                expired.set(true);
            }
            start
                + if expired.get() {
                    Duration::from_secs(100)
                } else {
                    time.get()
                }
        };
        let parent = CancellationToken::new();
        let control =
            control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
        polls.set(0);
        armed.set(true);
        let mut fake = Fake::new(&time, &parent, vec![Action::default(); 2]);
        let batch = schedule::run(obligations(), &control, None, &mut fake);
        (batch, polls.get())
    };
    let (live, count) = run(usize::MAX);
    assert!(live.all_checked);
    assert!(count > 10);
    for ordinal in 1..=count {
        let (stopped, _) = run(ordinal);
        assert!(!stopped.all_checked, "clock ordinal {ordinal}");
        assert_eq!(stopped.rows.len(), 2);
    }
}

#[test]
fn original_solver_or_replay_error_precedes_a_concurrent_expiry() {
    for action in [
        Action {
            candidate: Candidate::Error,
            solve_time: Duration::from_secs(21),
            ..Action::default()
        },
        Action {
            replay: Replay::Error,
            replay_time: Duration::from_secs(21),
            ..Action::default()
        },
    ] {
        let start = Instant::now();
        let time = Cell::new(Duration::ZERO);
        let clock = || start + time.get();
        let parent = CancellationToken::new();
        let control =
            control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
        let mut fake = Fake::new(&time, &parent, vec![action]);
        let batch = schedule::run(obligations(), &control, None, &mut fake);
        assert!(!batch.all_checked);
        assert!(matches!(
            &batch.rows[0].outcome,
            Outcome::Error(crate::EncodeError::Chc(_))
        ));
        assert!(matches!(
            &batch.rows[1].outcome,
            Outcome::Unknown(QuantifiedQueryUnknownReason::BudgetExhausted)
        ));
    }
}
