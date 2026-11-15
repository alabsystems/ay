// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use runner::{EvidenceKind, Runner};
use schedule::Outcome;
use std::collections::VecDeque;

struct Evidence {
    source: String,
    kind: EvidenceKind,
}

struct Mixed<'a> {
    fake: Fake<'a>,
    kinds: VecDeque<EvidenceKind>,
}

impl Runner for Mixed<'_> {
    type Evidence = Evidence;

    fn kind(&self, evidence: &Evidence) -> EvidenceKind {
        evidence.kind
    }

    fn solve(
        &mut self,
        problem: &QuantifiedChcProblem,
        budget: Duration,
        memory: Option<usize>,
        token: &CancellationToken,
    ) -> crate::Result<Option<Evidence>> {
        let kind = self
            .kinds
            .pop_front()
            .expect("kind for every attempted row");
        Ok(self
            .fake
            .solve(problem, budget, memory, token)?
            .map(|source| Evidence { source, kind }))
    }

    fn source<'a>(&self, evidence: &'a Evidence) -> &'a str {
        &evidence.source
    }

    fn recheck(
        &mut self,
        evidence: &Evidence,
        problem: &QuantifiedChcProblem,
        budget: Duration,
        token: &CancellationToken,
    ) -> crate::Result<bool> {
        self.fake.recheck(&evidence.source, problem, budget, token)
    }
}

fn mixed<'a>(
    time: &'a Cell<Duration>,
    parent: &'a CancellationToken,
    actions: Vec<Action>,
    kinds: Vec<EvidenceKind>,
) -> Mixed<'a> {
    Mixed {
        fake: Fake::new(time, parent, actions),
        kinds: kinds.into(),
    }
}

#[test]
fn checked_unsafe_is_distinct_and_dominates_safe_without_omitting_rows() {
    for unsafe_index in 0..2 {
        let start = Instant::now();
        let time = Cell::new(Duration::ZERO);
        let clock = || start + time.get();
        let parent = CancellationToken::new();
        let control =
            control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
        let mut kinds = vec![EvidenceKind::Safe; 2];
        kinds[unsafe_index] = EvidenceKind::Unsafe;
        let mut runner = mixed(&time, &parent, vec![Action::default(); 2], kinds);
        let batch = schedule::run(obligations(), &control, Some(4096), &mut runner);
        assert!(batch.checked_unsafe);
        assert!(!batch.all_checked);
        assert_eq!(batch.rows.len(), 2);
        assert_eq!(batch.rows[0].obligation.id().label(), "error_p0");
        assert_eq!(batch.rows[1].obligation.id().label(), "error_p1");
        assert!(matches!(
            batch.rows[unsafe_index].outcome,
            Outcome::CheckedUnsafe(_)
        ));
        assert!(matches!(
            batch.rows[1 - unsafe_index].outcome,
            Outcome::CheckedSafe(_)
        ));
        assert_eq!(runner.fake.calls.len(), 4, "both rows require fresh replay");
        assert_eq!(
            runner.fake.calls[0],
            Call::Solve(Duration::from_secs(5), Some(4096))
        );
        assert_eq!(runner.fake.calls[1], Call::Replay(Duration::from_secs(8)));
    }
}

#[test]
fn an_inconclusive_or_failed_sibling_does_not_hide_a_checked_counterexample() {
    for candidate in [Candidate::Unknown, Candidate::Error] {
        let start = Instant::now();
        let time = Cell::new(Duration::ZERO);
        let clock = || start + time.get();
        let parent = CancellationToken::new();
        let control =
            control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
        let mut runner = mixed(
            &time,
            &parent,
            vec![
                Action {
                    candidate,
                    ..Action::default()
                },
                Action::default(),
            ],
            vec![EvidenceKind::Safe, EvidenceKind::Unsafe],
        );
        let batch = schedule::run(obligations(), &control, None, &mut runner);
        assert!(batch.checked_unsafe);
        assert!(!batch.all_checked);
        assert_eq!(batch.rows.len(), 2);
        assert!(matches!(
            batch.rows[0].outcome,
            Outcome::Unknown(_) | Outcome::Error(_)
        ));
        assert!(matches!(batch.rows[1].outcome, Outcome::CheckedUnsafe(_)));
    }
}

#[test]
fn unsafe_requires_matching_source_successful_replay_and_live_row_controls() {
    for action in [
        Action {
            candidate: Candidate::Foreign,
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
        Action {
            candidate: Candidate::CancelReset,
            ..Action::default()
        },
        Action {
            replay: Replay::CancelReset,
            ..Action::default()
        },
        Action {
            solve_time: Duration::from_secs(11),
            ..Action::default()
        },
        Action {
            replay_time: Duration::from_secs(11),
            ..Action::default()
        },
    ] {
        let start = Instant::now();
        let time = Cell::new(Duration::ZERO);
        let clock = || start + time.get();
        let parent = CancellationToken::new();
        let control =
            control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
        let mut runner = mixed(
            &time,
            &parent,
            vec![action, Action::default()],
            vec![EvidenceKind::Unsafe, EvidenceKind::Safe],
        );
        let batch = schedule::run(obligations(), &control, None, &mut runner);
        assert!(!batch.checked_unsafe);
        assert!(!batch.all_checked);
        assert_eq!(batch.rows.len(), 2);
        assert!(!matches!(batch.rows[0].outcome, Outcome::CheckedUnsafe(_)));
    }
}

#[test]
fn late_batch_stop_keeps_the_checked_unsafe_row_but_revokes_aggregate_admission() {
    for second in [
        Action {
            candidate: Candidate::CancelReset,
            ..Action::default()
        },
        Action {
            replay: Replay::CancelReset,
            ..Action::default()
        },
        Action {
            solve_time: Duration::from_secs(21),
            ..Action::default()
        },
    ] {
        let start = Instant::now();
        let time = Cell::new(Duration::ZERO);
        let clock = || start + time.get();
        let parent = CancellationToken::new();
        let control =
            control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
        let mut runner = mixed(
            &time,
            &parent,
            vec![Action::default(), second],
            vec![EvidenceKind::Unsafe, EvidenceKind::Safe],
        );
        let batch = schedule::run(obligations(), &control, None, &mut runner);
        assert!(!batch.checked_unsafe);
        assert!(!batch.all_checked);
        assert_eq!(batch.rows.len(), 2);
        assert!(matches!(batch.rows[0].outcome, Outcome::CheckedUnsafe(_)));
        assert!(matches!(batch.rows[1].outcome, Outcome::Unknown(_)));
    }
}

#[test]
fn unsafe_membership_rejects_subset_reorder_foreign_source_and_wrong_evidence_kind() {
    let start = Instant::now();
    let time = Cell::new(Duration::ZERO);
    let clock = || start + time.get();
    let parent = CancellationToken::new();
    let control = control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
    let expected: Vec<_> = obligations().iter().map(|o| o.id().clone()).collect();
    let mut runner = mixed(
        &time,
        &parent,
        vec![Action::default(); 2],
        vec![EvidenceKind::Unsafe, EvidenceKind::Safe],
    );
    let mut batch = schedule::run(obligations(), &control, None, &mut runner);
    assert!(schedule::complete_unsafe(&expected, &batch.rows, &runner));
    assert!(!schedule::complete_unsafe(
        &expected,
        &batch.rows[..1],
        &runner
    ));
    batch.rows.swap(0, 1);
    assert!(!schedule::complete_unsafe(&expected, &batch.rows, &runner));
    batch.rows.swap(0, 1);
    let original = batch.rows[0].obligation.clone();
    batch.rows[0].obligation = batch.rows[1].obligation.clone();
    assert!(!schedule::complete_unsafe(&expected, &batch.rows, &runner));
    batch.rows[0].obligation = original;
    let Outcome::CheckedUnsafe(evidence) = &mut batch.rows[0].outcome else {
        panic!("checked unsafe fixture")
    };
    evidence.kind = EvidenceKind::Safe;
    assert!(!schedule::complete_unsafe(&expected, &batch.rows, &runner));
    let Outcome::CheckedUnsafe(evidence) = &mut batch.rows[0].outcome else {
        panic!("checked unsafe fixture")
    };
    evidence.kind = EvidenceKind::Unsafe;
    evidence.source.push_str(" foreign");
    assert!(!schedule::complete_unsafe(&expected, &batch.rows, &runner));
}

#[test]
fn unsafe_aggregate_is_refused_at_every_clock_checkpoint() {
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
        let mut runner = mixed(
            &time,
            &parent,
            vec![Action::default(); 2],
            vec![EvidenceKind::Unsafe, EvidenceKind::Safe],
        );
        let batch = schedule::run(obligations(), &control, None, &mut runner);
        (batch, polls.get())
    };
    let (live, count) = run(usize::MAX);
    assert!(live.checked_unsafe);
    assert!(!live.all_checked);
    assert!(count > 10);
    for ordinal in 1..=count {
        let (stopped, _) = run(ordinal);
        assert!(!stopped.checked_unsafe, "clock ordinal {ordinal}");
        assert!(!stopped.all_checked);
        assert_eq!(stopped.rows.len(), 2);
    }
}
