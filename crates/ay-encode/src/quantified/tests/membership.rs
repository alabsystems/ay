// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn foreign_source_or_candidate_cannot_pass_binding_or_trigger_replay() {
    let obligations = obligations();
    let start = Instant::now();
    let time = Cell::new(Duration::ZERO);
    let clock = || start + time.get();
    let parent = CancellationToken::new();
    let control = control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
    assert!(schedule::validate_obligations(
        &schedule::digest(source().source_smtlib()),
        &obligations,
        &control
    )
    .is_ok());
    assert!(schedule::validate_obligations("foreign aggregate", &obligations, &control).is_err());
    let mut fake = Fake::new(
        &time,
        &parent,
        vec![
            Action {
                candidate: Candidate::Foreign,
                ..Action::default()
            };
            2
        ],
    );
    let batch = schedule::run(obligations, &control, None, &mut fake);
    assert!(!batch.all_checked);
    assert!(batch
        .rows
        .iter()
        .all(|row| matches!(&row.outcome, schedule::Outcome::Error(_))));
    assert!(fake
        .calls
        .iter()
        .all(|call| matches!(call, Call::Solve(..))));
}

#[test]
fn omitted_reordered_duplicate_or_changed_rows_cannot_claim_complete_membership() {
    let obligations = obligations();
    let expected: Vec<_> = obligations.iter().map(|o| o.id().clone()).collect();
    let start = Instant::now();
    let time = Cell::new(Duration::ZERO);
    let clock = || start + time.get();
    let parent = CancellationToken::new();
    let control = control::Control::new(start, Duration::from_secs(20), &parent, &clock).unwrap();
    let mut fake = Fake::new(&time, &parent, vec![Action::default(); 2]);
    let mut batch = schedule::run(obligations, &control, None, &mut fake);
    assert!(schedule::complete(&expected, &batch.rows, &fake));
    assert!(!schedule::complete(&expected, &batch.rows[..1], &fake));
    batch.rows.swap(0, 1);
    assert!(!schedule::complete(&expected, &batch.rows, &fake));
    batch.rows.swap(0, 1);
    // The source/ID pair is now one sealed object; replacing only one private
    // component is no longer representable at the encoder boundary.
    let original = batch.rows[1].obligation.clone();
    batch.rows[1].obligation = batch.rows[0].obligation.clone();
    assert!(!schedule::complete(&expected, &batch.rows, &fake));
    batch.rows[1].obligation = original;
    batch.rows[0].obligation = batch.rows[1].obligation.clone();
    assert!(!schedule::complete(&expected, &batch.rows, &fake));
    assert!(!schedule::complete(&[], &[], &fake));
}
