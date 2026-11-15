// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::budget_tests::deadline_tests::checked_ground_fixture;
use super::*;

mod ground;
mod payload;
mod smt;

const BUDGET: Duration = Duration::from_secs(600);

fn live_control(cancellation: &ReplayCancellation) -> FreshRecheckControl<'_> {
    FreshRecheckControl {
        deadline: fresh_recheck_deadline(Instant::now(), BUDGET).unwrap(),
        cancellation: Some(cancellation),
    }
}

fn assert_interrupted<T>(result: ChcResult<T>) {
    match result {
        Ok(_) => panic!("cancelled retained validation must not be admitted"),
        Err(error) => assert!(error.to_string().contains("interrupted"), "{error}"),
    }
}

#[test]
fn public_precancel_inherited_retry_and_metadata_are_unchanged() {
    let checked = checked_ground_fixture();
    let metadata = checked.proof_run().metadata().to_json_value();
    let summary = checked.summary().to_json_value();
    let manifest = checked.manifest().to_json_value();
    let payload = checked
        .obligation_payloads()
        .next()
        .unwrap()
        .payload_bytes()
        .to_vec();
    let parent = CancellationToken::new();
    let token = parent.child().child();
    let sibling = parent.child();
    parent.cancel();
    assert_interrupted(checked.recheck_with_fresh_ay_with_cancellation(BUDGET, &token));
    parent.reset();
    checked
        .recheck_with_fresh_ay_with_cancellation(BUDGET, &token)
        .unwrap();
    checked.recheck_with_fresh_ay(BUDGET).unwrap();
    assert!(!parent.is_cancelled());
    assert!(!sibling.is_cancelled());
    assert_eq!(checked.proof_run().metadata().to_json_value(), metadata);
    assert_eq!(checked.summary().to_json_value(), summary);
    assert_eq!(checked.manifest().to_json_value(), manifest);
    assert_eq!(
        checked
            .obligation_payloads()
            .next()
            .unwrap()
            .payload_bytes(),
        payload.as_slice()
    );
}

#[test]
fn typed_entry_preserves_zero_alignment_and_overflow_precedence() {
    let checked = checked_ground_fixture();
    let token = CancellationToken::new();
    token.cancel();
    for budget in [Duration::ZERO, Duration::MAX] {
        assert_eq!(
            checked
                .recheck_with_fresh_ay_with_cancellation(budget, &token)
                .unwrap_err()
                .to_string(),
            checked
                .recheck_with_fresh_ay(budget)
                .unwrap_err()
                .to_string(),
        );
    }
    let mut misaligned = checked.clone();
    misaligned.obligation_payloads.clear();
    let error = misaligned
        .recheck_with_fresh_ay_with_controls(BUDGET, Some(&token), &mut || {
            panic!("alignment must precede even the initial clock sample")
        })
        .unwrap_err();
    assert!(error
        .to_string()
        .contains("payload alignment is incomplete"));
}

#[test]
fn cancellation_at_each_retained_outer_boundary_is_terminal() {
    let checked = checked_ground_fixture();
    let start = Instant::now();
    let live = CancellationToken::new();
    let mut samples = 0;
    checked
        .recheck_with_fresh_ay_with_controls(BUDGET, Some(&live), &mut || {
            samples += 1;
            start
        })
        .unwrap();
    // Entry, payload admission and recheck admission: every sample is an
    // admission, none follows the last row (#completed-check-accepted).
    assert!(samples >= 3);
    for stop_at in 1..=samples {
        let parent = CancellationToken::new();
        let token = parent.child();
        let mut ordinal = 0;
        assert_interrupted(checked.recheck_with_fresh_ay_with_controls(
            BUDGET,
            Some(&token),
            &mut || {
                ordinal += 1;
                if ordinal == stop_at {
                    parent.cancel();
                }
                start
            },
        ));
        assert_eq!(
            ordinal, stop_at,
            "no later row or final clock after refusal"
        );
    }
}

#[test]
fn live_token_cannot_renew_the_original_wall() {
    let checked = checked_ground_fixture();
    let token = CancellationToken::new();
    let start = Instant::now();
    let deadline = fresh_recheck_deadline(start, BUDGET).unwrap();
    let mut ordinal = 0;
    let error = checked
        .recheck_with_fresh_ay_with_controls(BUDGET, Some(&token), &mut || {
            ordinal += 1;
            if ordinal == 1 {
                start
            } else {
                deadline
            }
        })
        .unwrap_err();
    assert_eq!(ordinal, 2);
    assert!(error
        .to_string()
        .contains("budget exhausted before obligation"));
    assert!(
        !token.is_cancelled(),
        "deadline refusal must not poison caller state"
    );
}

#[test]
fn payload_preflight_is_not_started_after_sticky_parent_refusal() {
    let checked = checked_ground_fixture();
    let parent = CancellationToken::new();
    let token = parent.child();
    let cancellation = ReplayCancellation::new(&token);
    let observer = cancellation.clone();
    parent.cancel();
    assert!(observer.is_cancelled());
    parent.reset();
    let item = checked.obligation_payloads().next().unwrap();
    assert_interrupted(validate_payload_with_control(
        item.payload,
        item.obligation(),
        live_control(&cancellation),
        &mut || panic!("sticky refusal precedes payload work and its clock sample"),
    ));
    assert!(!token.is_cancelled());
}
