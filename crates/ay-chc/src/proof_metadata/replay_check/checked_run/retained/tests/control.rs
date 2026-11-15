// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Deterministic compatibility controls; these do not mint source authority.

use super::*;

#[test]
fn retained_row_checks_the_original_wall_before_and_after_work() {
    let start = Instant::now();
    let ceiling = start + BUDGET;
    let control = FreshRecheckControl {
        deadline: ceiling,
        cancellation: None,
    };
    let obligation = row(b"test-only source", b"test-only bundle");
    for (phase, expected) in [
        (RetainedRowPhase::Before, "before obligation"),
        (RetainedRowPhase::During, "during obligation"),
    ] {
        control
            .check_retained_row(&mut || start, &obligation, phase)
            .unwrap();
        let error = control
            .check_retained_row(&mut || ceiling, &obligation, phase)
            .unwrap_err();
        assert!(error.to_string().contains(expected), "{error}");
        assert_eq!(control.deadline, ceiling);
    }
}

#[test]
fn retained_row_clock_cancellation_stays_sticky_after_parent_reset() {
    let parent = CancellationToken::new();
    let cancellation = ReplayCancellation::new(&parent.child());
    let control = FreshRecheckControl {
        deadline: deadline(),
        cancellation: Some(&cancellation),
    };
    let obligation = row(b"test-only source", b"test-only bundle");
    let start = Instant::now();
    let mut samples = 0;
    let error = control
        .check_retained_row(
            &mut || {
                samples += 1;
                parent.cancel();
                start
            },
            &obligation,
            RetainedRowPhase::During,
        )
        .unwrap_err();
    assert!(error.to_string().contains("interrupted"), "{error}");
    assert_eq!(samples, 1);
    parent.reset();
    assert!(control
        .check_retained_row(
            &mut || panic!("observed refusal cannot sample another clock"),
            &obligation,
            RetainedRowPhase::Before,
        )
        .is_err());
}

#[test]
fn retained_request_final_gate_refuses_the_original_expired_wall() {
    let start = Instant::now();
    let ceiling = start + BUDGET;
    let control = FreshRecheckControl {
        deadline: ceiling,
        cancellation: None,
    };
    let mut live = || true;
    let progress = RetainedReplayProgress::new(control.limit(), &mut live).unwrap();
    assert_eq!(progress.deadline(), ceiling);
    let mut samples = 0;
    let error = finish_request(Some(progress), control, &mut || {
        samples += 1;
        ceiling
    })
    .unwrap_err();
    assert_eq!(samples, 1);
    assert!(error
        .to_string()
        .contains("budget exhausted after final obligation"));
}

#[test]
fn retained_request_final_gate_observes_inherited_cancellation() {
    let parent = CancellationToken::new();
    let cancellation = ReplayCancellation::new(&parent.child());
    let control = FreshRecheckControl {
        deadline: deadline(),
        cancellation: Some(&cancellation),
    };
    let mut live = || true;
    let progress = RetainedReplayProgress::new(control.limit(), &mut live).unwrap();
    parent.cancel();
    let error = finish_request(Some(progress), control, &mut || {
        panic!("cancelled retained completion must not sample the clock")
    })
    .unwrap_err();
    assert!(error.to_string().contains("interrupted"), "{error}");
    parent.reset();
    assert!(cancellation.is_cancelled());
}

#[test]
fn legacy_request_completion_does_not_sample_clock_or_cancellation() {
    let token = CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    token.cancel();
    let control = FreshRecheckControl {
        deadline: Instant::now(),
        cancellation: Some(&cancellation),
    };
    finish_request(None, control, &mut || {
        panic!("completed legacy-only request has no terminal clock")
    })
    .unwrap();
}

#[test]
fn retained_request_finishes_under_the_live_original_wall() {
    let start = Instant::now();
    let ceiling = start + BUDGET;
    let control = FreshRecheckControl {
        deadline: ceiling,
        cancellation: None,
    };
    let mut live = || true;
    let progress = RetainedReplayProgress::new(control.limit(), &mut live).unwrap();
    let mut samples = 0;
    finish_request(Some(progress), control, &mut || {
        samples += 1;
        start
    })
    .unwrap();
    assert_eq!(samples, 1);
}
