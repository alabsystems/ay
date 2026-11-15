// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::time::Duration;

#[test]
fn every_callback_refusal_is_sticky_including_post_cleanup_admission() {
    let dag = fixture(4_096);
    let units = [n(0), n(1)];
    let limits = ResolutionValidationLimits::default();
    let (expected, total) = measured(&dag, &units, &limits);
    assert!(expected.is_ok() && total > 10);
    for stop_at in 1..=total {
        let mut calls = 0;
        let result = dag.validate_with_unit_premises_and_limits_and_cancellation_work(
            &units,
            &limits,
            &mut || {
                calls += 1;
                // A later invocation would return true; no such invocation is
                // permitted after this one refusal.
                calls != stop_at
            },
        );
        assert_eq!(result, Err(ResolutionValidationError::Cancelled));
        assert_eq!(calls, stop_at, "refusal {stop_at}/{total} is terminal");
    }
    assert_eq!(dag, fixture(4_096));
    assert_eq!(units, [n(0), n(1)]);
    assert_eq!(measured(&dag, &units, &limits), (expected, total));
}

#[test]
fn an_expired_original_deadline_refuses_without_calling_caller_code() {
    let dag = fixture(2);
    let limits = ResolutionValidationLimits {
        deadline: Some(Instant::now()),
        ..ResolutionValidationLimits::default()
    };
    assert_eq!(
        measured(&dag, &[n(0), n(1)], &limits),
        (Err(ResolutionValidationError::DeadlineExceeded), 0),
    );
}

#[test]
fn accepting_final_callback_cannot_overstay_the_original_absolute_deadline() {
    let dag = fixture(2);
    let units = [n(0), n(1)];
    let (_, total) = measured(&dag, &units, &ResolutionValidationLimits::default());
    let deadline = Instant::now() + Duration::from_secs(1);
    let limits = ResolutionValidationLimits {
        deadline: Some(deadline),
        ..ResolutionValidationLimits::default()
    };
    let mut calls = 0;
    let result = dag.validate_with_unit_premises_and_limits_and_cancellation_work(
        &units,
        &limits,
        &mut || {
            calls += 1;
            if calls == total {
                while Instant::now() < deadline {
                    std::thread::yield_now();
                }
            }
            true
        },
    );
    assert_eq!(result, Err(ResolutionValidationError::DeadlineExceeded));
    assert_eq!(calls, total);
}

#[test]
fn reached_malformed_proof_error_does_not_trigger_a_cleanup_success_poll() {
    let mut dag = fixture(2);
    dag.derived[0].rup_hints = vec![u64::MAX];
    let units = [n(0), n(1)];
    let limits = ResolutionValidationLimits::default();
    let mut private_calls = 0;
    let expected = dag.validate_with_limits_interruptible(
        &limits,
        &units,
        units.len() * size_of::<Literal>(),
        0,
        &mut || {
            private_calls += 1;
            false
        },
    );
    let (actual, calls) = measured(&dag, &units, &limits);
    assert_eq!(actual, expected);
    assert_eq!(calls, private_calls);
    assert_eq!(
        actual,
        Err(invalid(ResolutionDagValidateError::UnknownHint {
            step: 2,
            hint: u64::MAX,
        })),
    );
}

#[test]
fn public_replay_reports_private_deterministic_work_not_admission_poll_count() {
    for num_vars in [2, 4_096] {
        let dag = fixture(num_vars);
        let units = [n(0), n(1)];
        let limits = ResolutionValidationLimits::default();
        let mut private_calls = 0;
        let expected = dag.validate_with_limits_interruptible(
            &limits,
            &units,
            units.len() * size_of::<Literal>(),
            0,
            &mut || {
                private_calls += 1;
                false
            },
        );
        let (actual, calls) = measured(&dag, &units, &limits);
        assert_eq!(actual, expected);
        assert_eq!(actual, Ok(25 + 5 * (num_vars as u64 - 2)));
        assert_eq!(calls, private_calls + 1);
    }
}

#[test]
fn successful_private_replay_is_refused_at_the_new_post_cleanup_boundary() {
    let dag = fixture(2);
    let units = [n(0), n(1)];
    let limits = ResolutionValidationLimits::default();
    let mut private_calls = 0;
    assert!(dag
        .validate_with_limits_interruptible(
            &limits,
            &units,
            units.len() * size_of::<Literal>(),
            0,
            &mut || {
                private_calls += 1;
                false
            },
        )
        .is_ok());
    let mut calls = 0;
    let result = dag.validate_with_unit_premises_and_limits_and_cancellation_work(
        &units,
        &limits,
        &mut || {
            calls += 1;
            calls <= private_calls
        },
    );
    assert_eq!(result, Err(ResolutionValidationError::Cancelled));
    assert_eq!(calls, private_calls + 1);
}
