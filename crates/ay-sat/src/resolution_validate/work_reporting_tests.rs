// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn fixture(num_vars: usize) -> ResolutionDag {
    ResolutionDag {
        num_vars,
        original_clauses: vec![
            (1, vec![Literal::from_dimacs(1), Literal::from_dimacs(2)]),
            (2, vec![Literal::from_dimacs(-1)]),
            (3, vec![Literal::from_dimacs(-2)]),
        ],
        derived: vec![RupStep {
            id: 4,
            clause: vec![],
            rup_hints: vec![1, 2, 3],
        }],
        empty_clause_id: 4,
    }
}

fn measured(
    dag: &ResolutionDag,
    limits: &ResolutionValidationLimits,
) -> (Result<u64, ResolutionValidationError>, usize) {
    let mut polls = 0;
    let result = dag.validate_with_limits_and_cancellation_work(limits, &mut || {
        polls += 1;
        true
    });
    (result, polls)
}

#[test]
fn reported_work_is_the_existing_debit_sum_not_callback_count() {
    let limits = ResolutionValidationLimits::default();
    for num_vars in [2, 4_096] {
        // Four row censuses, eight reserved DB buckets, three namespace
        // initialization/reservation debits, seven original row/literal visits,
        // one derived row, ten fixpoint hint/literal visits, two trail resets.
        let expected = 4 + 8 + 3 * num_vars as u64 + 7 + 1 + 10 + 2;
        let dag = fixture(num_vars);
        let (result, polls) = measured(&dag, &limits);
        assert_eq!(result, Ok(expected));
        assert!(polls > 1 && (polls as u64) < expected);
        let mut internal_polls = 0;
        assert_eq!(
            dag.validate_with_limits_interruptible(&limits, &[], 0, 0, &mut || {
                internal_polls += 1;
                false
            }),
            result
        );
        assert_eq!(internal_polls, polls);
        assert_eq!(dag, fixture(num_vars));
    }
}

#[test]
fn exact_one_short_and_zero_work_preserve_legacy_errors_and_polls() {
    let dag = fixture(2);
    for cap in [38, 37, 0] {
        let limits = ResolutionValidationLimits {
            max_work: cap,
            ..ResolutionValidationLimits::default()
        };
        let (reported, polls) = measured(&dag, &limits);
        if cap == 38 {
            assert_eq!(reported, Ok(38));
        } else {
            assert_eq!(
                reported,
                Err(ResolutionValidationError::LimitExceeded {
                    resource: ResolutionValidationResource::Work,
                    limit: u128::from(cap),
                    actual: u128::from(cap + 1),
                })
            );
        }
        let mut legacy_polls = 0;
        assert_eq!(
            dag.validate_with_limits_and_cancellation(&limits, &mut || {
                legacy_polls += 1;
                true
            }),
            reported.clone().map(|_| ())
        );
        assert_eq!(legacy_polls, polls);
        assert_eq!(dag.validate_with_limits(&limits), reported.map(|_| ()));
    }
}

#[test]
fn every_replay_callback_including_final_refuses_without_usage_or_repoll() {
    let dag = fixture(4_096);
    let limits = ResolutionValidationLimits::default();
    let (expected, total) = measured(&dag, &limits);
    assert!(expected.is_ok() && total > 10 && total < 100);
    for stop_at in 1..=total {
        let mut calls = 0;
        assert_eq!(
            dag.validate_with_limits_and_cancellation_work(&limits, &mut || {
                calls += 1;
                calls != stop_at
            }),
            Err(ResolutionValidationError::Cancelled),
            "callback {stop_at}/{total}"
        );
        assert_eq!(calls, stop_at);
        let mut legacy_calls = 0;
        assert_eq!(
            dag.validate_with_limits_and_cancellation(&limits, &mut || {
                legacy_calls += 1;
                legacy_calls != stop_at
            }),
            Err(ResolutionValidationError::Cancelled)
        );
        assert_eq!(legacy_calls, stop_at);
    }
    assert_eq!(measured(&dag, &limits), (expected, total));
}

#[test]
fn reached_invalid_replay_error_never_publishes_work_or_adds_a_poll() {
    let mut dag = fixture(2);
    dag.derived[0].rup_hints = vec![u64::MAX];
    let limits = ResolutionValidationLimits::default();
    let (error, polls) = measured(&dag, &limits);
    assert_eq!(
        error,
        Err(ResolutionValidationError::Invalid(
            ResolutionDagValidateError::UnknownHint {
                step: 4,
                hint: u64::MAX,
            }
        ))
    );
    let mut calls = 0;
    assert_eq!(
        dag.validate_with_limits_and_cancellation_work(&limits, &mut || {
            calls += 1;
            calls <= polls
        }),
        error
    );
    assert_eq!(calls, polls);
    assert_eq!(dag.validate_with_limits(&limits), error.map(|_| ()));
}

#[test]
fn expired_deadline_and_storage_refusal_have_no_success_report() {
    let dag = fixture(2);
    let limits = ResolutionValidationLimits {
        deadline: Some(Instant::now()),
        ..ResolutionValidationLimits::default()
    };
    assert_eq!(
        measured(&dag, &limits),
        (Err(ResolutionValidationError::DeadlineExceeded), 0)
    );
    let limits = ResolutionValidationLimits {
        max_bytes: 0,
        ..ResolutionValidationLimits::default()
    };
    let (reported, _) = measured(&dag, &limits);
    assert!(matches!(
        reported,
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Bytes,
            limit: 0,
            ..
        })
    ));
    assert_eq!(dag.validate_with_limits(&limits), reported.map(|_| ()));
}

#[test]
fn successful_usage_can_be_subtracted_once_from_a_shared_caller_grant() {
    let dag = fixture(2);
    for total in [76, 75] {
        let mut limits = ResolutionValidationLimits {
            max_work: total,
            ..ResolutionValidationLimits::default()
        };
        let first = dag
            .validate_with_limits_and_cancellation_work(&limits, &mut || true)
            .unwrap();
        assert_eq!(first, 38);
        limits.max_work = limits.max_work.checked_sub(first).unwrap();
        let second = dag.validate_with_limits_and_cancellation_work(&limits, &mut || true);
        if total == 76 {
            assert_eq!(second, Ok(38));
        } else {
            assert_eq!(
                second,
                Err(ResolutionValidationError::LimitExceeded {
                    resource: ResolutionValidationResource::Work,
                    limit: 37,
                    actual: 38,
                })
            );
        }
    }
}
