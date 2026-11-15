// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
enum ReplayEntry {
    Public,
    Private,
}

fn boundary_replay(
    dag: &ResolutionDag,
    units: &[Literal],
    limits: &ResolutionValidationLimits,
    entry: ReplayEntry,
) -> Result<u64, ResolutionValidationError> {
    match entry {
        ReplayEntry::Public => measured(dag, units, limits).0,
        ReplayEntry::Private => {
            dag.validate_with_limits_interruptible(limits, units, 0, 0, &mut || false)
        }
    }
}

fn byte_boundary(dag: &ResolutionDag, units: &[Literal], entry: ReplayEntry) -> usize {
    let mut low = 0;
    let mut high = 4_096;
    while low < high {
        let cap = low + (high - low) / 2;
        let limits = ResolutionValidationLimits {
            max_bytes: cap,
            ..ResolutionValidationLimits::default()
        };
        let result = boundary_replay(dag, units, &limits, entry);
        if result.is_ok() {
            high = cap;
        } else {
            assert!(matches!(
                result,
                Err(ResolutionValidationError::LimitExceeded {
                    resource: ResolutionValidationResource::Bytes,
                    ..
                }),
            ));
            low = cap + 1;
        }
    }
    let limits = ResolutionValidationLimits {
        max_bytes: high,
        ..ResolutionValidationLimits::default()
    };
    let result = boundary_replay(dag, units, &limits, entry);
    assert!(
        result.is_ok(),
        "boundary must actually admit the complete replay"
    );
    high
}

#[test]
fn exact_unit_payload_bytes_are_not_an_unaccounted_public_argument() {
    let dag = fixture(2);
    let units = [n(0), n(1)];
    let internal = byte_boundary(&dag, &units, ReplayEntry::Private);
    let public = byte_boundary(&dag, &units, ReplayEntry::Public);
    assert_eq!(public, internal + units.len() * size_of::<Literal>());
    for cap in [public, public - 1, 0] {
        let limits = ResolutionValidationLimits {
            max_bytes: cap,
            ..ResolutionValidationLimits::default()
        };
        let result = measured(&dag, &units, &limits).0;
        if cap == public {
            assert_eq!(result, Ok(25));
        } else {
            assert!(matches!(
                result,
                Err(ResolutionValidationError::LimitExceeded {
                    resource: ResolutionValidationResource::Bytes,
                    ..
                }),
            ));
        }
    }
}

#[test]
fn original_clause_and_literal_limits_include_every_unit_occurrence() {
    let dag = fixture(2);
    let units = [n(0), n(1)];
    let admitted = ResolutionValidationLimits {
        max_original_clauses: 3,
        max_original_literals: 4,
        ..ResolutionValidationLimits::default()
    };
    assert_eq!(measured(&dag, &units, &admitted).0, Ok(25));
    for (resource, limits) in [
        (
            ResolutionValidationResource::OriginalClauses,
            ResolutionValidationLimits {
                max_original_clauses: 2,
                ..admitted.clone()
            },
        ),
        (
            ResolutionValidationResource::OriginalLiterals,
            ResolutionValidationLimits {
                max_original_literals: 3,
                ..admitted.clone()
            },
        ),
    ] {
        assert!(matches!(
            measured(&dag, &units, &limits).0,
            Err(ResolutionValidationError::LimitExceeded { resource: actual, .. })
                if actual == resource,
        ));
    }
    let duplicated = [n(0), n(1), n(1)];
    assert!(measured(&dag, &duplicated, &admitted).0.is_err());
    let limits = ResolutionValidationLimits {
        max_original_clauses: 4,
        max_original_literals: 5,
        ..admitted
    };
    assert_eq!(measured(&dag, &duplicated, &limits).0, Ok(26));
}

#[test]
fn derived_row_literal_and_hint_limits_are_not_widened_for_unit_replay() {
    let mut dag = fixture(2);
    let units = [n(0), n(1)];
    let limits = ResolutionValidationLimits::default();
    for (resource, bounded) in [
        (
            ResolutionValidationResource::DerivedSteps,
            ResolutionValidationLimits {
                max_derived_steps: 0,
                ..limits.clone()
            },
        ),
        (
            ResolutionValidationResource::Hints,
            ResolutionValidationLimits {
                max_hints: 0,
                ..limits.clone()
            },
        ),
    ] {
        assert!(matches!(
            measured(&dag, &units, &bounded).0,
            Err(ResolutionValidationError::LimitExceeded { resource: actual, .. })
                if actual == resource,
        ));
    }
    dag.derived.insert(
        0,
        RupStep {
            id: 2,
            clause: vec![p(1)],
            rup_hints: vec![1],
        },
    );
    dag.derived[1].id = 3;
    dag.empty_clause_id = 3;
    let bounded = ResolutionValidationLimits {
        max_derived_literals: 0,
        ..limits
    };
    assert!(matches!(
        measured(&dag, &units, &bounded).0,
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::DerivedLiterals,
            ..
        }),
    ));
}

#[test]
fn exact_one_short_and_zero_work_fail_without_a_usage_report() {
    let dag = fixture(2);
    let units = [n(0), n(1)];
    for cap in [25, 24, 0] {
        let limits = ResolutionValidationLimits {
            max_work: cap,
            ..ResolutionValidationLimits::default()
        };
        let result = measured(&dag, &units, &limits).0;
        if cap == 25 {
            assert_eq!(result, Ok(25));
        } else {
            assert_eq!(
                result,
                Err(ResolutionValidationError::LimitExceeded {
                    resource: ResolutionValidationResource::Work,
                    limit: u128::from(cap),
                    actual: u128::from(cap + 1),
                }),
            );
        }
    }
}

#[test]
fn namespace_scratch_initialization_is_charged_even_for_a_small_proof() {
    let dag = fixture(65_536);
    let limits = ResolutionValidationLimits {
        max_work: 128,
        ..ResolutionValidationLimits::default()
    };
    assert!(matches!(
        measured(&dag, &[n(0), n(1)], &limits).0,
        Err(ResolutionValidationError::LimitExceeded {
            resource: ResolutionValidationResource::Work,
            limit: 128,
            ..
        }),
    ));
}

#[test]
fn returned_work_can_continue_one_shared_grant_without_a_new_initial_work_api() {
    let dag = fixture(2);
    let units = [n(0), n(1)];
    for total in [50, 49] {
        let mut limits = ResolutionValidationLimits {
            max_work: total,
            ..ResolutionValidationLimits::default()
        };
        let first = measured(&dag, &units, &limits).0.unwrap();
        assert_eq!(first, 25);
        limits.max_work = limits.max_work.checked_sub(first).unwrap();
        let second = measured(&dag, &units, &limits).0;
        if total == 50 {
            assert_eq!(second, Ok(25));
            limits.max_work = limits.max_work.checked_sub(second.unwrap()).unwrap();
            assert_eq!(limits.max_work, 0);
            assert!(measured(&dag, &units, &limits).0.is_err());
        } else {
            assert!(matches!(
                second,
                Err(ResolutionValidationError::LimitExceeded {
                    resource: ResolutionValidationResource::Work,
                    limit: 24,
                    actual: 25,
                }),
            ));
        }
    }
}
