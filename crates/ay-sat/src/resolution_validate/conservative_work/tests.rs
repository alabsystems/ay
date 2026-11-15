// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{Literal, ResolutionDag, ResolutionDagValidateError, RupStep};
use std::cell::Cell;

fn source(dag: &ResolutionDag) -> ConservativeRupSourceShape {
    ConservativeRupSourceShape {
        num_vars: dag.num_vars,
        original_clauses: dag.original_clauses.len(),
        original_literals: dag.original_clauses.iter().map(|(_, row)| row.len()).sum(),
        max_original_width: dag
            .original_clauses
            .iter()
            .map(|(_, row)| row.len())
            .max()
            .unwrap_or(0),
    }
}

fn price(
    dag: &ResolutionDag,
    limits: &ResolutionValidationLimits,
) -> Result<u64, ResolutionValidationError> {
    conservative_rup_validation_work_bound(
        source(dag),
        dag.derived
            .iter()
            .map(|row| (row.clause.len(), row.rup_hints.len())),
        0,
        limits,
        &mut || true,
    )
}

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

#[test]
fn conservative_price_covers_actual_fixpoint_meter_without_changing_replay() {
    for variables in [2, 4_096] {
        let dag = fixture(variables);
        let snapshot = dag.clone();
        let limits = ResolutionValidationLimits::default();
        let bound = price(&dag, &limits).unwrap();
        let measured = dag
            .validate_with_limits_and_cancellation_work(&limits, &mut || true)
            .unwrap();
        assert!(bound >= measured);
        assert_eq!(measured, 32 + 3 * variables as u64);
        assert_eq!(dag, snapshot);
    }
}

#[test]
fn prior_derived_width_is_used_but_current_row_never_enters_its_own_database() {
    let shape = ConservativeRupSourceShape {
        num_vars: 10,
        original_clauses: 2,
        original_literals: 2,
        max_original_width: 1,
    };
    let limits = ResolutionValidationLimits::default();
    let bound = conservative_rup_validation_work_bound(
        shape,
        [(8, 0), (0, 3)].into_iter(),
        0,
        &limits,
        &mut || true,
    )
    .unwrap();
    // Base40; first row4+16+8=28 (zero hints); second4+3+4*3*9=115.
    assert_eq!(bound, 183);
    let reversed = conservative_rup_validation_work_bound(
        shape,
        [(0, 3), (8, 0)].into_iter(),
        0,
        &limits,
        &mut || true,
    )
    .unwrap();
    assert_eq!(reversed, 99);
}

#[test]
fn exact_bound_and_one_short_are_checked_without_a_new_allowance() {
    let dag = fixture(2);
    let mut limits = ResolutionValidationLimits::default();
    let bound = price(&dag, &limits).unwrap();
    assert_eq!(bound, 55);
    limits.max_work = bound;
    assert_eq!(price(&dag, &limits), Ok(bound));
    limits.max_work = bound - 1;
    assert_eq!(
        price(&dag, &limits),
        Err(ResolutionValidationError::LimitExceeded {
            resource: Resource::Work,
            limit: u128::from(bound - 1),
            actual: u128::from(bound),
        })
    );
}

#[test]
fn every_existing_count_cap_is_enforced_before_success() {
    let dag = fixture(2);
    for resource in [
        Resource::OriginalClauses,
        Resource::OriginalLiterals,
        Resource::DerivedSteps,
        Resource::DerivedLiterals,
        Resource::Hints,
    ] {
        let mut candidate = dag.clone();
        let mut limits = ResolutionValidationLimits::default();
        match resource {
            Resource::OriginalClauses => limits.max_original_clauses = 2,
            Resource::OriginalLiterals => limits.max_original_literals = 3,
            Resource::DerivedSteps => limits.max_derived_steps = 0,
            Resource::DerivedLiterals => {
                candidate.derived[0].clause.push(Literal::from_dimacs(1));
                limits.max_derived_literals = 0;
            }
            Resource::Hints => limits.max_hints = 2,
            _ => unreachable!(),
        }
        assert!(matches!(price(&candidate, &limits),
            Err(ResolutionValidationError::LimitExceeded { resource: found, .. }) if found == resource));
    }
}

#[test]
fn checked_namespace_prefix_and_hint_products_refuse_overflow() {
    let limits = ResolutionValidationLimits::unbounded();
    let empty = ConservativeRupSourceShape {
        num_vars: 0,
        original_clauses: 0,
        original_literals: 0,
        max_original_width: 0,
    };
    let huge_namespace = ConservativeRupSourceShape {
        num_vars: usize::MAX,
        ..empty
    };
    let namespace_price = (usize::MAX as u128) * 3;
    let namespace_expected = u64::try_from(namespace_price).map_err(|_| overflow());
    assert_eq!(
        conservative_rup_validation_work_bound(
            huge_namespace,
            [].into_iter(),
            0,
            &limits,
            &mut || true,
        ),
        namespace_expected
    );
    assert_eq!(
        conservative_rup_validation_work_bound(
            empty,
            [(1, 0)].into_iter(),
            u64::MAX,
            &limits,
            &mut || true,
        ),
        Err(overflow())
    );
    let wide = ConservativeRupSourceShape {
        num_vars: 10,
        max_original_width: usize::MAX,
        ..empty
    };
    assert_eq!(
        conservative_rup_validation_work_bound(
            wide,
            [(0, usize::MAX)].into_iter(),
            0,
            &limits,
            &mut || true,
        ),
        Err(overflow())
    );
}

#[test]
fn original_prefix_is_retained_and_empty_inventory_has_no_semantic_authority() {
    let limits = ResolutionValidationLimits::default();
    let empty = ConservativeRupSourceShape {
        num_vars: 0,
        original_clauses: 0,
        original_literals: 0,
        max_original_width: 0,
    };
    assert_eq!(
        conservative_rup_validation_work_bound(empty, [].into_iter(), 17, &limits, &mut || true,),
        Ok(17)
    );
    let invalid = ResolutionDag {
        num_vars: 0,
        original_clauses: vec![],
        derived: vec![],
        empty_clause_id: 0,
    };
    assert_eq!(price(&invalid, &limits), Ok(0));
    assert_eq!(
        invalid.validate_with_limits(&limits),
        Err(ResolutionValidationError::Invalid(
            ResolutionDagValidateError::NoSteps
        ))
    );
}

#[test]
fn every_control_observation_including_terminal_refuses_before_publication() {
    let dag = fixture(2);
    let limits = ResolutionValidationLimits::default();
    let mut total = 0;
    let healthy = conservative_rup_validation_work_bound(
        source(&dag),
        [(0, 3)].into_iter(),
        0,
        &limits,
        &mut || {
            total += 1;
            true
        },
    );
    assert_eq!(healthy, Ok(55));
    assert_eq!(total, 6);
    for stop_at in 1..=total {
        let mut calls = 0;
        let result = conservative_rup_validation_work_bound(
            source(&dag),
            [(0, 3)].into_iter(),
            0,
            &limits,
            &mut || {
                calls += 1;
                calls != stop_at
            },
        );
        assert_eq!(result, Err(ResolutionValidationError::Cancelled));
        assert_eq!(calls, stop_at);
    }
}

#[test]
fn row_iterator_is_never_advanced_after_refusal_and_is_polled_after_advance() {
    let dag = fixture(2);
    let limits = ResolutionValidationLimits::default();
    let advances = Cell::new(0);
    let rows = std::iter::from_fn(|| {
        advances.set(advances.get() + 1);
        Some((0, 3))
    });
    let mut calls = 0;
    assert_eq!(
        conservative_rup_validation_work_bound(source(&dag), rows, 0, &limits, &mut || {
            calls += 1;
            calls < 2
        },),
        Err(ResolutionValidationError::Cancelled)
    );
    assert_eq!(advances.get(), 0);
    let stopped = Cell::new(false);
    let rows = std::iter::once((0, 3)).inspect(|_| stopped.set(true));
    assert_eq!(
        conservative_rup_validation_work_bound(source(&dag), rows, 0, &limits, &mut || !stopped
            .get(),),
        Err(ResolutionValidationError::Cancelled)
    );
}

#[test]
fn expired_original_absolute_deadline_refuses_before_any_callback() {
    let dag = fixture(2);
    let limits = ResolutionValidationLimits {
        deadline: Some(Instant::now()),
        ..ResolutionValidationLimits::default()
    };
    let mut polls = 0;
    assert_eq!(
        conservative_rup_validation_work_bound(
            source(&dag),
            [(0, 3)].into_iter(),
            0,
            &limits,
            &mut || {
                polls += 1;
                true
            },
        ),
        Err(ResolutionValidationError::DeadlineExceeded)
    );
    assert_eq!(polls, 0);
}

#[test]
fn callback_unwind_does_not_clear_the_callers_sticky_owner() {
    let dag = fixture(2);
    let limits = ResolutionValidationLimits::default();
    let stopped = Cell::new(false);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = conservative_rup_validation_work_bound(
            source(&dag),
            [(0, 3)].into_iter(),
            0,
            &limits,
            &mut || {
                stopped.set(true);
                panic!("original owner callback did not return")
            },
        );
    }));
    assert!(result.is_err());
    assert_eq!(
        conservative_rup_validation_work_bound(
            source(&dag),
            [(0, 3)].into_iter(),
            0,
            &limits,
            &mut || !stopped.get(),
        ),
        Err(ResolutionValidationError::Cancelled)
    );
}
