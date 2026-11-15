// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::literal::Variable;

mod controls;
mod limits;

fn p(index: usize) -> Literal {
    Literal::positive(Variable::new(index as u32))
}

fn n(index: usize) -> Literal {
    Literal::negative(Variable::new(index as u32))
}

fn fixture(num_vars: usize) -> ResolutionDag {
    ResolutionDag {
        num_vars,
        original_clauses: vec![(1, vec![p(0), p(1)])],
        derived: vec![RupStep {
            id: 2,
            clause: vec![],
            rup_hints: vec![1],
        }],
        empty_clause_id: 2,
    }
}

fn base_fixture() -> ResolutionDag {
    ResolutionDag {
        num_vars: 2,
        original_clauses: vec![(1, vec![p(0)]), (2, vec![n(0)])],
        derived: vec![RupStep {
            id: 3,
            clause: vec![],
            rup_hints: vec![1, 2],
        }],
        empty_clause_id: 3,
    }
}

fn measured(
    dag: &ResolutionDag,
    units: &[Literal],
    limits: &ResolutionValidationLimits,
) -> (Result<u64, ResolutionValidationError>, usize) {
    let mut calls = 0;
    let result = dag.validate_with_unit_premises_and_limits_and_cancellation_work(
        units,
        limits,
        &mut || {
            calls += 1;
            true
        },
    );
    (result, calls)
}

fn invalid(error: ResolutionDagValidateError) -> ResolutionValidationError {
    ResolutionValidationError::Invalid(error)
}

#[test]
fn premise_dependent_refutation_replays_without_search_but_plain_replay_refuses() {
    let dag = fixture(2);
    let units = [n(0), n(1)];
    let limits = ResolutionValidationLimits::default();
    assert_eq!(
        dag.validate_with_limits(&limits),
        Err(invalid(ResolutionDagValidateError::HintNotUnit {
            step: 2,
            hint: 1,
        })),
    );
    assert_eq!(measured(&dag, &units, &limits).0, Ok(25));
    assert_eq!(dag, fixture(2));
    assert_eq!(units, [n(0), n(1)]);
}

#[test]
fn dropped_flipped_and_empty_units_do_not_validate_the_same_refutation() {
    let dag = fixture(2);
    let limits = ResolutionValidationLimits::default();
    for units in [vec![n(0)], vec![n(0), p(1)], vec![p(0), n(1)], vec![]] {
        assert!(matches!(
            measured(&dag, &units, &limits).0,
            Err(ResolutionValidationError::Invalid(_)),
        ));
    }
}

#[test]
fn duplicate_and_permuted_units_keep_their_logical_semantics() {
    let dag = fixture(2);
    let limits = ResolutionValidationLimits::default();
    assert_eq!(measured(&dag, &[n(0), n(1)], &limits).0, Ok(25));
    assert_eq!(measured(&dag, &[n(1), n(0)], &limits).0, Ok(25));
    assert_eq!(measured(&dag, &[n(0), n(1), n(1)], &limits).0, Ok(26));
    // This API does not authenticate authored order. Equal replay work and
    // logical results do not grant interchangeable query-source authority.
}

#[test]
fn opposite_units_are_explicitly_inconsistent_premises_not_base_unsat() {
    let dag = ResolutionDag {
        num_vars: 1,
        original_clauses: vec![],
        derived: vec![RupStep {
            id: 1,
            clause: vec![],
            rup_hints: vec![],
        }],
        empty_clause_id: 1,
    };
    let limits = ResolutionValidationLimits::default();
    assert!(dag.validate_with_limits(&limits).is_err());
    assert!(measured(&dag, &[p(0), n(0)], &limits).0.is_ok());
    assert!(measured(&dag, &[p(0)], &limits).0.is_err());
}

#[test]
fn out_of_range_units_refuse_before_indexing_assignment_scratch() {
    let dag = fixture(2);
    for units in [vec![n(0), n(2)], vec![p(0), n(0), n(2)]] {
        assert_eq!(
            measured(&dag, &units, &ResolutionValidationLimits::default()).0,
            Err(invalid(ResolutionDagValidateError::VarOutOfRange {
                clause: 0,
                var: 2,
                num_vars: 2,
            })),
        );
    }
}

#[test]
fn fixed_units_survive_every_derived_row_and_target_trail_reset() {
    let dag = ResolutionDag {
        num_vars: 2,
        original_clauses: vec![(1, vec![p(0), p(1)])],
        derived: vec![
            RupStep {
                id: 2,
                clause: vec![p(1)],
                rup_hints: vec![1],
            },
            RupStep {
                id: 3,
                clause: vec![],
                rup_hints: vec![2],
            },
        ],
        empty_clause_id: 3,
    };
    let limits = ResolutionValidationLimits::default();
    assert!(measured(&dag, &[n(0), n(1)], &limits).0.is_ok());
    assert!(measured(&dag, &[n(0)], &limits).0.is_err());
    assert!(dag.validate_with_limits(&limits).is_err());
}

#[test]
fn inconsistent_units_do_not_remove_structural_terminal_checks() {
    let limits = ResolutionValidationLimits::default();
    let mut dag = fixture(2);
    dag.empty_clause_id = 99;
    assert_eq!(
        measured(&dag, &[p(0), n(0)], &limits).0,
        Err(invalid(ResolutionDagValidateError::EmptyClauseIdMismatch {
            recorded: 99,
            actual: 2,
        })),
    );
    dag.empty_clause_id = 2;
    dag.derived[0].clause = vec![p(1)];
    assert_eq!(
        measured(&dag, &[p(0), n(0)], &limits).0,
        Err(invalid(ResolutionDagValidateError::FinalClauseNotEmpty {
            len: 1
        })),
    );
}

#[test]
fn empty_unit_public_api_preserves_plain_work_and_adds_only_cleanup_admission() {
    let dag = base_fixture();
    let limits = ResolutionValidationLimits::default();
    let mut plain_calls = 0;
    let plain = dag.validate_with_limits_and_cancellation_work(&limits, &mut || {
        plain_calls += 1;
        true
    });
    let (premised, premise_calls) = measured(&dag, &[], &limits);
    assert_eq!(premised, plain);
    assert_eq!(premise_calls, plain_calls + 1);
}
