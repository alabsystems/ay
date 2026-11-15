// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ResolutionValidationResource;
use std::time::Duration;

mod controls;

fn limits() -> ResolutionProofLimits {
    ResolutionProofLimits {
        deadline: Some(Instant::now() + Duration::from_secs(30)),
        ..ResolutionProofLimits::default()
    }
}

fn grid() -> Vec<Vec<Literal>> {
    [[1, 2], [-1, 2], [1, -2], [-1, -2]]
        .into_iter()
        .map(|clause| clause.into_iter().map(Literal::from_dimacs).collect())
        .collect()
}

fn reported(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    limits: &ResolutionProofLimits,
) -> (Result<(ResolutionDag, u64), ResolutionProofError>, usize) {
    let mut calls = 0;
    let result = prove_unsat_resolution_dag_with_limits_and_cancellation_work(
        num_vars,
        clauses,
        limits,
        &mut || {
            calls += 1;
            true
        },
    );
    (result, calls)
}

#[test]
fn producer_usage_equals_one_fresh_replay_on_all_refutation_routes() {
    for (num_vars, clauses) in [
        (2, grid()),
        (
            1,
            vec![
                vec![Literal::from_dimacs(1)],
                vec![Literal::from_dimacs(-1)],
            ],
        ),
        (0, vec![vec![]]),
    ] {
        let limits = limits();
        let (report, calls) = reported(num_vars, &clauses, &limits);
        let (dag, work) = report.unwrap();
        assert!(work > 0);
        let mut replay_limits = limits.validation.clone();
        replay_limits.deadline = earliest_deadline(limits.deadline, replay_limits.deadline);
        assert_eq!(
            dag.validate_with_limits_and_cancellation_work(&replay_limits, &mut || true),
            Ok(work)
        );
        let mut legacy_calls = 0;
        assert_eq!(
            prove_unsat_resolution_dag_with_limits_and_cancellation(
                num_vars,
                &clauses,
                &limits,
                &mut || {
                    legacy_calls += 1;
                    true
                }
            ),
            Ok(dag.clone())
        );
        assert_eq!(legacy_calls, calls);
        assert_eq!(
            prove_unsat_resolution_dag_with_limits(num_vars, &clauses, &limits),
            Ok(dag.clone())
        );
        assert_eq!(
            solve_resolution_dag_with_limits(num_vars, &clauses, &limits),
            Ok(ResolutionSolveOutcome::Unsat(dag))
        );
    }
}

#[test]
fn producer_validation_exact_one_short_and_zero_match_standalone_replay() {
    let clauses = grid();
    let (dag, work) = reported(2, &clauses, &limits()).0.unwrap();
    assert!(work > 1);
    for cap in [work, work - 1, 0] {
        let mut limits = limits();
        limits.validation.max_work = cap;
        let expected = dag
            .validate_with_limits_and_cancellation_work(&limits.validation, &mut || true)
            .map(|used| (dag.clone(), used))
            .map_err(ResolutionProofError::Validation);
        let (actual, calls) = reported(2, &clauses, &limits);
        assert_eq!(actual, expected);
        if cap == work {
            assert_eq!(actual, Ok((dag.clone(), work)));
        } else {
            assert!(matches!(
                actual,
                Err(ResolutionProofError::Validation(
                    ResolutionValidationError::LimitExceeded {
                        resource: ResolutionValidationResource::Work,
                        ..
                    }
                ))
            ));
        }
        let mut legacy_calls = 0;
        assert_eq!(
            prove_unsat_resolution_dag_with_limits_and_cancellation(
                2,
                &clauses,
                &limits,
                &mut || {
                    legacy_calls += 1;
                    true
                }
            ),
            actual.map(|(dag, _)| dag)
        );
        assert_eq!(legacy_calls, calls);
    }
}

#[test]
fn sat_source_and_resource_errors_never_acquire_success_usage() {
    let p = Literal::from_dimacs(1);
    let mut codec_zero = limits();
    codec_zero.max_codec_bytes = 0;
    let mut expired = limits();
    expired.deadline = Some(Instant::now());
    for (num_vars, clauses, limits) in [
        (1, vec![vec![p]], limits()),
        (1, vec![vec![p, p]], limits()),
        (1, vec![vec![Literal::from_dimacs(3)]], limits()),
        (0, vec![], ResolutionProofLimits::default()),
        (1, vec![vec![p]], codec_zero),
        (1, vec![vec![p]], expired),
    ] {
        let (result, calls) = reported(num_vars, &clauses, &limits);
        assert!(result.is_err());
        let mut legacy_calls = 0;
        assert_eq!(
            prove_unsat_resolution_dag_with_limits_and_cancellation(
                num_vars,
                &clauses,
                &limits,
                &mut || {
                    legacy_calls += 1;
                    true
                }
            ),
            result.map(|(dag, _)| dag)
        );
        assert_eq!(legacy_calls, calls);
    }
    assert_eq!(
        reported(1, &[vec![p]], &limits()).0,
        Err(ResolutionProofError::Satisfiable)
    );
}

#[test]
fn exhausted_search_returns_no_report_even_when_validation_grant_is_live() {
    // Every three-variable assignment is blocked. Unlike the binary grid,
    // a first lucky decision cannot learn a root unit without a second
    // decision; this fixture therefore reaches a counted CDCL conflict.
    let clauses: Vec<Vec<Literal>> = (0..8)
        .map(|signs| {
            (0..3)
                .map(|var| {
                    let literal = var + 1;
                    Literal::from_dimacs(if signs & (1 << var) == 0 {
                        literal
                    } else {
                        -literal
                    })
                })
                .collect()
        })
        .collect();
    let mut limits = limits();
    let (dag, work) = reported(3, &clauses, &limits).0.unwrap();
    assert!(work > 0);
    assert_eq!(
        dag.validate_with_limits_and_cancellation_work(&limits.validation, &mut || true),
        Ok(work)
    );
    limits.max_conflicts = Some(0);
    let (actual, _) = reported(3, &clauses, &limits);
    assert_eq!(
        actual,
        Err(ResolutionProofError::LimitExceeded {
            resource: ResolutionProofResource::Conflicts,
            limit: 0,
            actual: 1,
        })
    );
    assert_eq!(
        prove_unsat_resolution_dag_with_limits(3, &clauses, &limits),
        actual.map(|(dag, _)| dag)
    );
}
