// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_producer_callback_including_post_cleanup_refuses_without_report() {
    for clauses in [grid(), vec![vec![Literal::from_dimacs(1)]]] {
        let (expected, total) = reported(2, &clauses, &limits());
        assert!(total > 10 && total < 5_000);
        for stop_at in 1..=total {
            let limits = limits();
            let mut calls = 0;
            assert_eq!(
                prove_unsat_resolution_dag_with_limits_and_cancellation_work(
                    2,
                    &clauses,
                    &limits,
                    &mut || {
                        calls += 1;
                        calls != stop_at
                    }
                ),
                Err(ResolutionProofError::Cancelled),
                "callback {stop_at}/{total}"
            );
            assert_eq!(calls, stop_at);
        }
        assert_eq!(reported(2, &clauses, &limits()), (expected, total));
    }
}

#[test]
fn precancel_keeps_precedence_over_missing_deadline_invalid_source_and_sat() {
    for (num_vars, clauses, limits) in [
        (0, vec![], limits()),
        (0, vec![vec![]], limits()),
        (1, vec![vec![Literal::from_dimacs(3)]], limits()),
        (0, vec![], ResolutionProofLimits::default()),
    ] {
        let mut calls = 0;
        assert_eq!(
            prove_unsat_resolution_dag_with_limits_and_cancellation_work(
                num_vars,
                &clauses,
                &limits,
                &mut || {
                    calls += 1;
                    false
                }
            ),
            Err(ResolutionProofError::Cancelled)
        );
        assert_eq!(calls, 1);
    }
}

#[test]
fn earliest_validation_deadline_refuses_proof_but_does_not_reclassify_sat() {
    let mut limits = limits();
    limits.validation.deadline = Some(Instant::now());
    assert_eq!(
        reported(2, &grid(), &limits).0,
        Err(ResolutionProofError::DeadlineExceeded {
            phase: ResolutionProofPhase::Validate,
        })
    );
    let clauses = [vec![Literal::from_dimacs(1)]];
    assert_eq!(
        reported(1, &clauses, &limits).0,
        Err(ResolutionProofError::Satisfiable)
    );
    assert_eq!(
        solve_resolution_dag_with_limits(1, &clauses, &limits),
        Ok(ResolutionSolveOutcome::Sat(vec![true]))
    );
}

#[test]
fn reached_producer_error_does_not_poll_again_or_publish_usage() {
    let clauses = [vec![Literal::from_dimacs(1), Literal::from_dimacs(1)]];
    let limits = limits();
    let (expected, reached) = reported(1, &clauses, &limits);
    assert!(matches!(
        expected,
        Err(ResolutionProofError::DuplicateInputLiteral { .. })
    ));
    let mut calls = 0;
    assert_eq!(
        prove_unsat_resolution_dag_with_limits_and_cancellation_work(
            1,
            &clauses,
            &limits,
            &mut || {
                calls += 1;
                calls <= reached
            }
        ),
        expected
    );
    assert_eq!(calls, reached);
}

/// Pigeonhole: `holes + 1` pigeons, each in some hole, no two in one.
fn pigeonhole(holes: i32) -> (usize, Vec<Vec<Literal>>) {
    let var = |pigeon: i32, hole: i32| pigeon * holes + hole + 1;
    let mut clauses: Vec<Vec<Literal>> = (0..=holes)
        .map(|pigeon| {
            (0..holes)
                .map(|hole| Literal::from_dimacs(var(pigeon, hole)))
                .collect()
        })
        .collect();
    for hole in 0..holes {
        for first in 0..=holes {
            for second in first + 1..=holes {
                clauses.push(vec![
                    Literal::from_dimacs(-var(first, hole)),
                    Literal::from_dimacs(-var(second, hole)),
                ]);
            }
        }
    }
    let vars = usize::try_from((holes + 1) * holes).unwrap();
    (vars, clauses)
}

/// The counted producer is the work-reporting producer plus the conflicts
/// the solve spent, on every outcome: a refutation, a stop on the conflict
/// cap, and a stop on the proof output cap, which still reports the search it
/// ran (the strict checker's sweep is charged that search).
#[test]
fn counted_producer_reports_the_conflicts_of_every_outcome() {
    let (vars, clauses) = pigeonhole(4);
    let mut output_capped = limits();
    output_capped.max_proof_output_bytes = 256;
    let mut conflict_capped = limits();
    conflict_capped.max_conflicts = Some(3);
    for (limits, stop) in [
        (limits(), None),
        (
            output_capped,
            Some(ResolutionProofResource::ProofOutputBytes),
        ),
        (conflict_capped, Some(ResolutionProofResource::Conflicts)),
    ] {
        let mut reference_calls = 0;
        let reference = prove_unsat_resolution_dag_with_limits_and_cancellation_work(
            vars,
            &clauses,
            &limits,
            &mut || {
                reference_calls += 1;
                true
            },
        );
        let mut counted_calls = 0;
        let (proved, conflicts) =
            crate::prove_unsat_resolution_dag_counted_work(vars, &clauses, &limits, &mut || {
                counted_calls += 1;
                true
            });
        assert_eq!(counted_calls, reference_calls);
        assert_eq!(proved, reference);
        let (_, solved) =
            crate::solve_resolution_dag_counted(vars, &clauses, &limits, &mut || true);
        assert_eq!(conflicts, solved);
        match (&proved, stop) {
            (Ok(_), None) => assert!(conflicts > 0),
            (
                Err(ResolutionProofError::LimitExceeded {
                    resource: ResolutionProofResource::ProofOutputBytes,
                    ..
                }),
                Some(ResolutionProofResource::ProofOutputBytes),
            ) => assert!(
                conflicts > 0,
                "a stopped search still reports its conflicts"
            ),
            (
                Err(ResolutionProofError::LimitExceeded {
                    resource: ResolutionProofResource::Conflicts,
                    actual,
                    ..
                }),
                Some(ResolutionProofResource::Conflicts),
            ) => assert_eq!(u128::from(conflicts), *actual),
            (other, _) => panic!("{stop:?}: unexpected outcome {other:?}"),
        }
    }
}

#[test]
fn counted_adapter_keeps_actual_conflicts_and_one_validation_callback_sequence() {
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
    let mut full_calls = 0;
    let full = solve_resolution_dag_with_work(3, &clauses, &limits(), &mut || {
        full_calls += 1;
        true
    })
    .unwrap();
    assert!(matches!(full.0, ResolutionSolveOutcome::Unsat(_)));
    assert!(full.1 > 0);
    let mut short_validation = limits();
    short_validation.validation.max_work = full.1 - 1;
    let mut no_conflicts = limits();
    no_conflicts.max_conflicts = Some(0);
    let mut searched_conflicts = None;
    for (num_vars, input, limits) in [
        (3, clauses.clone(), limits()),
        (3, clauses.clone(), short_validation),
        (3, clauses, no_conflicts),
        (1, vec![vec![Literal::from_dimacs(1)]], limits()),
        (1, vec![vec![Literal::from_dimacs(1); 2]], limits()),
    ] {
        let mut reference_calls = 0;
        let reference = solve_resolution_dag_with_work(num_vars, &input, &limits, &mut || {
            reference_calls += 1;
            true
        });
        let mut counted_calls = 0;
        let (counted, conflicts) =
            crate::solve_resolution_dag_counted(num_vars, &input, &limits, &mut || {
                counted_calls += 1;
                true
            });
        assert_eq!(counted_calls, reference_calls);
        assert_eq!(counted, reference.map(|(outcome, _)| outcome));
        match &counted {
            Ok(ResolutionSolveOutcome::Unsat(_)) => {
                assert_eq!(counted_calls, full_calls);
                assert!(conflicts > 0);
                searched_conflicts = Some(conflicts);
            }
            Err(ResolutionProofError::Validation(_)) => {
                assert_eq!(Some(conflicts), searched_conflicts);
            }
            Err(ResolutionProofError::LimitExceeded {
                resource: ResolutionProofResource::Conflicts,
                actual,
                ..
            }) => assert_eq!(u128::from(conflicts), *actual),
            _ => assert_eq!(conflicts, 0),
        }
    }
    let mut calls = 0;
    let (cancelled, conflicts) =
        crate::solve_resolution_dag_counted(0, &[], &limits(), &mut || {
            calls += 1;
            false
        });
    assert_eq!(cancelled, Err(ResolutionProofError::Cancelled));
    assert_eq!((conflicts, calls), (0, 1));
}
