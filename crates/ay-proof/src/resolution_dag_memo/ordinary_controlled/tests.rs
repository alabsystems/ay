// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn pair() -> Vec<Vec<Literal>> {
    vec![
        vec![Literal::from_dimacs(1)],
        vec![Literal::from_dimacs(-1)],
    ]
}

#[test]
fn controlled_and_compatibility_ordinary_calls_share_only_the_exact_certificate() {
    reset_resolution_dag_memo();
    let cnf = pair();
    let expected = prove_unsat_resolution_dag_memoized(1, &cnf).expect("ordinary proof");
    let actual = prove_unsat_resolution_dag_with_cancellation_memoized(1, &cnf, &mut || true)
        .expect("same ordinary certificate");
    assert_eq!(expected, actual);
    actual.validate().expect("independent RUP replay");
    assert_eq!(resolution_dag_memo_counters(), (1, 1));
}

#[test]
fn initial_refusal_does_not_copy_or_count_a_cached_proof() {
    reset_resolution_dag_memo();
    let cnf = pair();
    prove_unsat_resolution_dag_memoized(1, &cnf).expect("preexisting proof");
    let mut calls = 0;
    let result = prove_unsat_resolution_dag_with_cancellation_memoized(1, &cnf, &mut || {
        calls += 1;
        false
    });
    assert_eq!(result, Err(ResolutionDagCancellationError::Cancelled));
    assert_eq!(calls, 1);
    assert_eq!(resolution_dag_memo_counters(), (0, 1));
}

#[test]
fn every_hit_copy_observation_refuses_without_erasing_valid_prior_work() {
    let cnf = pair();
    for stop in 1..=3 {
        reset_resolution_dag_memo();
        let expected = prove_unsat_resolution_dag_memoized(1, &cnf).expect("preexisting proof");
        let mut calls = 0;
        let result = prove_unsat_resolution_dag_with_cancellation_memoized(1, &cnf, &mut || {
            calls += 1;
            calls != stop
        });
        assert_eq!(result, Err(ResolutionDagCancellationError::Cancelled));
        assert_eq!(calls, stop);
        assert_eq!(
            prove_unsat_resolution_dag_memoized(1, &cnf).expect("prior proof remains"),
            expected
        );
    }
}

#[test]
fn every_cold_observation_refuses_the_result_without_resurrecting_the_owner() {
    reset_resolution_dag_memo();
    let cnf = pair();
    let mut total = 0;
    prove_unsat_resolution_dag_with_cancellation_memoized(1, &cnf, &mut || {
        total += 1;
        true
    })
    .expect("cold proof");
    assert!(total > 3 && total < 20_000);
    for stop in 1..=total {
        reset_resolution_dag_memo();
        let mut calls = 0;
        let result = prove_unsat_resolution_dag_with_cancellation_memoized(1, &cnf, &mut || {
            calls += 1;
            calls != stop
        });
        assert_eq!(
            result,
            Err(ResolutionDagCancellationError::Cancelled),
            "poll {stop}/{total}"
        );
        assert_eq!(calls, stop);
    }
}

#[test]
fn a_cancelled_actual_ordinary_child_is_not_cached() {
    reset_resolution_dag_memo();
    let cnf = pair();
    let mut calls = 0;
    let result = prove_unsat_resolution_dag_with_cancellation_memoized(1, &cnf, &mut || {
        calls += 1;
        calls != 11
    });
    // 3 memo polls + 1 ordinary entry + 1 child entry + 4 copies + 1 pre-solve.
    assert_eq!(result, Err(ResolutionDagCancellationError::Cancelled));
    assert_eq!(calls, 11);
    assert_eq!(resolution_dag_memo_counters(), (0, 1));
    prove_unsat_resolution_dag_memoized(1, &cnf).expect("fresh retry after refused call");
    assert_eq!(resolution_dag_memo_counters(), (0, 2));
}

#[test]
fn post_retention_refusal_publishes_no_result_but_preserves_a_valid_certificate() {
    reset_resolution_dag_memo();
    let cnf = pair();
    let mut total = 0;
    let expected = prove_unsat_resolution_dag_with_cancellation_memoized(1, &cnf, &mut || {
        total += 1;
        true
    })
    .expect("fresh proof");
    reset_resolution_dag_memo();
    let mut calls = 0;
    let result = prove_unsat_resolution_dag_with_cancellation_memoized(1, &cnf, &mut || {
        calls += 1;
        calls != total
    });
    assert_eq!(result, Err(ResolutionDagCancellationError::Cancelled));
    assert_eq!(calls, total);
    let retained =
        prove_unsat_resolution_dag_memoized(1, &cnf).expect("certificate, not a refusal verdict");
    assert_eq!(retained, expected);
    retained
        .validate()
        .expect("independent replay of exact retained certificate");
    assert_eq!(resolution_dag_memo_counters(), (1, 1));
}
