// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use std::cell::Cell;
use std::rc::Rc;

fn grid() -> Vec<Vec<Literal>> {
    vec![
        vec![positive(0), positive(1)],
        vec![negative(0), positive(1)],
        vec![positive(0), negative(1)],
        vec![negative(0), negative(1)],
    ]
}

#[test]
fn legacy_and_live_control_preserve_checked_sat_and_exact_unsat_dag() {
    for clauses in [vec![vec![positive(0)]], grid()] {
        let limits = limits();
        let expected = solve_resolution_dag_with_limits(2, &clauses, &limits).unwrap();
        // Rc is intentionally !Send: the caller-owned callback is never sent
        // to a worker or retained by the erased Send+'static proof writer.
        let calls = Rc::new(Cell::new(0usize));
        let actual =
            solve_resolution_dag_with_limits_and_cancellation(2, &clauses, &limits, &mut || {
                calls.set(calls.get() + 1);
                true
            })
            .unwrap();
        assert!(calls.get() > 5);
        assert_eq!(actual, expected);
        if let ResolutionSolveOutcome::Unsat(dag) = actual {
            assert_eq!(dag.validate(), Ok(()));
            assert_eq!(
                dag.original_clauses
                    .iter()
                    .map(|(_, clause)| clause.clone())
                    .collect::<Vec<_>>(),
                clauses
            );
        }
    }
}

#[test]
fn each_public_producer_callback_is_terminal_including_active_solve_and_final_admission() {
    for clauses in [vec![vec![positive(0)]], grid()] {
        let limits = limits();
        let mut total = 0;
        let expected =
            solve_resolution_dag_with_limits_and_cancellation(2, &clauses, &limits, &mut || {
                total += 1;
                true
            })
            .unwrap();
        assert!(
            total > 10 && total < 5_000,
            "bounded fixture callbacks: {total}"
        );
        for stop in 1..=total {
            let mut calls = 0;
            let result = solve_resolution_dag_with_limits_and_cancellation(
                2,
                &clauses,
                &limits,
                &mut || {
                    calls += 1;
                    calls != stop
                },
            );
            assert_eq!(
                result,
                Err(ResolutionProofError::Cancelled),
                "callback {stop}/{total}"
            );
            assert_eq!(calls, stop);
        }
        assert_eq!(
            solve_resolution_dag_with_limits_and_cancellation(2, &clauses, &limits, &mut || true),
            Ok(expected)
        );
    }
}

#[test]
fn precancel_is_typed_even_for_empty_sat_invalid_source_and_missing_deadline() {
    for (num_vars, clauses, limits) in [
        (0, vec![], limits()),
        (0, vec![vec![]], limits()),
        (1, vec![vec![positive(2)]], limits()),
        (0, vec![], ResolutionProofLimits::default()),
    ] {
        let mut calls = 0;
        let result = prove_unsat_resolution_dag_with_limits_and_cancellation(
            num_vars,
            &clauses,
            &limits,
            &mut || {
                calls += 1;
                false
            },
        );
        assert_eq!(result, Err(ResolutionProofError::Cancelled));
        assert_eq!(calls, 1);
    }
}

#[test]
fn live_invalid_input_and_resource_errors_retain_legacy_precedence() {
    let mut codec_zero = limits();
    codec_zero.max_codec_bytes = 0;
    let mut expired = limits();
    expired.deadline = Some(Instant::now());
    for (num_vars, clauses, limits) in [
        (1, vec![vec![positive(0), positive(0)]], limits()),
        (1, vec![vec![positive(2)]], limits()),
        (0, vec![], ResolutionProofLimits::default()),
        (1, vec![vec![positive(0)]], codec_zero),
        (1, vec![vec![positive(0)]], expired),
    ] {
        let expected = solve_resolution_dag_with_limits(num_vars, &clauses, &limits).unwrap_err();
        let actual = solve_resolution_dag_with_limits_and_cancellation(
            num_vars,
            &clauses,
            &limits,
            &mut || true,
        )
        .unwrap_err();
        assert_eq!(actual, expected);
    }
    assert_eq!(
        prove_unsat_resolution_dag_with_limits_and_cancellation(
            1,
            &[vec![positive(0)]],
            &limits(),
            &mut || true
        ),
        Err(ResolutionProofError::Satisfiable)
    );
}
