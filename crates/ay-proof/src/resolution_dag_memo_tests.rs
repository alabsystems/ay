// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The memo replays a refutation and nothing else.
//!
//! These run on one thread each (the store is thread-local) and reset it first,
//! so a count is a statement about this test and not about the suite's order.

use super::{
    prove_unsat_resolution_dag_memoized, prove_unsat_resolution_dag_memoized_until,
    prove_unsat_resolution_dag_with_limits_and_cancellation_memoized, reset_resolution_dag_memo,
    resolution_dag_is_memoized_by, resolution_dag_memo_counters, resolution_dag_memoized_by,
};
use ay_sat::{Literal, ResolutionDagError, ResolutionProofError, ResolutionProofLimits};
use std::time::{Duration, Instant};

/// `(x) AND (NOT x)` — refuted by unit propagation alone.
fn unsat_pair(var: u32) -> Vec<Vec<Literal>> {
    vec![
        vec![Literal::from_dimacs(var as i32 + 1)],
        vec![Literal::from_dimacs(-(var as i32 + 1))],
    ]
}

fn bounded_limits() -> ResolutionProofLimits {
    ResolutionProofLimits {
        deadline: Some(Instant::now() + Duration::from_secs(30)),
        ..ResolutionProofLimits::default()
    }
}

#[test]
fn a_repeated_refutation_is_served_from_the_memo_and_is_identical() {
    reset_resolution_dag_memo();
    let cnf = unsat_pair(0);

    let first = prove_unsat_resolution_dag_memoized(1, &cnf).expect("UNSAT");
    assert_eq!(
        resolution_dag_memo_counters(),
        (0, 1),
        "first ask is a miss"
    );

    let second = prove_unsat_resolution_dag_memoized(1, &cnf).expect("UNSAT");
    assert_eq!(
        resolution_dag_memo_counters(),
        (1, 1),
        "second ask is a hit"
    );

    // The point of the memo: the replayed certificate IS the derived one, so a
    // consumer that prints it cannot tell which ask produced it.
    assert_eq!(first, second);
}

#[test]
fn a_different_cnf_is_a_different_key() {
    reset_resolution_dag_memo();
    prove_unsat_resolution_dag_memoized(1, &unsat_pair(0)).expect("UNSAT");
    prove_unsat_resolution_dag_memoized(2, &unsat_pair(1)).expect("UNSAT");
    assert_eq!(
        resolution_dag_memo_counters(),
        (0, 2),
        "two distinct formulas must both derive"
    );
}

#[test]
fn a_satisfiable_formula_is_never_cached() {
    reset_resolution_dag_memo();
    let sat = vec![vec![Literal::from_dimacs(1)]];

    assert!(prove_unsat_resolution_dag_memoized(1, &sat).is_err());
    assert!(prove_unsat_resolution_dag_memoized(1, &sat).is_err());

    // Two misses, no hit: a failure is re-derived every time, so nothing about
    // a refusal is made sticky.
    assert_eq!(resolution_dag_memo_counters(), (0, 2));
}

#[test]
fn the_bounded_and_ungated_entry_points_do_not_share_a_key() {
    reset_resolution_dag_memo();
    let cnf = unsat_pair(0);
    let limits = bounded_limits();

    prove_unsat_resolution_dag_memoized(1, &cnf).expect("UNSAT");
    prove_unsat_resolution_dag_with_limits_and_cancellation_memoized(1, &cnf, &limits, &mut || {
        true
    })
    .expect("UNSAT");
    assert_eq!(
        resolution_dag_memo_counters(),
        (0, 2),
        "a bounded ask may not be answered by an unbounded refutation"
    );

    prove_unsat_resolution_dag_with_limits_and_cancellation_memoized(1, &cnf, &limits, &mut || {
        true
    })
    .expect("UNSAT");
    assert_eq!(resolution_dag_memo_counters().0, 1, "bounded repeat hits");
}

#[test]
fn a_tighter_bound_is_a_different_key() {
    reset_resolution_dag_memo();
    let cnf = unsat_pair(0);
    let loose = bounded_limits();
    let tight = ResolutionProofLimits {
        max_derived_steps: 4,
        ..bounded_limits()
    };

    prove_unsat_resolution_dag_with_limits_and_cancellation_memoized(1, &cnf, &loose, &mut || true)
        .expect("UNSAT");
    let _ = prove_unsat_resolution_dag_with_limits_and_cancellation_memoized(
        1,
        &cnf,
        &tight,
        &mut || true,
    );
    assert_eq!(
        resolution_dag_memo_counters(),
        (0, 2),
        "a resource bound is part of the key, so a looser run cannot answer a tighter ask"
    );
}

#[test]
fn only_the_deadline_is_dropped_from_the_key() {
    reset_resolution_dag_memo();
    let cnf = unsat_pair(0);

    prove_unsat_resolution_dag_with_limits_and_cancellation_memoized(
        1,
        &cnf,
        &ResolutionProofLimits {
            deadline: Some(Instant::now() + Duration::from_secs(30)),
            ..ResolutionProofLimits::default()
        },
        &mut || true,
    )
    .expect("UNSAT");

    // A different wall-clock deadline, everything else identical. This is the
    // one deliberate inexactness, and it runs in the honest direction: the
    // same input already produced this refutation.
    prove_unsat_resolution_dag_with_limits_and_cancellation_memoized(
        1,
        &cnf,
        &ResolutionProofLimits {
            deadline: Some(Instant::now() + Duration::from_secs(600)),
            ..ResolutionProofLimits::default()
        },
        &mut || true,
    )
    .expect("UNSAT");

    assert_eq!(resolution_dag_memo_counters(), (1, 1));
}

#[test]
fn a_cancelled_caller_is_refused_even_on_a_hit() {
    reset_resolution_dag_memo();
    let cnf = unsat_pair(0);
    let limits = bounded_limits();

    prove_unsat_resolution_dag_with_limits_and_cancellation_memoized(1, &cnf, &limits, &mut || {
        true
    })
    .expect("UNSAT");

    let refused = prove_unsat_resolution_dag_with_limits_and_cancellation_memoized(
        1,
        &cnf,
        &limits,
        &mut || false,
    );
    assert!(
        matches!(refused, Err(ResolutionProofError::Cancelled)),
        "a stopping caller must observe a cancellation, never a replayed refutation"
    );
}

/// The polled monolithic refutation is keyed as the unpolled one: the stop
/// only polls, so a refutation it lets finish is the same one. A stop is
/// never stored, and a caller that has stopped is refused even on a hit.
#[test]
fn a_polled_refutation_shares_the_key_and_a_stop_is_never_served() {
    reset_resolution_dag_memo();
    let cnf = unsat_pair(0);

    let stopped = prove_unsat_resolution_dag_memoized_until(1, &cnf, &|| true);
    assert_eq!(stopped, Err(ResolutionDagError::Unknown));
    assert_eq!(
        resolution_dag_memo_counters(),
        (0, 1),
        "a stop stores nothing"
    );

    let polled = prove_unsat_resolution_dag_memoized_until(1, &cnf, &|| false).expect("UNSAT");
    assert_eq!(resolution_dag_memo_counters(), (0, 2));
    let unpolled = prove_unsat_resolution_dag_memoized(1, &cnf).expect("UNSAT");
    assert_eq!(
        resolution_dag_memo_counters(),
        (1, 2),
        "the unpolled ask is served the polled refutation"
    );
    assert_eq!(polled, unpolled);

    let refused = prove_unsat_resolution_dag_memoized_until(1, &cnf, &|| true);
    assert_eq!(
        refused,
        Err(ResolutionDagError::Unknown),
        "a stopped caller must observe the stop, never a replayed refutation"
    );
}

/// The peek answers whether THIS strategy's refutation of THIS CNF is
/// retained, derives nothing and counts nothing.
#[test]
fn a_peek_sees_only_a_retained_strategy_and_counts_nothing() {
    reset_resolution_dag_memo();
    let cnf = unsat_pair(0);
    assert!(!resolution_dag_is_memoized_by(1, &cnf, "sweep"));
    let derived = prove_unsat_resolution_dag_memoized(1, &cnf).expect("UNSAT");
    assert!(
        !resolution_dag_is_memoized_by(1, &cnf, "sweep"),
        "the SAT entry point's entry is not a strategy's"
    );
    assert!(resolution_dag_memoized_by(1, &cnf, "sweep", || Some(derived)).is_some());
    assert!(resolution_dag_is_memoized_by(1, &cnf, "sweep"));
    assert!(!resolution_dag_is_memoized_by(1, &cnf, "direct"));
    assert!(!resolution_dag_is_memoized_by(2, &unsat_pair(1), "sweep"));
    assert_eq!(
        resolution_dag_memo_counters(),
        (0, 2),
        "one miss per derivation"
    );
}
