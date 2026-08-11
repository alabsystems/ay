// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Capability-boundary regressions for native term constructors.

use ay_dpll::api::{Logic, Solver, SolverError, Term};

fn assert_invalid_handle(result: Result<Term, SolverError>) {
    assert!(
        matches!(result, Err(SolverError::InvalidTermHandle { .. })),
        "expected an invalid-term-handle error, got {result:?}"
    );
}

#[test]
fn construction_rejects_a_term_owned_by_another_solver() {
    let mut owner = Solver::new(Logic::All);
    let mut foreign_owner = Solver::new(Logic::All);
    let local = owner.int_const(1);
    let foreign = foreign_owner.int_const(2);

    assert_invalid_handle(owner.try_add(local, foreign));
}

#[test]
fn construction_rejects_a_stale_term_after_reset_and_id_reuse() {
    let mut solver = Solver::new(Logic::All);
    let stale = solver.string_const("before-reset");

    solver.try_reset().expect("reset succeeds");
    let current = solver.string_const("after-reset");
    assert_eq!(
        stale.to_raw(),
        current.to_raw(),
        "the regression requires numeric term-ID reuse"
    );

    assert_invalid_handle(solver.try_str_len(stale));
    assert!(solver.try_str_len(current).is_ok());
}

#[test]
fn raw_numeric_round_trip_does_not_reauthenticate_a_term() {
    let mut solver = Solver::new(Logic::All);
    let fp = solver.fp_plus_zero(8, 24);
    let unauthenticated = Term::from_raw(fp.to_raw());

    assert_invalid_handle(solver.try_fp_abs(unauthenticated));
    assert!(solver.try_fp_abs(fp).is_ok());
}
