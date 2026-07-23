// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native-API isolation tests for solver-generated array-extensionality witnesses.

use crate::api::{Logic, Solver, SolverError, Sort, Term};
use ay_frontend::{Command, Objective, ObjectiveDirection, SoftAssertion};

fn solver_with_active_witness() -> (Solver, Term, Term, Term) {
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = solver.declare_const("a", array_sort.clone());
    let b = solver.declare_const("b", array_sort);
    let arrays_equal = solver.try_eq(a, b).unwrap();
    let arrays_differ = solver.try_not(arrays_equal).unwrap();
    solver.try_assert_term(arrays_differ).unwrap();

    let first = solver.check_sat();
    assert!(
        first.is_sat(),
        "a single array disequality must produce the SAT baseline, got {first:?}"
    );
    let witness = solver
        .executor
        .array_ext_witness_cache
        .pair_witness(solver.executor.terms(), a.0, b.0)
        .expect("array solve should mint an active extensionality witness");
    (solver, a, b, Term::from_raw(witness.0))
}

fn equality_at(solver: &mut Solver, a: Term, b: Term, index: Term) -> Term {
    let select_a = solver.try_select(a, index).unwrap();
    let select_b = solver.try_select(b, index).unwrap();
    solver.try_eq(select_a, select_b).unwrap()
}

#[test]
fn active_witness_cannot_be_registered_as_hard_soft_or_objective_input() {
    let (mut solver, a, b, witness) = solver_with_active_witness();
    let pinned_equal = equality_at(&mut solver, a, b, witness);

    assert!(matches!(
        solver.try_assert_term(pinned_equal),
        Err(SolverError::InvalidArgument {
            operation: "assert_term",
            ..
        })
    ));
    assert!(matches!(
        solver.assert_soft(pinned_equal, 1, None),
        Err(SolverError::InvalidArgument {
            operation: "assert_soft",
            ..
        })
    ));
    assert!(matches!(
        solver.try_minimize(witness),
        Err(SolverError::InvalidArgument {
            operation: "register_objective",
            ..
        })
    ));

    let invalid = Term::from_raw(u32::MAX);
    assert!(matches!(
        solver.try_assert_term(invalid),
        Err(SolverError::InvalidArgument {
            operation: "assert_term",
            ..
        })
    ));
}

#[test]
fn retired_witness_in_assumption_fails_closed_before_solving() {
    let (mut solver, a, b, witness) = solver_with_active_witness();
    let pinned_equal = equality_at(&mut solver, a, b, witness);

    let result = solver.check_sat_assuming(&[pinned_equal]);
    assert!(result.is_unknown(), "captured witness must fail closed");
    assert_eq!(solver.get_reason_unknown().as_deref(), Some("incomplete"));
}

#[test]
fn retired_witness_in_bypassed_permanent_assertion_fails_closed() {
    let (mut solver, a, b, witness) = solver_with_active_witness();
    let pinned_equal = equality_at(&mut solver, a, b, witness);

    // Simulate a replay/adapter that bypassed the immediate native assertion
    // gate. The public solve boundary must independently catch the retired
    // identity in the authored DAG before any theory code indexes it.
    solver
        .executor
        .context_mut()
        .assertions
        .push(pinned_equal.0);

    let result = solver.check_sat();
    assert!(result.is_unknown(), "captured witness must fail closed");
    assert_eq!(solver.get_reason_unknown().as_deref(), Some("incomplete"));
}

#[test]
fn retired_witness_in_bypassed_objective_fails_closed() {
    let (mut solver, _a, _b, witness) = solver_with_active_witness();

    // Simulate an adapter that writes directly to the elaboration context.
    // The executor optimization boundary must still reject the retired
    // solver-owned identity before inspecting its sort or optimizing it.
    solver.executor.context_mut().add_objective(Objective {
        direction: ObjectiveDirection::Minimize,
        term: witness.0,
    });

    let result = solver.optimize_check();
    assert!(result.is_unknown(), "captured objective must fail closed");
    assert_eq!(solver.get_reason_unknown().as_deref(), Some("incomplete"));
}

#[test]
fn retired_witness_in_bypassed_soft_constraint_fails_closed() {
    let (mut solver, a, b, witness) = solver_with_active_witness();
    let pinned_equal = equality_at(&mut solver, a, b, witness);

    // Parsed soft constraints live in the executor context rather than the
    // native API list. Bypass both registration surfaces to exercise the
    // central MaxSMT preflight before it materializes relaxation clauses.
    let displaced = solver
        .executor
        .context_mut()
        .replace_soft_constraints(vec![SoftAssertion {
            term: pinned_equal.0,
            weight: 1,
            id: None,
        }]);
    assert!(displaced.is_empty());

    solver.executor.execute(&Command::CheckSat).unwrap();
    assert!(
        solver
            .executor
            .last_result()
            .is_some_and(|result| result.is_unknown()),
        "captured soft constraint must fail closed"
    );
    assert_eq!(
        solver.executor.unknown_reason(),
        Some(crate::UnknownReason::Incomplete)
    );
}
