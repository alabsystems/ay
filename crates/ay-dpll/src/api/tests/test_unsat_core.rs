// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::api::{Logic, SolveResult, Solver, Sort};

fn core_contains(core: &[String], name: &str) -> bool {
    core.iter().any(|entry| entry == name)
}

fn is_vacuous_unsat(core: &[String], negated_postcondition_name: &str) -> bool {
    !core_contains(core, negated_postcondition_name)
}

#[test]
fn test_unsat_core_basic() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let pos = solver.gt(x, zero);
    solver.try_assert_named(pos, "positive constraint").unwrap();
    let neg = solver.lt(x, zero);
    solver.try_assert_named(neg, "negative").unwrap();
    assert!(solver.check_sat().is_unsat());
    let core = solver.try_get_unsat_core().unwrap();
    assert!(
        core.contains(&"positive constraint".to_string()),
        "quoted symbols must round-trip through get_unsat_core(): {core:?}"
    );
    assert!(
        core.contains(&"negative".to_string()),
        "expected both conflicting named assertions in core: {core:?}"
    );
}

#[test]
fn test_unsat_core_not_enabled() {
    let mut solver = Solver::new(Logic::QfLia);
    // Do NOT enable produce-unsat-cores
    let f = solver.bool_const(false);
    solver.assert_term(f);
    assert!(solver.check_sat().is_unsat());
    let result = solver.try_get_unsat_core();
    match result {
        Err(crate::api::SolverError::UnsatCoreGenerationFailed(msg)) => {
            assert!(msg.contains("unsat core generation is not enabled"));
        }
        other => panic!("expected UnsatCoreGenerationFailed, got {other:?}"),
    }
}

#[test]
fn test_reset_assertions_preserves_declarations() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);
    solver.try_assert_term(gt).unwrap();
    solver.try_push().unwrap();
    assert_eq!(solver.num_scopes(), 1);

    solver.try_reset_assertions().unwrap();
    assert_eq!(solver.num_scopes(), 0);
    assert_eq!(solver.assertions().len(), 0);

    // x is still declared — can reuse it
    let one = solver.int_const(1);
    let eq = solver.eq(x, one);
    solver.try_assert_term(eq).unwrap();
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_assert_named_sort_check() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    match solver.try_assert_named(x, "should_fail") {
        Err(crate::api::SolverError::SortMismatch { operation, .. }) => {
            assert_eq!(operation, "assert_named");
        }
        other => panic!("expected SortMismatch, got {other:?}"),
    }
}

#[test]
fn test_vacuity_detection_non_vacuous() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    let preconditions = solver.eq(x, zero);
    solver
        .try_assert_named(preconditions, "preconditions")
        .unwrap();

    let encoding_axioms = solver.le(x, zero);
    solver
        .try_assert_named(encoding_axioms, "encoding_axioms")
        .unwrap();

    let postcondition = solver.eq(x, zero);
    let negated_postcondition = solver.not(postcondition);
    solver
        .try_assert_named(negated_postcondition, "negated_postcondition")
        .unwrap();

    assert!(solver.check_sat().is_unsat());
    let core = solver.try_get_unsat_core().unwrap();

    assert!(
        core_contains(&core, "negated_postcondition"),
        "non-vacuous core must include negated postcondition: {core:?}"
    );
    assert!(
        !is_vacuous_unsat(&core, "negated_postcondition"),
        "proof should be non-vacuous when negated postcondition is in the core: {core:?}"
    );
}

#[test]
fn test_vacuity_detection_vacuous() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    let preconditions = solver.ge(x, one);
    solver
        .try_assert_named(preconditions, "preconditions")
        .unwrap();

    let encoding_axioms = solver.le(x, zero);
    solver
        .try_assert_named(encoding_axioms, "encoding_axioms")
        .unwrap();

    let postcondition = solver.eq(x, zero);
    let negated_postcondition = solver.not(postcondition);
    solver
        .try_assert_named(negated_postcondition, "negated_postcondition")
        .unwrap();

    assert!(solver.check_sat().is_unsat());
    let core = solver.try_get_unsat_core().unwrap();

    assert!(
        core_contains(&core, "preconditions"),
        "vacuous core should still include the conflicting preconditions: {core:?}"
    );
    assert!(
        core_contains(&core, "encoding_axioms"),
        "vacuous core should still include the conflicting encoding axioms: {core:?}"
    );
    assert!(
        !core_contains(&core, "negated_postcondition"),
        "vacuous core must omit the negated postcondition: {core:?}"
    );
    assert!(
        is_vacuous_unsat(&core, "negated_postcondition"),
        "proof should be classified as vacuous when negated postcondition is absent: {core:?}"
    );
}

/// Verify that named assertions respect push/pop scope:
/// a named assertion in a popped scope does not appear in subsequent cores.
#[test]
fn test_unsat_core_push_pop_scope() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    // Outer scope: x > 0
    let pos = solver.gt(x, zero);
    solver.try_assert_named(pos, "outer_positive").unwrap();

    solver.try_push().unwrap();
    // Inner scope: x < 0 (conflicts with outer)
    let neg = solver.lt(x, zero);
    solver.try_assert_named(neg, "inner_negative").unwrap();
    assert!(solver.check_sat().is_unsat());
    let core = solver.try_get_unsat_core().unwrap();
    assert!(
        core_contains(&core, "outer_positive"),
        "outer name in core: {core:?}"
    );
    assert!(
        core_contains(&core, "inner_negative"),
        "inner name in core: {core:?}"
    );

    // Pop the inner scope — inner_negative is gone
    solver.try_pop().unwrap();
    // Outer constraints alone are SAT
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

/// Verify that `try_get_unsat_core` returns `NotUnsat` after a SAT result.
#[test]
fn test_unsat_core_after_sat_returns_error() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let t = solver.bool_const(true);
    solver.try_assert_named(t, "trivially_true").unwrap();
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    match solver.try_get_unsat_core() {
        Err(crate::api::SolverError::NotUnsat) => {} // expected
        other => panic!("expected NotUnsat error, got {other:?}"),
    }
}
