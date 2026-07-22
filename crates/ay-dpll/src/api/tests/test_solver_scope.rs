// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Focused coverage for the public `SolverScope` RAII guard.

use std::panic::{catch_unwind, AssertUnwindSafe};

use crate::api::{Logic, SolveResult, Solver, SolverScope, Sort};

#[test]
fn test_solver_scope_pushes_and_pops() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");
    assert_eq!(solver.num_scopes(), 0, "solver should start without scopes");

    {
        let scope = SolverScope::new(&mut solver).expect("scope push should succeed");
        assert_eq!(scope.num_scopes(), 1, "scope guard should push once");
    }
    assert_eq!(solver.num_scopes(), 0, "scope guard should pop on drop");

    {
        let scope = SolverScope::new(&mut solver).expect("solver should remain reusable");
        assert_eq!(scope.num_scopes(), 1, "reused solver should push again");
    }
    assert_eq!(
        solver.num_scopes(),
        0,
        "reused scope should also pop on drop"
    );
}

#[test]
fn test_solver_scope_panic_does_not_abort() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");

    let result = catch_unwind(AssertUnwindSafe(|| {
        let _scope = SolverScope::new(&mut solver).expect("scope push should succeed");
        panic!("simulated panic inside solver scope");
    }));

    assert!(
        result.is_err(),
        "inner panic should propagate to catch_unwind"
    );
    assert_eq!(
        solver.num_scopes(),
        0,
        "scope guard should clean up during unwind",
    );

    {
        let scope = SolverScope::new(&mut solver).expect("solver should remain reusable");
        assert_eq!(scope.num_scopes(), 1, "solver should push after unwind");
    }
    assert_eq!(
        solver.num_scopes(),
        0,
        "cleanup after unwind should balance scopes"
    );
}

#[test]
fn test_solver_scope_deref_mut_exposes_solver_api() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");
    let mut scope = SolverScope::new(&mut solver).expect("scope push should succeed");

    let x = scope.declare_const("x", Sort::Int);
    let zero = scope.int_const(0);
    let x_gt_zero = scope.try_gt(x, zero).expect("matching Int sorts");
    scope
        .try_assert_term(x_gt_zero)
        .expect("boolean assertion should succeed");

    let result = scope
        .try_check_sat()
        .expect("scoped solver operations should remain available");
    assert_eq!(
        result,
        SolveResult::Sat,
        "scoped query should be satisfiable"
    );
}

#[test]
fn test_solver_scope_drop_restores_nested_manual_pushes() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");

    {
        let mut scope = SolverScope::new(&mut solver).expect("scope push should succeed");
        scope
            .try_push()
            .expect("nested manual push through the guard should succeed");
        assert_eq!(
            scope.num_scopes(),
            2,
            "nested push should increase the visible scope depth"
        );
    }

    assert_eq!(
        solver.num_scopes(),
        0,
        "dropping the guard should restore the solver to its entry depth"
    );

    {
        let scope = SolverScope::new(&mut solver).expect("solver should remain reusable");
        assert_eq!(
            scope.num_scopes(),
            1,
            "solver should still accept a fresh scope after nested push cleanup"
        );
    }
    assert_eq!(
        solver.num_scopes(),
        0,
        "nested push cleanup should leave no leaked scopes behind"
    );
}

#[test]
fn test_solver_scope_drop_panics_after_manual_pop() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");

    let result = catch_unwind(AssertUnwindSafe(|| {
        let mut scope = SolverScope::new(&mut solver).expect("scope push should succeed");
        scope
            .try_pop()
            .expect("manual pop through the guard should succeed once");
    }));

    assert!(
        result.is_err(),
        "dropping a mismatched scope guard should surface the invariant break"
    );
    assert_eq!(
        solver.num_scopes(),
        0,
        "manual pop should leave the solver at the base scope"
    );

    {
        let scope = SolverScope::new(&mut solver).expect("solver should remain reusable");
        assert_eq!(
            scope.num_scopes(),
            1,
            "solver should still accept a fresh scope after the caught panic"
        );
    }
    assert_eq!(
        solver.num_scopes(),
        0,
        "reused solver should still clean up correctly after the regression path"
    );
}

#[test]
fn test_solver_scope_drop_panics_after_reset_assertions() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");

    let result = catch_unwind(AssertUnwindSafe(|| {
        let mut scope = SolverScope::new(&mut solver).expect("scope push should succeed");
        scope
            .try_reset_assertions()
            .expect("reset-assertions through the guard should succeed");
    }));

    assert!(
        result.is_err(),
        "dropping after reset-assertions should surface the invariant break"
    );
    assert_eq!(
        solver.num_scopes(),
        0,
        "reset-assertions should leave the solver at the base scope"
    );

    {
        let scope = SolverScope::new(&mut solver).expect("solver should remain reusable");
        assert_eq!(
            scope.num_scopes(),
            1,
            "solver should still accept a fresh scope after the caught panic"
        );
    }
    assert_eq!(
        solver.num_scopes(),
        0,
        "reused solver should still clean up correctly after reset-assertions"
    );
}

/// Regression test for #7958: pop() on an empty stack must return an error,
/// not panic. verification-consumer relies on try_pop() returning Err for underflow
/// rather than triggering an assert!/panic inside the theory combiner.
#[test]
fn test_try_pop_on_empty_returns_error() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");
    assert_eq!(solver.num_scopes(), 0);

    let result = solver.try_pop();
    assert!(result.is_err(), "try_pop on empty stack should return Err");
    assert_eq!(
        solver.num_scopes(),
        0,
        "scope level should remain 0 after failed pop"
    );

    // Solver should remain usable after the failed pop
    solver
        .try_push()
        .expect("push after failed pop should work");
    assert_eq!(solver.num_scopes(), 1);
    solver.try_pop().expect("pop after push should succeed");
    assert_eq!(solver.num_scopes(), 0);
}

/// Regression test for #7958: multiple pops past zero must all return errors
/// without corrupting state.
#[test]
fn test_try_pop_multiple_underflows() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver should construct");

    solver.try_push().expect("push should succeed");
    solver.try_pop().expect("pop should succeed");

    // Now at depth 0 — three consecutive pops should all fail gracefully
    for i in 0..3 {
        let result = solver.try_pop();
        assert!(
            result.is_err(),
            "try_pop underflow attempt {i} should return Err"
        );
    }

    assert_eq!(solver.num_scopes(), 0);

    // Solver should still work
    solver
        .try_push()
        .expect("push after underflows should work");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.try_gt(x, zero).expect("gt should work");
    solver.try_assert_term(gt).expect("assert should work");
    let result = solver.try_check_sat().expect("check_sat should work");
    assert_eq!(result, SolveResult::Sat);
}
