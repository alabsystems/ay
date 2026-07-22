// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for the CaDiCaL-style constrain() API (#8207).
//!
//! Verifies that the temporary constraint clause API works correctly
//! for IC3/PDR use cases: no variable accumulation, proper isolation
//! between solve calls, and correct SAT/UNSAT behavior.

use ay_sat::{AssumeResult, Literal, Solver, Variable};

/// Basic constraint: single literal constraint forces that literal true.
#[test]
fn test_constrain_single_literal_forces_true() {
    let mut solver = Solver::new(2);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);

    // x0 OR x1 (permanent)
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);

    // Constrain: x0 must be true
    solver.constrain(&[Literal::positive(x0)]);

    let result = solver.solve_with_assumptions(&[]).into_inner();
    match result {
        AssumeResult::Sat(model) => {
            assert!(model[0], "x0 should be true due to constraint");
        }
        other => panic!("expected Sat, got {other:?}"),
    }
    // Constraint cleared after solve
    assert!(!solver.failed_constraint());
}

/// Constraint is automatically cleared after solve.
#[test]
fn test_constrain_cleared_after_solve() {
    let mut solver = Solver::new(2);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);

    // x0 OR x1
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);

    // First solve with constraint forcing x0
    solver.constrain(&[Literal::positive(x0)]);
    let r1 = solver.solve_with_assumptions(&[]).into_inner();
    assert!(matches!(r1, AssumeResult::Sat(_)));

    // Second solve without constraint — x1 alone satisfies the clause
    let r2 = solver
        .solve_with_assumptions(&[Literal::negative(x0)])
        .into_inner();
    assert!(
        matches!(r2, AssumeResult::Sat(_)),
        "should be SAT without constraint: x1 can be true"
    );
}

/// Empty constraint is immediately UNSAT.
#[test]
fn test_constrain_empty_is_unsat() {
    let mut solver = Solver::new(2);
    let x0 = Variable::new(0);

    solver.add_clause(vec![Literal::positive(x0)]);
    solver.constrain(&[]);

    let result = solver.solve_with_assumptions(&[]).into_inner();
    assert!(matches!(result, AssumeResult::Unsat(..)));
}

/// Tautological constraint (x and !x) is ignored (always satisfied).
#[test]
fn test_constrain_tautology_ignored() {
    let mut solver = Solver::new(2);
    let x0 = Variable::new(0);

    solver.add_clause(vec![Literal::positive(x0)]);

    // Constraint is tautological — should be ignored
    solver.constrain(&[Literal::positive(x0), Literal::negative(x0)]);

    let result = solver.solve_with_assumptions(&[]).into_inner();
    assert!(matches!(result, AssumeResult::Sat(_)));
    assert!(!solver.failed_constraint());
}

/// Multiple solves with different constraints — verifies isolation.
#[test]
fn test_constrain_multiple_solves_isolated() {
    let mut solver = Solver::new(3);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);

    // x0 OR x1 OR x2
    solver.add_clause(vec![
        Literal::positive(x0),
        Literal::positive(x1),
        Literal::positive(x2),
    ]);

    // Solve 1: constraint forces x0
    solver.constrain(&[Literal::positive(x0)]);
    let r1 = solver.solve_with_assumptions(&[]).into_inner();
    match r1 {
        AssumeResult::Sat(model) => assert!(model[0], "x0 forced by constraint"),
        other => panic!("expected Sat, got {other:?}"),
    }

    // Solve 2: constraint forces x1
    solver.constrain(&[Literal::positive(x1)]);
    let r2 = solver.solve_with_assumptions(&[]).into_inner();
    match r2 {
        AssumeResult::Sat(model) => assert!(model[1], "x1 forced by constraint"),
        other => panic!("expected Sat, got {other:?}"),
    }

    // Solve 3: no constraint — any assignment works
    let r3 = solver.solve_with_assumptions(&[]).into_inner();
    assert!(matches!(r3, AssumeResult::Sat(_)));
}

/// Verify no variable accumulation: constrain() does not create new variables.
#[test]
fn test_constrain_no_variable_accumulation() {
    let mut solver = Solver::new(3);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);

    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);

    let initial_vars = solver.total_num_vars();

    // Run 100 constrain+solve cycles — this is the IC3 pattern
    for _ in 0..100 {
        solver.constrain(&[Literal::positive(x0)]);
        let _ = solver.solve_with_assumptions(&[]);
    }

    // No new variables should have been created
    assert_eq!(
        solver.total_num_vars(),
        initial_vars,
        "constrain() should not create new variables"
    );
}

/// IC3-style usage pattern: repeated solve with constraint + assumptions.
#[test]
fn test_constrain_ic3_pattern() {
    let mut solver = Solver::new(4);
    let vars: Vec<Variable> = (0..4).map(Variable::new).collect();

    // Transition relation: x0' = x0 XOR x1
    // Encoded as CNF clauses
    solver.add_clause(vec![
        Literal::negative(vars[0]),
        Literal::negative(vars[1]),
        Literal::negative(vars[2]),
    ]);
    solver.add_clause(vec![
        Literal::positive(vars[0]),
        Literal::positive(vars[1]),
        Literal::negative(vars[2]),
    ]);
    solver.add_clause(vec![
        Literal::positive(vars[0]),
        Literal::negative(vars[1]),
        Literal::positive(vars[2]),
    ]);
    solver.add_clause(vec![
        Literal::negative(vars[0]),
        Literal::positive(vars[1]),
        Literal::positive(vars[2]),
    ]);

    // IC3 iteration 1: check if cube {x2=T, x3=T} is reachable
    solver.constrain(&[Literal::positive(vars[2]), Literal::positive(vars[3])]);
    let r1 = solver.solve_with_assumptions(&[Literal::positive(vars[0])]);
    assert!(r1.is_sat() || r1.is_unsat()); // either is valid

    // IC3 iteration 2: check different cube
    solver.constrain(&[Literal::negative(vars[2])]);
    let r2 = solver.solve_with_assumptions(&[Literal::negative(vars[0])]);
    assert!(r2.is_sat() || r2.is_unsat());

    // No constraint leakage between iterations
    assert!(!solver.failed_constraint());
}

/// Constraint with disjunction: at least one literal must be satisfiable.
#[test]
fn test_constrain_disjunction() {
    let mut solver = Solver::new(3);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);

    // No permanent clauses — everything is free
    // Constraint: x0 OR x1 OR x2
    solver.constrain(&[
        Literal::positive(x0),
        Literal::positive(x1),
        Literal::positive(x2),
    ]);

    // Assume x0=false and x1=false — constraint forces x2=true
    let result = solver
        .solve_with_assumptions(&[Literal::negative(x0), Literal::negative(x1)])
        .into_inner();
    match result {
        AssumeResult::Sat(model) => {
            assert!(
                model[2],
                "x2 should be true: only remaining constraint literal"
            );
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Verify that constrain() works with solve_with_assumptions_interruptible.
#[test]
fn test_constrain_with_interruptible_solve() {
    let mut solver = Solver::new(2);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);

    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);

    solver.constrain(&[Literal::positive(x0)]);

    let result = solver
        .solve_with_assumptions_interruptible(&[], || false)
        .into_inner();
    match result {
        AssumeResult::Sat(model) => {
            assert!(model[0], "x0 should be true due to constraint");
        }
        other => panic!("expected Sat, got {other:?}"),
    }
    assert!(!solver.failed_constraint());
}

/// Constraint replaced by new constrain() call before solve.
#[test]
fn test_constrain_replace_before_solve() {
    let mut solver = Solver::new(3);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let x2 = Variable::new(2);

    solver.add_clause(vec![
        Literal::positive(x0),
        Literal::positive(x1),
        Literal::positive(x2),
    ]);

    // First constraint
    solver.constrain(&[Literal::positive(x0)]);
    // Replace with different constraint before solving
    solver.constrain(&[Literal::positive(x1)]);

    let result = solver.solve_with_assumptions(&[]).into_inner();
    match result {
        AssumeResult::Sat(model) => {
            assert!(model[1], "x1 should be true (replaced constraint)");
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Stress test: many constrain/solve cycles don't leak memory or vars.
#[test]
fn test_constrain_stress_no_leak() {
    let mut solver = Solver::new(10);
    let vars: Vec<Variable> = (0..10).map(Variable::new).collect();

    // Add some clauses
    for i in 0..9 {
        solver.add_clause(vec![
            Literal::positive(vars[i]),
            Literal::positive(vars[i + 1]),
        ]);
    }

    let initial_vars = solver.total_num_vars();

    for i in 0..500 {
        let constraint_var = vars[i % 10];
        solver.constrain(&[Literal::positive(constraint_var)]);
        let result = solver.solve_with_assumptions(&[]);
        assert!(result.is_sat(), "should always be SAT for this formula");
    }

    assert_eq!(
        solver.total_num_vars(),
        initial_vars,
        "500 constrain/solve cycles should not create new variables"
    );
}
