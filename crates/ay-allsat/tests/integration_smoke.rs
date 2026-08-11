// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_allsat::{AllSatConfig, AllSatSolver, AllSatStats};

#[test]
fn projection_collapses_models_with_same_projected_assignment() {
    let mut solver = AllSatSolver::new();

    // x1 must be true.
    solver.add_clause(vec![1]);
    // Tautology introduces x2 but does not constrain it.
    solver.add_clause(vec![2, -2]);

    // Full assignments differ on x2, so two models exist.
    assert_eq!(solver.count().unwrap(), 2);

    // Projecting onto x1 collapses both models into one projected assignment.
    let projected = solver.enumerate_with_config(AllSatConfig {
        projection: Some(vec![1]),
        ..AllSatConfig::default()
    });
    assert_eq!(projected.len(), 1);
    assert_eq!(projected[0].get(1), Some(true));
}

#[test]
fn from_solver_preserves_learned_clauses_incrementally() {
    use ay_sat::{Literal, Solver as SatSolver, Variable};

    // Build solver with (x0 OR x1) AND (NOT x0 OR NOT x1) — XOR, 2 solutions
    let mut sat = SatSolver::new(2);
    sat.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    sat.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::negative(Variable::new(1)),
    ]);

    let mut allsat = AllSatSolver::from_solver(sat);

    // Enumerate with callback, verify incremental behavior
    let mut solutions = Vec::new();
    let stats: AllSatStats = allsat.enumerate_with_callback(AllSatConfig::default(), |sol| {
        solutions.push(sol.clone());
        true
    });

    assert_eq!(solutions.len(), 2, "XOR has exactly 2 models");
    assert_eq!(stats.solutions_found, 2);
    // The final UNSAT call proves blocking worked
    assert_eq!(stats.sat_calls, 3, "2 SAT + 1 final UNSAT call");
}

#[test]
fn from_solver_projected_enumeration_minimal_blocking() {
    use ay_sat::{Literal, Solver as SatSolver, Variable};

    // Formula: x0 AND (x1 OR x2)
    // Full models: {x0=T,x1=T,x2=T}, {x0=T,x1=T,x2=F}, {x0=T,x1=F,x2=T}
    // Projected to {x0}: only 1 distinct assignment (x0=T)
    let mut sat = SatSolver::new(3);
    sat.add_clause(vec![Literal::positive(Variable::new(0))]);
    sat.add_clause(vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    let mut allsat = AllSatSolver::from_solver(sat);
    let config = AllSatConfig {
        projection: Some(vec![0]),
        ..AllSatConfig::default()
    };
    let solutions = allsat.enumerate_with_config(config);
    assert_eq!(solutions.len(), 1, "Only one projected assignment to x0");
}

#[test]
fn callback_early_termination_stops_enumeration() {
    let mut solver = AllSatSolver::new();
    // x1 OR x2 OR x3 — has 7 solutions
    solver.add_clause(vec![1, 2, 3]);

    let mut count = 0usize;
    let stats = solver.enumerate_with_callback(AllSatConfig::default(), |_| {
        count += 1;
        count < 3 // stop after collecting 3rd
    });

    assert_eq!(count, 3);
    assert_eq!(stats.solutions_found, 3);
}

#[test]
fn max_solutions_limit_stops_enumeration() {
    let mut solver = AllSatSolver::new();
    solver.add_clause(vec![1, 2]);
    solver.add_clause(vec![-1, -2]);

    let bounded = solver.enumerate_with_config(AllSatConfig {
        max_solutions: Some(1),
        ..AllSatConfig::default()
    });
    assert_eq!(bounded.len(), 1);
}
