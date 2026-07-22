// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use ay_maxsat::{MaxSatResult, MaxSatSolver};

#[test]
fn weighted_partial_instance_returns_expected_cost() {
    let mut solver = MaxSatSolver::new();

    // Hard requirement: x1 must be true.
    solver.add_hard_clause(vec![1]);

    // Weighted soft preferences.
    solver.add_soft_clause(vec![1], 10);
    solver.add_soft_clause(vec![-1], 3);
    solver.add_soft_clause(vec![2], 2);

    match solver.solve() {
        MaxSatResult::Optimal { cost, .. } => assert_eq!(cost, 3),
        other => panic!("expected Optimal result, got {other:?}"),
    }
}

#[test]
fn conflicting_hard_clauses_are_unsatisfiable() {
    let mut solver = MaxSatSolver::new();
    solver.add_hard_clause(vec![1]);
    solver.add_hard_clause(vec![-1]);

    assert!(matches!(solver.solve(), MaxSatResult::Unsatisfiable));
}
