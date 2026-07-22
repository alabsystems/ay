// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #4632: `new_var_internal` must push to ALL per-variable
//! vectors (`scope_selector_set`, `glue_stamp`, `shrink_stamp`) and call
//! `conditioning.ensure_num_vars`. Missing pushes cause OOB panics when the new
//! variable is used in conflict analysis, glue recomputation, or shrinking.

use ay_sat::{Literal, Solver, Variable};
use ntest::timeout;

/// Create a solver, dynamically add variables via `new_var`, build a formula
/// that exercises conflict analysis + glue recomputation on the new variables,
/// and verify no OOB panic occurs.
#[test]
#[timeout(10_000)]
fn new_var_after_construction_does_not_panic() {
    // Start with 2 variables.
    let mut solver = Solver::new(2);
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);

    // Add 3 more variables dynamically — this exercises new_var_internal.
    let x2 = solver.new_var();
    let x3 = solver.new_var();
    let x4 = solver.new_var();

    // Build a non-trivial formula involving all 5 variables so that solving
    // exercises conflict analysis (which uses shrink_stamp) and glue
    // recomputation (which uses glue_stamp).
    // Simple pigeonhole-like constraints to force conflicts:
    // At least one of each pair must be true:
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x2)]);
    solver.add_clause(vec![Literal::positive(x1), Literal::positive(x3)]);
    solver.add_clause(vec![Literal::positive(x2), Literal::positive(x4)]);
    // But also add conflicting constraints to force learning:
    solver.add_clause(vec![
        Literal::negative(x0),
        Literal::negative(x1),
        Literal::negative(x2),
    ]);
    solver.add_clause(vec![
        Literal::negative(x2),
        Literal::negative(x3),
        Literal::negative(x4),
    ]);
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x4)]);
    solver.add_clause(vec![
        Literal::negative(x0),
        Literal::negative(x4),
        Literal::positive(x3),
    ]);

    // Solve — if any per-variable vector was not extended for x2..x4,
    // this will panic with an out-of-bounds index.
    let result = solver.solve().into_inner();
    assert!(
        result.is_sat() || result.is_unsat(),
        "Solver must produce a result without panicking"
    );
}

/// Dynamic variable addition followed by push/pop must not corrupt
/// scope_selector_set or other per-variable state.
#[test]
#[timeout(10_000)]
fn new_var_with_push_pop_no_panic() {
    let mut solver = Solver::new(1);
    let x0 = Variable::new(0);

    solver.add_clause(vec![Literal::positive(x0)]);
    assert!(solver.solve().is_sat());

    solver.push();

    // Add new variables inside the scope.
    let x1 = solver.new_var();
    let x2 = solver.new_var();

    solver.add_clause(vec![Literal::positive(x1), Literal::positive(x2)]);
    solver.add_clause(vec![Literal::negative(x1)]);
    solver.add_clause(vec![Literal::negative(x2)]);

    assert!(
        solver.solve().is_unsat(),
        "Scoped formula with new vars should be UNSAT"
    );

    assert!(solver.pop(), "Pop should succeed");
    let result3 = solver.solve().into_inner();
    assert!(
        result3.is_sat(),
        "After pop, base formula should be SAT, got {result3:?}"
    );
}
