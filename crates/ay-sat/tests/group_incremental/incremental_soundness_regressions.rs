// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_sat::{Literal, SatResult, Solver, Variable};
use ntest::timeout;

/// Scoped contradictions must not latch UNSAT after pop().
#[test]
#[timeout(10_000)]
fn test_unsat_latch_cleared_after_pop() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    solver.push();
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
    solver.add_clause(vec![Literal::negative(Variable::new(0))]);
    assert!(
        solver.solve().into_inner().is_unsat(),
        "Scoped contradiction should produce UNSAT"
    );

    assert!(solver.pop(), "Pop should succeed");
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "After pop, base formula should be SAT again"
    );
}

/// Conditioning (GBCE) can eliminate base clauses during the first solve.
/// Those clauses must be restored before a scoped solve so that the solver
/// can derive UNSAT from scoped constraints that contradict the base formula.
///
/// Without clause restoration in reset_search_state (#3475, 3bf12e13c),
/// the scoped solve sees an empty base formula and returns wrong-SAT.
#[test]
#[timeout(10_000)]
fn test_conditioning_eliminated_clauses_restored_for_scoped_solve() {
    // 4 user variables. All clauses are positive-literal (satisfied under the
    // default all-true phase assignment). Conditioning should identify all
    // variables as autarky and eliminate all base clauses.
    let mut solver = Solver::new(4);
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(2)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(3)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(2)),
        Literal::positive(Variable::new(3)),
    ]);

    // First solve: preprocessing may run conditioning and eliminate all base
    // clauses (they are all globally blocked under the all-true assignment).
    let result1 = solver.solve().into_inner();
    assert!(
        matches!(result1, SatResult::Sat(_)),
        "Base formula should be SAT"
    );

    // Push scope and add constraints that contradict the base formula:
    // force all variables false. Base clauses require at least 2 true.
    solver.push();
    solver.add_clause(vec![Literal::negative(Variable::new(0))]);
    solver.add_clause(vec![Literal::negative(Variable::new(1))]);
    solver.add_clause(vec![Literal::negative(Variable::new(2))]);
    solver.add_clause(vec![Literal::negative(Variable::new(3))]);

    let result2 = solver.solve().into_inner();
    assert!(
        result2.is_unsat(),
        "Base + all-negative scoped constraints should be UNSAT. \
         If SAT, conditioning-eliminated base clauses were not restored."
    );

    // Pop and verify base formula is still SAT.
    assert!(solver.pop(), "Pop should succeed");
    let result3 = solver.solve().into_inner();
    assert!(
        matches!(result3, SatResult::Sat(_)),
        "After pop, base formula should be SAT again"
    );
}
