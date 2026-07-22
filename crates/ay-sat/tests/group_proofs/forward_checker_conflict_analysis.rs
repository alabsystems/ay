// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Forward-checker regression tests for non-level-0 UNSAT derivations.
//!
//! Follow-up audit for #4483:
//! ensure empty-clause notification also works when UNSAT is reached
//! after at least one non-zero-level conflict analysis.

use ay_sat::{Literal, Solver, Variable};

/// Pigeonhole formula PHP(3,2): 3 pigeons into 2 holes.
///
/// No unit clauses exist initially, and proving UNSAT requires search with
/// learned clauses.
#[test]
fn test_forward_checker_empty_clause_after_conflict_analysis() {
    let mut solver: Solver = Solver::new(6);
    solver.set_preprocess_enabled(false);
    solver.set_warmup_enabled(false);
    solver.set_walk_enabled(false);
    solver.enable_forward_checker();

    // Each pigeon must be in at least one hole.
    for pigeon in 0..3 {
        let v0 = Literal::positive(Variable::new((pigeon * 2) as u32));
        let v1 = Literal::positive(Variable::new((pigeon * 2 + 1) as u32));
        solver.add_clause(vec![v0, v1]);
    }

    // No two pigeons can share the same hole.
    for hole in 0..2 {
        for p1 in 0..3 {
            for p2 in (p1 + 1)..3 {
                let v1 = Literal::negative(Variable::new((p1 * 2 + hole) as u32));
                let v2 = Literal::negative(Variable::new((p2 * 2 + hole) as u32));
                solver.add_clause(vec![v1, v2]);
            }
        }
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());
    assert!(
        solver.num_learned_clauses() > 0,
        "expected at least one learned clause before UNSAT"
    );
}
