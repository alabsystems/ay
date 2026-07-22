// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for ay-qbf.

use ay_qbf::{parse_qdimacs, QbfSolver};

/// Cube propagation reason indices must not panic during conflict analysis.
///
/// Before the fix, `propagate_cubes()` stored reason indices as
/// `Reason::Propagated(usize::MAX / 2 + i)`, which caused an index-out-of-bounds
/// panic in `analyze_conflict()` when it tried to look up the reason clause.
/// The fix uses `Reason::CubePropagated(i)` so conflict analysis can handle
/// cube-propagated literals without indexing into the clause database.
#[test]
fn cube_propagated_reason_no_panic() {
    // ∀y∃x∀z. (x ∨ y ∨ z) ∧ (¬x ∨ y ∨ ¬z) ∧ (x ∨ ¬y ∨ z) ∧ (¬x ∨ ¬y ∨ ¬z)
    // Interleaved quantifiers force cube learning + clause conflicts.
    let input = "p cnf 3 4\na 1 0\ne 2 0\na 3 0\n2 1 3 0\n-2 1 -3 0\n2 -1 3 0\n-2 -1 -3 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    // Must not panic. Result correctness is secondary to no-panic.
    let _result = solver.solve_with_limit(1000);
}
