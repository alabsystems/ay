// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Learned cube and clause database tests.

use super::*;

#[test]
fn test_cube_learning_basic() {
    // Test that cube learning correctly handles partial solutions
    // ∃x∀y∀z. (x ∨ y) ∧ (x ∨ ¬y) ∧ (x ∨ z) ∧ (x ∨ ¬z)
    // SAT: x = true satisfies all clauses regardless of y, z
    // This should trigger cube learning when x=true makes everything SAT
    let input = r#"
p cnf 3 4
e 1 0
a 2 3 0
1 2 0
1 -2 0
1 3 0
1 -3 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));

    // Check that cube learning happened
    let stats = solver.stats();
    assert!(
        stats.learned_cubes > 0 || stats.decisions <= 2,
        "Expected cube learning or quick SAT detection"
    );
}

#[test]
fn test_cube_learning_multiple_universals() {
    // Test cube learning with multiple universal variables
    // ∃x₁x₂∀y₁y₂. (x₁ ∨ y₁) ∧ (x₁ ∨ ¬y₁) ∧ (x₂ ∨ y₂) ∧ (x₂ ∨ ¬y₂)
    // SAT: x₁ = true, x₂ = true
    // The solver should learn cubes to avoid exploring all y₁, y₂ combinations
    let input = r#"
p cnf 4 4
e 1 2 0
a 3 4 0
1 3 0
1 -3 0
2 4 0
2 -4 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_cube_propagation() {
    // Test that cube propagation works correctly
    // ∃x∀y∀z. (x ∨ y ∨ z) ∧ (x ∨ y ∨ ¬z) ∧ (x ∨ ¬y ∨ z) ∧ (x ∨ ¬y ∨ ¬z)
    // SAT: x = true satisfies all
    // After x = true, z = true leads to SAT → cube (z) learned
    // Cube propagation should then try z = false automatically
    let input = r#"
p cnf 3 4
e 1 0
a 2 3 0
1 2 3 0
1 2 -3 0
1 -2 3 0
1 -2 -3 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));

    let stats = solver.stats();
    // With cube learning and propagation, we should solve efficiently
    assert!(
        stats.decisions <= 10,
        "Too many decisions: {}",
        stats.decisions
    );
}

/// Document that the QBF solver has no learned clause/cube reduction.
///
/// Unlike the SAT solver (which has `reduce_db`), the QBF solver's `learned`
/// and `cubes` vectors grow monotonically. Every non-level-0 conflict adds
/// a clause; every cube learning event adds a cube. Nothing is ever removed.
///
/// When clause database reduction is implemented, update this test to verify
/// that learned_clauses can decrease between invocations.
#[test]
fn test_learned_clause_reduction() {
    // ∃x∀y. (x ∨ y) ∧ (¬x ∨ ¬y) — UNSAT (from test_exists_forall_unsat)
    // With clause database reduction, learned_clauses + clauses_deleted
    // equals the total clauses ever learned. Active count is bounded.
    let input = "p cnf 2 2\ne 1 0\na 2 0\n1 2 0\n-1 -2 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let _result = solver.solve();

    let stats = solver.stats();
    // Active learned clauses are bounded by total minus deleted
    assert!(
        stats.learned_clauses + stats.clauses_deleted <= stats.conflicts,
        "active ({}) + deleted ({}) should not exceed conflicts ({})",
        stats.learned_clauses,
        stats.clauses_deleted,
        stats.conflicts,
    );
}
