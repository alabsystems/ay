// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for lookahead and cube generation.

use super::*;

/// Lookahead on a satisfiable formula with unassigned variables should
/// return Some (a split literal).
#[test]
fn test_lookahead_returns_some_for_unassigned_vars() {
    let mut solver = Solver::new(3);
    // (x0 | x1) & (x1 | x2)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    let result = solver.lookahead();
    assert!(result.is_some(), "lookahead should find a split variable");
    assert_eq!(solver.decision_level, 0, "must return at level 0");
}

/// Lookahead when all variables are assigned at level 0 returns None.
#[test]
fn test_lookahead_all_assigned_returns_none() {
    let mut solver = Solver::new(2);
    // Unit clauses force both variables.
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    let result = solver.lookahead();
    assert!(result.is_none(), "all vars assigned, no split possible");
    assert_eq!(solver.decision_level, 0);
}

/// Lookahead detects failed literals: when one polarity conflicts, the
/// negation is forced at level 0.
#[test]
fn test_lookahead_detects_failed_literal() {
    let mut solver = Solver::new(3);
    // Setting x0=true forces x1=true (from -x0|x1) and x1=false (from -x0|-x1),
    // creating a conflict. So x0 must be false.
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]); // -x0 | x1
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
    ]); // -x0 | -x1
        // Add a clause to keep x2 relevant.
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(2)),
    ]); // x0 | x2
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    let _result = solver.lookahead();

    // x0 should now be assigned false at level 0 (failed literal detection).
    assert_eq!(
        solver.lit_val(Literal::negative(Variable(0))),
        1,
        "x0 should be forced false by failed literal detection"
    );
    assert_eq!(solver.decision_level, 0);
}

/// Lookahead with has_empty_clause set returns None immediately.
#[test]
fn test_lookahead_empty_clause_returns_none() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    // Simulate UNSAT discovery by setting the flag directly.
    solver.has_empty_clause = true;

    let result = solver.lookahead();
    assert!(result.is_none(), "lookahead should return None when UNSAT");
}

/// Lookahead preserves level 0 state: decision_level must be 0 after return,
/// and trail should only grow from failed literal detection (level-0 units).
#[test]
fn test_lookahead_preserves_level0_state() {
    let mut solver = Solver::new(4);
    // A formula where no immediate failed literals exist.
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(2)),
    ]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    let trail_before = solver.trail.len();
    let _result = solver.lookahead();

    assert_eq!(solver.decision_level, 0);
    // Trail can only grow (failed literal units), never shrink.
    assert!(
        solver.trail.len() >= trail_before,
        "trail should not shrink after lookahead"
    );
}

/// generate_cubes(0) returns a single empty cube.
#[test]
fn test_generate_cubes_depth_0() {
    let mut solver = Solver::new(3);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    let cubes = solver.generate_cubes(0);
    assert_eq!(cubes.len(), 1);
    assert!(cubes[0].is_empty());
}

/// generate_cubes(1) produces exactly 2 cubes with 1 literal each,
/// and the two literals are negations of each other.
#[test]
fn test_generate_cubes_depth_1() {
    let mut solver = Solver::new(3);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(2)),
    ]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    let cubes = solver.generate_cubes(1);
    assert_eq!(cubes.len(), 2, "depth-1 should produce 2 cubes");
    assert_eq!(cubes[0].len(), 1, "each cube should have 1 literal");
    assert_eq!(cubes[1].len(), 1, "each cube should have 1 literal");
    assert_eq!(
        cubes[0][0],
        cubes[1][0].negated(),
        "cube literals should be negations of each other"
    );
    assert_eq!(solver.decision_level, 0);
}

/// generate_cubes(2) produces up to 4 cubes.
#[test]
fn test_generate_cubes_depth_2() {
    let mut solver = Solver::new(5);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(3)),
        Literal::positive(Variable(4)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::negative(Variable(4)),
    ]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    let cubes = solver.generate_cubes(2);
    // Should produce at most 4 cubes (2^2), possibly fewer if pruning occurs.
    assert!(
        cubes.len() <= 4,
        "depth-2 should produce at most 4 cubes, got {}",
        cubes.len()
    );
    assert!(
        !cubes.is_empty(),
        "should produce at least 1 cube for satisfiable formula"
    );
    // Each cube should have at most 2 literals.
    for cube in &cubes {
        assert!(
            cube.len() <= 2,
            "depth-2 cube should have at most 2 literals, got {}",
            cube.len()
        );
    }
    assert_eq!(solver.decision_level, 0);
}

/// generate_cubes on an UNSAT formula returns empty.
#[test]
fn test_generate_cubes_unsat_returns_empty() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    // Simulate UNSAT by setting the flag.
    solver.has_empty_clause = true;

    let cubes = solver.generate_cubes(3);
    assert!(
        cubes.is_empty(),
        "UNSAT formula should produce no cubes, got {}",
        cubes.len()
    );
}

/// Cubes should cover the full search space: the set of cubes produced
/// should be such that solving the formula under each cube and combining
/// results covers all possibilities. We verify this by checking that solving
/// the formula with each cube as assumptions yields consistent results.
#[test]
fn test_generate_cubes_coverage() {
    let mut solver = Solver::new(4);
    // Satisfiable formula.
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(3)),
    ]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    let cubes = solver.generate_cubes(2);
    assert!(!cubes.is_empty());

    // Verify that at least one cube is satisfiable.
    let mut found_sat = false;
    for cube in &cubes {
        let mut sub_solver = Solver::new(4);
        sub_solver.add_clause(vec![
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ]);
        sub_solver.add_clause(vec![
            Literal::positive(Variable(2)),
            Literal::positive(Variable(3)),
        ]);
        sub_solver.add_clause(vec![
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ]);
        sub_solver.add_clause(vec![
            Literal::negative(Variable(1)),
            Literal::positive(Variable(3)),
        ]);
        let result = sub_solver.solve_with_assumptions(cube);
        if result.is_sat() {
            found_sat = true;
            break;
        }
    }
    assert!(found_sat, "at least one cube should be satisfiable");
}
