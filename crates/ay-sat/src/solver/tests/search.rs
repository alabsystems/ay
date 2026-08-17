// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Search heuristic tests: chronological backtracking, phase saving, random var freq.
//!
//! Extracted from tests.rs for code-quality (Part of #5142).

use super::*;

include!("search/chrono_phase_and_random_frequency.rs");

include!("search/basic_preprocessing_and_randomized.rs");

// ========================================================================
// Assignment-Level + Chrono BT Correctness Tests (#6993)
// ========================================================================

/// Regression test for #6993: conflict analysis panic when chrono BT +
/// assignment_level corrections cause all conflict clause literals to
/// be at level 0. Previously, analyze_and_backtrack would backtrack to
/// conflict_level=0 and then fall through to analyze_conflict, which
/// asserts decision_level > 0.
///
/// This test uses an UNSAT formula where unit propagation at level 0
/// determines most variables, forcing a level-0 conflict after a
/// decision at level 1.
#[test]
fn test_chrono_assignment_level_level0_conflict() {
    // Formula: variables 0..4
    // Level-0 unit propagations force most variables, then a decision
    // leads to a conflict where all reason clauses trace back to level 0.
    //
    // Clauses:
    //   (x0)          -- unit: x0 = true at level 0
    //   (-x0 | x1)    -- propagates x1 = true at level 0
    //   (-x1 | x2)    -- propagates x2 = true at level 0
    //   (-x2 | x3)    -- propagates x3 = true at level 0
    //   (-x3 | -x4)   -- when x4 decided true, conflicts via x3
    //   (x3 | x4)     -- forces x4=true when x3=false (not reached)
    //   (-x0 | -x2 | x4) -- with x0,x2 true at level 0, x4 must be true
    //   (-x3 | -x4)   -- duplicate: x3=true,x4=true conflicts
    //
    // Under chrono BT + assignment_level, propagated literals from
    // level-0 reasons get level=0, so the conflict clause has all
    // level-0 literals. find_conflict_level returns 0, and we must
    // handle this without calling analyze_conflict.
    let mut solver = Solver::new(5);
    solver.chrono_enabled = true;

    let x = |i: u32| Variable(i);
    let pos = |i: u32| Literal::positive(x(i));
    let neg = |i: u32| Literal::negative(x(i));

    // Unit clause: x0 = true
    solver.add_clause(vec![pos(0)]);
    // Implications chain from x0 → x1 → x2 → x3
    solver.add_clause(vec![neg(0), pos(1)]);
    solver.add_clause(vec![neg(1), pos(2)]);
    solver.add_clause(vec![neg(2), pos(3)]);
    // Conflict: x3 AND x4 can't both be true
    solver.add_clause(vec![neg(3), neg(4)]);
    // But also: x3 AND -x4 can't both be true (forces contradiction)
    solver.add_clause(vec![neg(3), pos(4)]);

    // This is UNSAT: x0→x1→x2→x3 forced, then both x4 and -x4 required.
    // With assignment_level, all propagated vars have level 0.
    let result = solver.solve().into_inner();
    assert!(
        result.is_unsat(),
        "Formula should be UNSAT (chrono + assignment_level level-0 conflict)"
    );
}

/// Same as above but through the assumptions path, which has its own
/// chrono pre-backtrack handling (#6993 Pattern 1).
#[test]
fn test_chrono_assignment_level_level0_conflict_assumptions() {
    let mut solver = Solver::new(6);
    solver.chrono_enabled = true;

    let x = |i: u32| Variable(i);
    let pos = |i: u32| Literal::positive(x(i));
    let neg = |i: u32| Literal::negative(x(i));

    // Unit propagation chain at level 0
    solver.add_clause(vec![pos(0)]);
    solver.add_clause(vec![neg(0), pos(1)]);
    solver.add_clause(vec![neg(1), pos(2)]);
    solver.add_clause(vec![neg(2), pos(3)]);

    // Conflict: x3 forces both x4 and -x4
    solver.add_clause(vec![neg(3), neg(4)]);
    solver.add_clause(vec![neg(3), pos(4)]);

    // Solve with an assumption on a variable not involved in the conflict
    let assumptions = vec![pos(5)];
    let result = solver.solve_with_assumptions(&assumptions);

    // Should be UNSAT regardless of assumptions (base formula is UNSAT)
    assert!(
        matches!(result.into_inner(), AssumeResult::Unsat(..)),
        "Formula should be UNSAT with assumptions (chrono + assignment_level)"
    );
}

// ========================================================================
// Monotone Lucky Phase Tests (Part of #8040)
// ========================================================================

/// Positive monotone: every clause contains at least one positive literal.
/// Setting all variables true satisfies all clauses trivially.
///
/// Formula: (x0 OR NOT x1) AND (x1 OR NOT x2) AND (x2 OR NOT x0)
/// Each clause has a positive literal, so positive monotone applies.
///
/// Reference: Kissat lucky.c:11-45 (no_all_negative_clauses)
#[test]
fn test_lucky_positive_monotone_sat() {
    let mut solver = Solver::new(3);
    // (x0 OR NOT x1): positive literal x0
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ]);
    // (x1 OR NOT x2): positive literal x1
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::negative(Variable(2)),
    ]);
    // (x2 OR NOT x0): positive literal x2
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::negative(Variable(0)),
    ]);
    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            // Verify model satisfies all clauses
            assert!(model[0] || !model[1], "clause 1 violated");
            assert!(model[1] || !model[2], "clause 2 violated");
            assert!(model[2] || !model[0], "clause 3 violated");
        }
        _ => panic!("Expected SAT for positive monotone formula"),
    }
}

/// Negative monotone: every clause contains at least one negative literal.
/// Setting all variables false satisfies all clauses trivially.
///
/// Formula: (NOT x0 OR x1) AND (NOT x1 OR x2) AND (NOT x2 OR x0)
/// Each clause has a negative literal, so negative monotone applies.
///
/// Reference: Kissat lucky.c:47-80 (no_all_positive_clauses)
#[test]
fn test_lucky_negative_monotone_sat() {
    let mut solver = Solver::new(3);
    // (NOT x0 OR x1): negative literal NOT x0
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    // (NOT x1 OR x2): negative literal NOT x1
    solver.add_clause(vec![
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    // (NOT x2 OR x0): negative literal NOT x2
    solver.add_clause(vec![
        Literal::negative(Variable(2)),
        Literal::positive(Variable(0)),
    ]);
    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            // Verify model satisfies all clauses
            assert!(!model[0] || model[1], "clause 1 violated");
            assert!(!model[1] || model[2], "clause 2 violated");
            assert!(!model[2] || model[0], "clause 3 violated");
        }
        _ => panic!("Expected SAT for negative monotone formula"),
    }
}

/// Positive monotone fails: formula has an all-negative clause.
/// (NOT x0 OR NOT x1) is all-negative, so positive monotone does not apply.
/// The formula is still SAT but must be solved by other strategies.
#[test]
fn test_lucky_positive_monotone_not_applicable() {
    let mut solver = Solver::new(2);
    // (x0 OR x1): has positive literals
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    // (NOT x0 OR NOT x1): all negative -- blocks positive monotone
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
    ]);
    let result = solver.solve().into_inner();
    // Still SAT, just not via positive monotone
    assert!(
        matches!(result, SatResult::Sat(_)),
        "Formula is SAT even if positive monotone doesn't apply"
    );
}

/// Negative monotone fails: formula has an all-positive clause.
/// (x0 OR x1) is all-positive, so negative monotone does not apply.
#[test]
fn test_lucky_negative_monotone_not_applicable() {
    let mut solver = Solver::new(2);
    // (NOT x0 OR NOT x1): has negative literals
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
    ]);
    // (x0 OR x1): all positive -- blocks negative monotone
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    let result = solver.solve().into_inner();
    // Still SAT, just not via negative monotone
    assert!(
        matches!(result, SatResult::Sat(_)),
        "Formula is SAT even if negative monotone doesn't apply"
    );
}
