// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for Blocked Clause Elimination (BCE).

use super::*;
use crate::test_util::lit;

#[test]
fn test_bce_occurrence_list() {
    let mut occ = BCEOccList::new(5);

    let clause1 = vec![lit(0, true), lit(1, false)];
    let clause2 = vec![lit(0, true), lit(2, true)];

    occ.add_clause(0, &clause1);
    occ.add_clause(1, &clause2);

    // lit(0, true) appears in both clauses
    assert_eq!(occ.count(lit(0, true)), 2);
    assert!(occ.get(lit(0, true)).contains(&0));
    assert!(occ.get(lit(0, true)).contains(&1));

    // lit(1, false) appears only in clause 0
    assert_eq!(occ.count(lit(1, false)), 1);
    assert!(occ.get(lit(1, false)).contains(&0));
}

#[test]
fn test_bce_tautology_detection() {
    let mut bce = BCE::new(5);

    // C = {x0, x1}, D = {~x0, ~x1}
    // Resolvent on x0 = {x1, ~x1} - tautology
    let c = vec![lit(0, true), lit(1, true)];
    let d = vec![lit(0, false), lit(1, false)];

    assert!(bce.is_tautological_resolvent(&c, &d, Variable(0)));
}

#[test]
fn test_bce_non_tautology() {
    let mut bce = BCE::new(5);

    // C = {x0, x1}, D = {~x0, x2}
    // Resolvent on x0 = {x1, x2} - NOT a tautology
    let c = vec![lit(0, true), lit(1, true)];
    let d = vec![lit(0, false), lit(2, true)];

    assert!(!bce.is_tautological_resolvent(&c, &d, Variable(0)));
}

#[test]
fn test_bce_simple_blocked() {
    let mut bce = BCE::new(5);

    // C0 = {x0, x1}
    // C1 = {~x0, ~x1}  <- only clause with ~x0
    // Resolving C0 on x0 with C1 gives {x1, ~x1} - tautology
    // So C0 is blocked on x0
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(1, false)], false);

    bce.rebuild(&clauses);

    // C0 should be blocked on x0
    assert!(bce.is_blocked(0, lit(0, true), &clauses));
}

#[test]
fn test_bce_not_blocked() {
    let mut bce = BCE::new(5);

    // C0 = {x0, x1}
    // C1 = {~x0, x2}  <- resolvent would be {x1, x2}, not a tautology
    // So C0 is NOT blocked on x0
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false);

    bce.rebuild(&clauses);

    // C0 should NOT be blocked on x0
    assert!(!bce.is_blocked(0, lit(0, true), &clauses));
}

#[test]
fn test_bce_blocked_no_negation() {
    let mut bce = BCE::new(5);

    // C0 = {x0, x1}
    // No clause contains ~x0
    // So C0 is trivially blocked on x0
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(2, true), lit(3, true)], false); // No ~x0

    bce.rebuild(&clauses);

    // C0 should be blocked on x0 (no resolution partners)
    assert!(bce.is_blocked(0, lit(0, true), &clauses));
}

#[test]
fn test_bce_find_blocking_literal() {
    let mut bce = BCE::new(5);

    // C0 = {x0, x1}
    // C1 = {~x0, ~x1}
    // C0 is blocked on x0 (or x1)
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(1, false)], false);

    bce.rebuild(&clauses);

    // Should find a blocking literal
    let frozen: &[u32] = &[];
    let blocking = bce.find_blocking_literal(0, &clauses, frozen);
    assert!(blocking.is_some());
}

#[test]
fn test_bce_run_elimination() {
    let mut bce = BCE::new(5);

    // C0 = {x0, x1} - blocked on x0 (resolvent with C1 is tautology)
    // C1 = {~x0, ~x1}
    // C2 = {x2, x3} - NOT blocked (no constraints)
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(1, false)], false);
    clauses.add(&[lit(2, true), lit(3, true)], false);

    bce.rebuild(&clauses);

    let frozen: &[u32] = &[];
    let eliminated = bce.run_elimination(&clauses, frozen, 10);

    // At least one clause should be blocked (either C0 or C1, or both)
    assert!(
        !eliminated.is_empty(),
        "Expected at least one blocked clause"
    );
}

#[test]
fn test_bce_stats() {
    let mut bce = BCE::new(5);

    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(1, false)], false);

    bce.rebuild(&clauses);
    let frozen: &[u32] = &[];
    let _ = bce.run_elimination(&clauses, frozen, 10);

    let stats = bce.stats();
    assert_eq!(stats.rounds, 1);
    // Should have eliminated some clauses
    assert!(
        stats.clauses_eliminated > 0 || stats.checks_performed > 0,
        "Expected some activity"
    );
}

#[test]
fn test_bce_multiple_blocking_literals() {
    let mut bce = BCE::new(5);

    // C0 = {x0, x1, x2}
    // C1 = {~x0, ~x1}  <- blocking partner for x0 gives tautology
    // C2 = {~x1, ~x2}  <- blocking partner for x1 gives tautology
    //
    // Resolving C0 on x0 with C1: {x1, x2, ~x1} - tautology
    // Resolving C0 on x1 with C1: {x0, x2, ~x0} - tautology
    // Resolving C0 on x1 with C2: {x0, x2, ~x2} - tautology
    //
    // C0 should be blocked on either x0 or x1
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, false)], false);
    clauses.add(&[lit(1, false), lit(2, false)], false);

    bce.rebuild(&clauses);

    // Check that C0 is blocked on x0 (resolvent with C1 is {x1, x2, ~x1} - tautology)
    let blocked_on_x0 = bce.is_blocked(0, lit(0, true), &clauses);

    // C0 should be blocked on at least one literal
    let frozen: &[u32] = &[];
    let blocking = bce.find_blocking_literal(0, &clauses, frozen);
    assert!(
        blocked_on_x0 || blocking.is_some(),
        "C0 should be blocked on some literal"
    );
}

/// Test that a frozen literal is skipped as a blocking candidate (#1482)
#[test]
fn test_bce_skip_frozen_blocking_literal() {
    let mut bce = BCE::new(5);

    // C0 = {x0, x1}
    // C1 = {~x0, ~x1}
    // C0 is blocked on x0 (or x1) - both work
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(1, false)], false);

    bce.rebuild(&clauses);

    // Without freezing, both x0 and x1 are valid blocking literals
    let frozen_empty: &[u32] = &[];
    let blocking = bce.find_blocking_literal(0, &clauses, frozen_empty);
    assert!(
        blocking.is_some(),
        "Should find blocking literal with no frozen vars"
    );

    // With x0 frozen, x1 should still work as blocking literal
    let frozen_x0 = vec![1u32, 0, 0, 0, 0];
    let blocking = bce.find_blocking_literal(0, &clauses, &frozen_x0);
    let blocking_lit = blocking.expect("x1 should still be a valid blocking literal");
    assert_ne!(
        blocking_lit.variable(),
        Variable(0),
        "frozen x0 should not be selected as blocking literal"
    );

    // With both x0 and x1 frozen, no blocking literal should be found
    let frozen_both = vec![1u32, 1, 0, 0, 0];
    let blocking = bce.find_blocking_literal(0, &clauses, &frozen_both);
    assert!(
        blocking.is_none(),
        "No blocking literal should be found when all candidates are frozen"
    );
}

/// Test that BCE run_elimination respects frozen variables (#1482)
#[test]
fn test_bce_run_elimination_respects_frozen() {
    let mut bce = BCE::new(5);

    // C0 = {x0, x1} - blocked on x0 (resolvent with C1 is tautology)
    // C1 = {~x0, ~x1}
    // C2 = {x2, x3} - blocked on x2 (trivially - no ~x2)
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(1, false)], false);
    clauses.add(&[lit(2, true), lit(3, true)], false);

    bce.rebuild(&clauses);

    // Freeze x0 and x1 to prevent C0/C1 elimination
    let frozen = vec![1u32, 1, 0, 0, 0]; // x0, x1 frozen

    let eliminated = bce.run_elimination(&clauses, &frozen, 10);

    // C0 cannot be eliminated because its only blocking literals (x0, x1) are frozen
    // C2 can still be eliminated on x2 or x3
    assert!(
        !eliminated.iter().any(|e| e.clause_idx == 0),
        "C0 should not be eliminated when x0 and x1 are frozen"
    );
}

/// Test that BCE returns blocking literals for reconstruction (#1486)
#[test]
fn test_bce_returns_blocking_literal() {
    let mut bce = BCE::new(5);

    // C0 = {x0, x1} - blocked on x0 (resolvent with C1 is tautology)
    // C1 = {~x0, ~x1}
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(1, false)], false);

    bce.rebuild(&clauses);

    let frozen: &[u32] = &[];
    let eliminated = bce.run_elimination(&clauses, frozen, 10);

    // At least one clause should be eliminated
    assert!(
        !eliminated.is_empty(),
        "Expected at least one blocked clause"
    );

    // Each eliminated clause should have a valid blocking literal
    for elim in &eliminated {
        let clause_lits = clauses.literals(elim.clause_idx);
        // The blocking literal must be in the clause
        assert!(
            clause_lits.contains(&elim.blocking_literal),
            "Blocking literal must be in the eliminated clause"
        );
    }
}
