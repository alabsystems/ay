// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_promote_doubles_positive_mark() {
    let mut marks = LitMarks::new(4);
    let lit = Literal::positive(Variable(2));
    marks.mark(lit);
    assert_eq!(marks.get(Variable(2)), 1);
    marks.promote(Variable(2));
    assert_eq!(marks.get(Variable(2)), 2);
}

#[test]
fn test_promote_doubles_negative_mark() {
    let mut marks = LitMarks::new(4);
    let lit = Literal::negative(Variable(1));
    marks.mark(lit);
    assert_eq!(marks.get(Variable(1)), -1);
    marks.promote(Variable(1));
    assert_eq!(marks.get(Variable(1)), -2);
}

#[test]
fn test_promote_zero_stays_zero() {
    let mut marks = LitMarks::new(4);
    assert_eq!(marks.get(Variable(0)), 0);
    marks.promote(Variable(0));
    assert_eq!(marks.get(Variable(0)), 0);
}

#[test]
fn test_promote_out_of_bounds_is_noop() {
    let mut marks = LitMarks::new(2);
    // Variable(5) is out of bounds — promote should not panic.
    marks.promote(Variable(5));
    assert_eq!(marks.get(Variable(5)), 0);
}

fn lit(v: u32, positive: bool) -> Literal {
    if positive {
        Literal::positive(Variable(v))
    } else {
        Literal::negative(Variable(v))
    }
}

/// Identity map returns Unchanged.
#[test]
fn test_rewrite_clause_identity_map_unchanged() {
    let mut marks = LitMarks::new(4);
    let identity: Vec<Literal> = (0..8).map(Literal::from_index).collect();
    let clause = [lit(0, true), lit(1, false), lit(2, true)];
    let mut out = Vec::new();
    let result = marks.rewrite_clause(&clause, &identity, &[], &mut out);
    assert_eq!(result, ClauseRewriteOutcome::Unchanged);
    assert_eq!(out, clause);
}

/// Mapping x1 → x0 produces Changed.
#[test]
fn test_rewrite_clause_substitution_changed() {
    let mut marks = LitMarks::new(4);
    // Map x1 → x0 (both polarities).
    let mut map: Vec<Literal> = (0..8).map(Literal::from_index).collect();
    map[lit(1, true).index()] = lit(0, true);
    map[lit(1, false).index()] = lit(0, false);
    let clause = [lit(1, true), lit(2, true)];
    let mut out = Vec::new();
    let result = marks.rewrite_clause(&clause, &map, &[], &mut out);
    assert_eq!(result, ClauseRewriteOutcome::Changed);
    assert_eq!(out, vec![lit(0, true), lit(2, true)]);
}

/// Duplicate literals after mapping are removed.
#[test]
fn test_rewrite_clause_dedup() {
    let mut marks = LitMarks::new(4);
    // Map x1 → x0.
    let mut map: Vec<Literal> = (0..8).map(Literal::from_index).collect();
    map[lit(1, true).index()] = lit(0, true);
    map[lit(1, false).index()] = lit(0, false);
    // Clause: (x0, x1) → after map: (x0, x0) → dedup: (x0) → Unit.
    let clause = [lit(0, true), lit(1, true)];
    let mut out = Vec::new();
    let result = marks.rewrite_clause(&clause, &map, &[], &mut out);
    assert_eq!(result, ClauseRewriteOutcome::Unit(lit(0, true)));
    assert_eq!(out, vec![lit(0, true)]);
}

/// Complementary literals after mapping produce Tautology.
#[test]
fn test_rewrite_clause_tautology() {
    let mut marks = LitMarks::new(4);
    // Map x1 → ¬x0.
    let mut map: Vec<Literal> = (0..8).map(Literal::from_index).collect();
    map[lit(1, true).index()] = lit(0, false);
    map[lit(1, false).index()] = lit(0, true);
    // Clause: (x0, x1) → after map: (x0, ¬x0) → tautology.
    let clause = [lit(0, true), lit(1, true)];
    let mut out = Vec::new();
    let result = marks.rewrite_clause(&clause, &map, &[], &mut out);
    assert_eq!(result, ClauseRewriteOutcome::Tautology);
}

/// All literals dedup to nothing → Empty.
#[test]
fn test_rewrite_clause_empty() {
    let mut marks = LitMarks::new(4);
    // Map x0 → x1 and x1 → x1.
    let mut map: Vec<Literal> = (0..8).map(Literal::from_index).collect();
    map[lit(0, true).index()] = lit(1, true);
    map[lit(0, false).index()] = lit(1, false);
    // Clause: (x0) → after map: (x1). Wait, that's not empty.
    // To get empty, need all literals to be false at level 0.
    // Use vals for that:
    let clause = [lit(0, true)];
    let mut vals = vec![0i8; 8];
    vals[lit(0, true).index()] = -1; // x0 false at level 0
    let identity: Vec<Literal> = (0..8).map(Literal::from_index).collect();
    let mut out = Vec::new();
    let result = marks.rewrite_clause(&clause, &identity, &vals, &mut out);
    assert_eq!(result, ClauseRewriteOutcome::Empty);
}

/// Level-0 true literal produces Satisfied.
#[test]
fn test_rewrite_clause_satisfied_by_vals() {
    let mut marks = LitMarks::new(4);
    let identity: Vec<Literal> = (0..8).map(Literal::from_index).collect();
    let clause = [lit(0, true), lit(1, true)];
    let mut vals = vec![0i8; 8];
    vals[lit(0, true).index()] = 1; // x0 true at level 0
    let mut out = Vec::new();
    let result = marks.rewrite_clause(&clause, &identity, &vals, &mut out);
    assert_eq!(result, ClauseRewriteOutcome::Satisfied);
}

/// Level-0 false literal is removed from clause.
#[test]
fn test_rewrite_clause_vals_removes_false_literals() {
    let mut marks = LitMarks::new(4);
    let identity: Vec<Literal> = (0..8).map(Literal::from_index).collect();
    let clause = [lit(0, true), lit(1, true), lit(2, true)];
    let mut vals = vec![0i8; 8];
    vals[lit(1, true).index()] = -1; // x1 false at level 0
    let mut out = Vec::new();
    let result = marks.rewrite_clause(&clause, &identity, &vals, &mut out);
    assert_eq!(result, ClauseRewriteOutcome::Changed);
    assert_eq!(out, vec![lit(0, true), lit(2, true)]);
}

/// Multiple calls reuse the same marks without corruption.
#[test]
fn test_rewrite_clause_marks_clean_between_calls() {
    let mut marks = LitMarks::new(4);
    let identity: Vec<Literal> = (0..8).map(Literal::from_index).collect();
    let mut out = Vec::new();

    let clause1 = [lit(0, true), lit(1, true)];
    let r1 = marks.rewrite_clause(&clause1, &identity, &[], &mut out);
    assert_eq!(r1, ClauseRewriteOutcome::Unchanged);

    let clause2 = [lit(0, false), lit(1, false)];
    let r2 = marks.rewrite_clause(&clause2, &identity, &[], &mut out);
    assert_eq!(r2, ClauseRewriteOutcome::Unchanged);
    assert_eq!(out, vec![lit(0, false), lit(1, false)]);
}
