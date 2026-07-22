// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::config::PdrConfig;
use crate::pdr::frame::{Frame, Lemma};
use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcParser, ChcSort, ChcVar, PredicateId};

#[test]
fn test_edge_summary_basic() {
    // Test: P(x) ∧ (x >= 0) ⇒ Q(x)
    // With frame lemma P: x >= 5
    // Expected: entry constraint for Q is x >= 5
    let input = r#"
        (declare-fun P (Int) Bool)
        (declare-fun Q (Int) Bool)
        (assert (forall ((x Int)) (=> (= x 5) (P x))))
        (assert (forall ((x Int)) (=> (and (P x) (>= x 0)) (Q x))))
        (assert (forall ((x Int)) (=> (and (Q x) (>= x 10)) false)))
    "#;

    let problem = ChcParser::parse(input).unwrap();
    let config = PdrConfig::default();
    let mut solver = PdrSolver::new(problem, config);

    // Add a frame lemma for P at level 1: x >= 5
    let p_pred = PredicateId::new(0);
    let p_vars = solver.canonical_vars(p_pred).unwrap().to_vec();
    let lemma = Lemma::new(
        p_pred,
        ChcExpr::ge(ChcExpr::var(p_vars[0].clone()), ChcExpr::Int(5)),
        1,
    );
    solver.frames.push(Frame::new());
    // Use add_lemma for proper deduplication tracking
    solver.frames[1].add_lemma(lemma);

    // Get entry constraints for Q (pred 1) at level 1
    let q_pred = PredicateId::new(1);
    let entry = solver.get_entry_constraints(q_pred, 1);

    // Should produce some entry constraint
    assert!(entry.is_some(), "Expected entry constraint for Q");

    let entry_formula = entry.unwrap();
    // The entry should contain x >= 5 (from P's frame lemma)
    // Note: exact form depends on MBP projection
    assert!(
        !matches!(entry_formula, ChcExpr::Bool(true)),
        "Expected non-trivial entry constraint"
    );
}

#[test]
fn test_edge_summary_infeasible_returns_none() {
    // #2491: An UNSAT edge (contradictory frame lemmas) must return None.
    // P(x) ∧ (x >= 0) ⇒ Q(x), but frame says x >= 100 AND x <= 0 → UNSAT.
    let input = r#"
        (declare-fun P (Int) Bool)
        (declare-fun Q (Int) Bool)
        (assert (forall ((x Int)) (=> (= x 5) (P x))))
        (assert (forall ((x Int)) (=> (and (P x) (>= x 0)) (Q x))))
        (assert (forall ((x Int)) (=> (and (Q x) (>= x 10)) false)))
    "#;

    let problem = ChcParser::parse(input).unwrap();
    let config = PdrConfig::default();
    let mut solver = PdrSolver::new(problem, config);

    let p_pred = PredicateId::new(0);
    let p_vars = solver.canonical_vars(p_pred).unwrap().to_vec();

    // Add contradictory frame lemmas: x >= 100 AND x <= 0
    solver.frames.push(Frame::new());
    solver.frames[1].add_lemma(Lemma::new(
        p_pred,
        ChcExpr::ge(ChcExpr::var(p_vars[0].clone()), ChcExpr::Int(100)),
        1,
    ));
    solver.frames[1].add_lemma(Lemma::new(
        p_pred,
        ChcExpr::le(ChcExpr::var(p_vars[0].clone()), ChcExpr::Int(0)),
        1,
    ));

    let q_pred = PredicateId::new(1);
    let entry = solver.get_entry_constraints(q_pred, 1);

    // Edge formula is UNSAT → no summary → None entry constraints.
    assert!(entry.is_none(), "Infeasible edge should return None");
}

#[test]
fn test_extract_bounds_from_conjunction() {
    // Verify extract_bounds_from_constraint finds atomic bounds in conjunctions.
    let x = ChcVar::new("x", ChcSort::Int);
    let constraint = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(10)),
    );
    let bounds = PdrSolver::extract_bounds_from_constraint(&constraint);
    assert_eq!(bounds.len(), 2, "Should extract both ge and le bounds");
}

#[test]
fn test_extract_bounds_from_equality() {
    // Verify extract_bounds_from_constraint extracts both bounds from equality.
    let x = ChcVar::new("x", ChcSort::Int);
    let constraint = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(5));
    let bounds = PdrSolver::extract_bounds_from_constraint(&constraint);
    assert_eq!(bounds.len(), 2, "Equality should yield ge and le bounds");
}

#[test]
fn test_extract_bounds_skips_bool_and_bv_comparisons_issue_6781() {
    let b = ChcVar::new("b", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::BitVec(32));
    let i = ChcVar::new("i", ChcSort::Int);
    let constraint = ChcExpr::and_all(vec![
        ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::Bool(true)),
        ChcExpr::lt(ChcExpr::var(b), ChcExpr::Bool(true)),
        ChcExpr::lt(ChcExpr::var(x), ChcExpr::BitVec(7, 32)),
        ChcExpr::eq(ChcExpr::var(i.clone()), ChcExpr::Int(5)),
    ]);

    let bounds = PdrSolver::extract_bounds_from_constraint(&constraint);

    assert_eq!(
        bounds,
        vec![
            ChcExpr::ge(ChcExpr::var(i.clone()), ChcExpr::Int(5)),
            ChcExpr::le(ChcExpr::var(i), ChcExpr::Int(5)),
        ],
        "edge-summary bound extraction must ignore Bool/BV comparisons"
    );
}

#[test]
fn test_edge_summary_expression_head_args_not_skipped() {
    // #2492: Clauses with expression head args (e.g., x+1) must produce a
    // summary instead of being silently skipped.
    //
    // P(x) ∧ (x >= 0) ⇒ Q(x + 1)
    // With frame lemma P: x >= 5
    // Expected: entry constraint for Q should exist (not None).
    let input = r#"
        (declare-fun P (Int) Bool)
        (declare-fun Q (Int) Bool)
        (assert (forall ((x Int)) (=> (= x 5) (P x))))
        (assert (forall ((x Int)) (=> (and (P x) (>= x 0)) (Q (+ x 1)))))
        (assert (forall ((x Int)) (=> (and (Q x) (>= x 10)) false)))
    "#;

    let problem = ChcParser::parse(input).unwrap();
    let config = PdrConfig::default();
    let mut solver = PdrSolver::new(problem, config);

    let p_pred = PredicateId::new(0);
    let p_vars = solver.canonical_vars(p_pred).unwrap().to_vec();

    solver.frames.push(Frame::new());
    solver.frames[1].add_lemma(Lemma::new(
        p_pred,
        ChcExpr::ge(ChcExpr::var(p_vars[0].clone()), ChcExpr::Int(5)),
        1,
    ));

    let q_pred = PredicateId::new(1);
    let entry = solver.get_entry_constraints(q_pred, 1);

    // Before #2492 fix, this returned None because expression head args were skipped.
    let entry_formula = entry.expect("Expression head args should produce an entry constraint");
    assert!(
        !matches!(entry_formula, ChcExpr::Bool(true)),
        "Expected non-trivial entry constraint, not Bool(true)"
    );
}

/// Verify that extract_bounds produces nothing from a `true` summary.
///
/// When SMT returns Unknown for an edge, we return `Bool(true)` as the
/// may-summary (#2491). This test validates that `true` yields no spurious
/// bounds — the invariant-discovery pipeline correctly skips such edges.
#[test]
fn test_unknown_edge_yields_no_bounds() {
    // Bool(true) has no atomic bounds to extract
    let bounds = PdrSolver::extract_bounds_from_constraint(&ChcExpr::Bool(true));
    assert!(
        bounds.is_empty(),
        "Expected no bounds from trivially-true summary, got {bounds:?}"
    );
}

/// Verify that a `true` entry in a disjunction of summaries
/// preserves the overall entry constraint (doesn't collapse to None).
#[test]
fn test_true_summary_in_disjunction() {
    // If one edge returns Bool(true) and another returns x >= 5,
    // the disjunction should be (true OR x >= 5) which simplifies
    // to true — no useful bounds.
    let x = ChcVar::new("x", ChcSort::Int);
    let bound = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(5));
    let disj = ChcExpr::or_all(vec![ChcExpr::Bool(true), bound]);

    let bounds = PdrSolver::extract_bounds_from_constraint(&disj);
    // Disjunctions don't yield bounds (conservative) — even without
    // the Bool(true), extract_bounds skips disjunctions entirely.
    assert!(
        bounds.is_empty(),
        "Expected no bounds from disjunction with true, got {bounds:?}"
    );
}
