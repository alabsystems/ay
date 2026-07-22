// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcSort, ChcVar};

// Helper to create a test variable
fn var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

// ClauseBody tests

#[test]
fn clause_body_empty() {
    let body = ClauseBody::empty();
    assert!(body.is_empty());
    assert!(body.is_fact());
    assert!(body.predicates.is_empty());
    assert!(body.constraint.is_none());
    assert!(body.vars().is_empty());
}

#[test]
fn clause_body_constraint_only() {
    let x = var("x");
    let body = ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0)));
    assert!(!body.is_empty());
    assert!(body.is_fact()); // No predicates = is_fact
    assert!(body.predicates.is_empty());
    assert!(body.constraint.is_some());

    let vars = body.vars();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name, "x");
}

#[test]
fn clause_body_predicates_only() {
    let x = var("x");
    let y = var("y");
    let pred = PredicateId(0);

    let body = ClauseBody::predicates_only(vec![(pred, vec![ChcExpr::var(x), ChcExpr::var(y)])]);

    assert!(!body.is_empty());
    assert!(!body.is_fact()); // Has predicates = not a fact
    assert_eq!(body.predicates.len(), 1);
    assert!(body.constraint.is_none());

    let vars = body.vars();
    assert_eq!(vars.len(), 2);
    assert!(vars.iter().any(|v| v.name == "x"));
    assert!(vars.iter().any(|v| v.name == "y"));
}

#[test]
fn clause_body_vars_deduplicates() {
    let x = var("x");
    let pred = PredicateId(0);

    // Same variable appears twice
    let body = ClauseBody::new(
        vec![(pred, vec![ChcExpr::var(x.clone()), ChcExpr::var(x.clone())])],
        Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5))),
    );

    let vars = body.vars();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name, "x");
}

#[test]
fn clause_body_vars_multiple_predicates() {
    let x = var("x");
    let y = var("y");
    let z = var("z");
    let pred1 = PredicateId(0);
    let pred2 = PredicateId(1);

    let body = ClauseBody::new(
        vec![
            (pred1, vec![ChcExpr::var(x)]),
            (pred2, vec![ChcExpr::var(y), ChcExpr::var(z)]),
        ],
        None,
    );

    let vars = body.vars();
    assert_eq!(vars.len(), 3);
    assert!(vars.iter().any(|v| v.name == "x"));
    assert!(vars.iter().any(|v| v.name == "y"));
    assert!(vars.iter().any(|v| v.name == "z"));
}

// ClauseHead tests

#[test]
fn clause_head_false() {
    let head = ClauseHead::False;
    assert!(head.is_query());
    assert!(head.predicate_id().is_none());
    assert!(head.vars().is_empty());
}

#[test]
fn clause_head_predicate() {
    let x = var("x");
    let pred = PredicateId(5);
    let head = ClauseHead::Predicate(pred, vec![ChcExpr::var(x)]);

    assert!(!head.is_query());
    assert_eq!(head.predicate_id(), Some(PredicateId(5)));

    let vars = head.vars();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].name, "x");
}

#[test]
fn clause_head_vars_deduplicates() {
    let x = var("x");
    let pred = PredicateId(0);
    let head = ClauseHead::Predicate(pred, vec![ChcExpr::var(x.clone()), ChcExpr::var(x)]);

    let vars = head.vars();
    assert_eq!(vars.len(), 1);
}

// HornClause tests

#[test]
fn horn_clause_fact() {
    let x = var("x");
    let pred = PredicateId(0);

    let clause = HornClause::fact(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        pred,
        vec![ChcExpr::var(x)],
    );

    assert!(clause.is_fact());
    assert!(!clause.is_query());

    let vars = clause.vars();
    assert_eq!(vars.len(), 1);

    let preds = clause.predicate_ids();
    assert_eq!(preds, vec![PredicateId(0)]);
}

#[test]
fn horn_clause_query() {
    let x = var("x");
    let pred = PredicateId(0);

    let clause = HornClause::query(ClauseBody::new(
        vec![(pred, vec![ChcExpr::var(x.clone())])],
        Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
    ));

    assert!(!clause.is_fact());
    assert!(clause.is_query());

    let preds = clause.predicate_ids();
    assert_eq!(preds, vec![PredicateId(0)]);
}

#[test]
fn horn_clause_vars_combines_body_and_head() {
    let x = var("x");
    let y = var("y");
    let pred1 = PredicateId(0);
    let pred2 = PredicateId(1);

    let clause = HornClause::new(
        ClauseBody::predicates_only(vec![(pred1, vec![ChcExpr::var(x)])]),
        ClauseHead::Predicate(pred2, vec![ChcExpr::var(y)]),
    );

    let vars = clause.vars();
    assert_eq!(vars.len(), 2);
    assert!(vars.iter().any(|v| v.name == "x"));
    assert!(vars.iter().any(|v| v.name == "y"));
}

#[test]
fn horn_clause_predicate_ids_includes_both() {
    let x = var("x");
    let pred1 = PredicateId(0);
    let pred2 = PredicateId(1);
    let pred3 = PredicateId(2);

    let clause = HornClause::new(
        ClauseBody::predicates_only(vec![
            (pred1, vec![ChcExpr::var(x.clone())]),
            (pred2, vec![ChcExpr::var(x.clone())]),
        ]),
        ClauseHead::Predicate(pred3, vec![ChcExpr::var(x)]),
    );

    let preds = clause.predicate_ids();
    assert_eq!(preds.len(), 3);
    assert!(preds.contains(&pred1));
    assert!(preds.contains(&pred2));
    assert!(preds.contains(&pred3));
}

#[test]
fn horn_clause_predicate_ids_deduplicates() {
    let x = var("x");
    let pred = PredicateId(0);

    // Same predicate in body and head
    let clause = HornClause::new(
        ClauseBody::predicates_only(vec![(pred, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x)]),
    );

    let preds = clause.predicate_ids();
    assert_eq!(preds.len(), 1);
    assert_eq!(preds[0], pred);
}

// Display tests

#[test]
fn display_empty_body() {
    let body = ClauseBody::empty();
    assert_eq!(body.to_string(), "true");
}

#[test]
fn display_clause_head_false() {
    let head = ClauseHead::False;
    assert_eq!(head.to_string(), "false");
}
