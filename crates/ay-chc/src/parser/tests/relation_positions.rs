// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Relation applications outside the positions a Horn clause gives them.
//!
//! The clause builder takes body atoms only from `and`; anything else went
//! into the background constraint, where the SMT encoding reads a relation
//! application as a FREE Bool variable, and a conjunction asserted as a fact
//! became `true => false`. AY published `unsat` on safe systems of these
//! shapes (found by the 2026-09-29 CHC differential generator, z3 5.1: `sat`).
//! Now a top-level conjunct is a body atom (or a fact), and a relation nested
//! under any other connective is refused.

use super::*;

const DECLS: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun R (Int) Bool)
(declare-fun fail () Bool)
(assert (P 1))
(assert (forall ((x Int)) (=> (P x) (Q (+ x 1)))))
";

fn parse(clause: &str) -> ChcResult<ChcProblem> {
    ChcParser::parse(&format!("{DECLS}{clause}\n(check-sat)\n"))
}

fn refused(clause: &str) {
    match parse(clause) {
        Err(error) => assert!(
            error.to_string().contains("unsupported CHC input"),
            "unexpected error for {clause}: {error}"
        ),
        Ok(problem) => panic!(
            "{clause} must be refused, parsed to {:?}",
            problem.clauses()
        ),
    }
}

/// The last clause, which must carry every relation as a body atom.
fn last_query_atoms(clause: &str) -> Vec<String> {
    let problem = parse(clause).expect("parses");
    let last = problem.clauses().last().expect("a clause").clone();
    assert!(last.is_query(), "{clause} is a query: {last}");
    let constraint = last.body.constraint.clone();
    assert!(
        !constraint
            .as_ref()
            .is_some_and(ChcProblem::expr_contains_predicate_app),
        "no relation may stay in the constraint: {last}"
    );
    last.body
        .predicates
        .iter()
        .map(|(id, _)| problem.get_predicate(*id).expect("declared").name.clone())
        .collect()
}

#[test]
fn a_relation_under_or_or_not_in_a_body_is_refused() {
    refused("(assert (forall ((x Int)) (=> (and (P x) (or (Q x) (R x))) false)))");
    refused("(assert (forall ((x Int)) (=> (and (Q x) (not (P x))) false)))");
    refused("(assert (forall ((x Int)) (=> (and (Q x) (ite (> x 0) (P x) (R x))) false)))");
    refused("(assert (forall ((x Int)) (=> (and (Q x) (= (P x) (> x 5))) false)))");
    refused("(assert (forall ((x Int)) (or (not (P x)) (Q x))))");
}

#[test]
fn a_negated_relation_head_becomes_a_body_atom() {
    // `Q(x) => not P(x)` is the query `Q(x) /\ P(x) => false`.
    let atoms = last_query_atoms("(assert (forall ((x Int)) (=> (Q x) (not (P x)))))");
    assert_eq!(atoms, ["Q", "P"]);
}

#[test]
fn negated_query_spellings_become_queries() {
    assert_eq!(
        last_query_atoms("(assert (forall ((x Int)) (not (and (P x) (< x 0)))))"),
        ["P"]
    );
    assert_eq!(
        last_query_atoms(
            "(assert (forall ((x Int)) (=> (and (P x) (> x 0)) fail)))\n(assert (not fail))"
        ),
        ["fail"]
    );
}

#[test]
fn a_conjunction_of_facts_is_each_fact() {
    let problem = parse("(assert (and (P 0) (Q 5)))").expect("parses");
    let facts: Vec<_> = problem
        .clauses()
        .iter()
        .filter(|clause| clause.body.predicates.is_empty() && !clause.is_query())
        .collect();
    assert_eq!(
        facts.len(),
        3,
        "P(1), P(0) and Q(5) are facts: {:?}",
        problem.clauses()
    );
    assert!(
        problem.clauses().iter().all(|clause| !clause.is_query()),
        "no `true => false` query may appear: {:?}",
        problem.clauses()
    );
}

#[test]
fn conjunctive_and_curried_heads_are_split_into_horn_clauses() {
    let problem =
        parse("(assert (forall ((x Int)) (=> (P x) (and (Q (+ x 2)) (R x)))))").expect("parses");
    let heads: Vec<String> = problem
        .clauses()
        .iter()
        .filter_map(|clause| match &clause.head {
            ClauseHead::Predicate(id, _) if !clause.body.predicates.is_empty() => {
                Some(problem.get_predicate(*id).expect("declared").name.clone())
            }
            _ => None,
        })
        .collect();
    // DECLS' P(x) => Q(x+1), then the two halves of the conjunctive head.
    assert_eq!(heads, ["Q", "Q", "R"]);
    // `Q(x) => (P(x) => x > 5)` is the query `Q(x) /\ P(x) /\ not(x > 5) => false`.
    assert_eq!(
        last_query_atoms("(assert (forall ((x Int)) (=> (Q x) (=> (P x) (> x 5)))))"),
        ["Q", "P"]
    );
}

#[test]
fn validation_still_rejects_a_nested_relation_built_through_the_api() {
    // The parser refuses the shape; `ChcProblem::validate` keeps rejecting it
    // for problems other frontends build, before dependency slicing.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![]);
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let nested = ChcExpr::or(
        ChcExpr::predicate_app("P", p, vec![]),
        ChcExpr::eq(x, ChcExpr::int(0)),
    );
    problem.add_clause(crate::HornClause::new(
        crate::ClauseBody::constraint(nested),
        ClauseHead::False,
    ));
    assert!(matches!(
        problem.validate(),
        Err(crate::ChcError::Verification(_))
    ));
}
