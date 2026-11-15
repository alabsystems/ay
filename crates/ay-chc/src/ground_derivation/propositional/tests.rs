// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the variable-free nullary ground refutation search.
//!
//! The search may only ever PROPOSE a derivation, so every test either checks
//! that a proposal survives the real validator or that no proposal is made.

use super::*;
use crate::clause::ClauseBody;
use crate::ground_derivation::validate_ground_derivation;
use crate::{ChcExpr, ChcSort, ChcVar};

mod cancellation;

fn refutation(problem: &ChcProblem) -> Option<GroundDerivation> {
    ground_nullary_refutation(problem, &mut || true).expect("uninterrupted producer")
}

/// `reached.  reached => error_p0.  error_p0 => false.`
///
/// The exact shape `ChcProblem::query_obligations` produces for a nullary
/// error-marker encoding, and the shape both proof engines decide Unsafe
/// without attaching any replayable evidence.
fn marker_chain() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let reached = problem.declare_predicate("reached_p0", vec![]);
    let error = problem.declare_predicate("error_p0", vec![]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(reached, vec![]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        error,
        vec![],
    )])));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(reached, vec![])]),
        ClauseHead::Predicate(error, vec![]),
    ));
    problem
}

#[test]
fn marker_chain_refutation_validates_against_its_own_clauses() {
    let problem = marker_chain();
    let derivation = refutation(&problem).expect("the chain is refutable");
    validate_ground_derivation(&problem, &derivation).expect("the proposal must validate");
    assert_eq!(derivation.len(), 3);
    assert_eq!(derivation.steps[derivation.query_step].clause_index, 1);
}

#[test]
fn unreachable_marker_is_not_refuted() {
    let mut problem = ChcProblem::new();
    let never = problem.declare_predicate("never", vec![]);
    let error = problem.declare_predicate("error_p1", vec![]);
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        error,
        vec![],
    )])));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(never, vec![])]),
        ClauseHead::Predicate(error, vec![]),
    ));
    assert!(refutation(&problem).is_none());
}

#[test]
fn constraint_only_query_with_no_body_is_refuted_in_one_step() {
    let mut problem = ChcProblem::new();
    let _ = problem.declare_predicate("different_reached", vec![]);
    problem.add_clause(HornClause::query(ClauseBody::empty()));
    let derivation = refutation(&problem).expect("`true => false` is refutable");
    validate_ground_derivation(&problem, &derivation).expect("the proposal must validate");
    assert_eq!(derivation.len(), 1);
    assert_eq!(derivation.query_step, 0);
}

#[test]
fn a_false_constraint_blocks_the_clause_it_guards() {
    let mut problem = ChcProblem::new();
    let error = problem.declare_predicate("error", vec![]);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(false)),
        ClauseHead::Predicate(error, vec![]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        error,
        vec![],
    )])));
    assert!(refutation(&problem).is_none());
}

#[test]
fn a_clause_outside_the_fragment_is_skipped_rather_than_interpreted() {
    // The fact carries a free variable, so its constraint is not decidable by
    // ground evaluation here; the query must not be refuted through it.
    let mut problem = ChcProblem::new();
    let error = problem.declare_predicate("error", vec![]);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(
            ChcExpr::Var(ChcVar::new("x", ChcSort::Int)),
            ChcExpr::Int(0),
        )),
        ClauseHead::Predicate(error, vec![]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        error,
        vec![],
    )])));
    assert!(refutation(&problem).is_none());
}

#[test]
fn a_non_nullary_predicate_is_outside_the_fragment() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("p", vec![ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(p, vec![ChcExpr::Int(0)]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        p,
        vec![ChcExpr::Int(0)],
    )])));
    assert!(refutation(&problem).is_none());
}
