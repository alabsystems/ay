// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

//! Tests for Boolean-ITE branch-implication premise recognition
//! (#ite-expansion-authority).

use crate::checker::{assumed_is_authored_bool_ite_consequence, validate_problem_assumptions};
use crate::ProofCheckError;
use ay_core::{Proof, Sort, TermId, TermStore};

/// Interns the exact producer shapes: the authored Bool ITE
/// `(ite (and g1 g2) t e)` plus the two implications
/// `rewrite_assertion_bool_ites` asserts for it.
fn ite_fixture(terms: &mut TermStore) -> (TermId, TermId, TermId, TermId, TermId, TermId) {
    let g1 = terms.mk_var("g1", Sort::Bool);
    let g2 = terms.mk_var("g2", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let cond = terms.mk_and(vec![g1, g2]);
    let ite = terms.mk_ite_raw(cond, t, e);
    let imp_then = terms.mk_implies(cond, t);
    let not_cond = terms.mk_not(cond);
    let imp_else = terms.mk_implies(not_cond, e);
    (ite, cond, t, e, imp_then, imp_else)
}

fn ites_of(terms: &TermStore, ite: TermId) -> Vec<(TermId, TermId, TermId)> {
    match terms.get(ite) {
        ay_core::term::TermData::Ite(c, t, e) => vec![(*c, *t, *e)],
        _ => panic!("fixture must intern an Ite"),
    }
}

#[test]
fn accepts_the_producers_then_and_else_implications() {
    let mut terms = TermStore::new();
    let (ite, _, _, _, imp_then, imp_else) = ite_fixture(&mut terms);
    let ites = ites_of(&terms, ite);

    assert!(
        assumed_is_authored_bool_ite_consequence(&terms, imp_then, &ites),
        "the then-implication (with De Morgan'd conjunctive guard) must be recognized"
    );
    assert!(
        assumed_is_authored_bool_ite_consequence(&terms, imp_else, &ites),
        "the else-implication must be recognized"
    );
}

#[test]
fn accepts_the_combined_pre_flatten_and_form() {
    let mut terms = TermStore::new();
    let (ite, _, _, _, imp_then, imp_else) = ite_fixture(&mut terms);
    let combined = terms.mk_and(vec![imp_then, imp_else]);
    let ites = ites_of(&terms, ite);

    assert!(
        assumed_is_authored_bool_ite_consequence(&terms, combined, &ites),
        "the pre-FlattenAnd (and then-form else-form) must be recognized"
    );
}

#[test]
fn rejects_a_stronger_clause_with_a_dropped_guard_literal() {
    let mut terms = TermStore::new();
    let (ite, _, t, _, _, _) = ite_fixture(&mut terms);
    let g1 = terms.mk_var("g1", Sort::Bool);
    let not_g1 = terms.mk_not(g1);
    // (or (not g1) t) omits (not g2): STRONGER than the entailed implication.
    let dropped = terms.mk_or(vec![not_g1, t]);
    let ites = ites_of(&terms, ite);

    assert!(
        !assumed_is_authored_bool_ite_consequence(&terms, dropped, &ites),
        "a strict subset of the entailed disjuncts is unentailed and must be rejected"
    );
    // The bare branch alone is stronger still.
    assert!(!assumed_is_authored_bool_ite_consequence(&terms, t, &ites));
}

#[test]
fn rejects_foreign_disjunctions_and_empty_registry() {
    let mut terms = TermStore::new();
    let (ite, _, _, _, imp_then, _) = ite_fixture(&mut terms);
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let foreign = terms.mk_or(vec![a, b]);
    let ites = ites_of(&terms, ite);

    assert!(!assumed_is_authored_bool_ite_consequence(
        &terms, foreign, &ites
    ));
    assert!(!assumed_is_authored_bool_ite_consequence(
        &terms,
        imp_then,
        &[]
    ));
}

#[test]
fn rejects_an_implication_with_an_extra_literal() {
    let mut terms = TermStore::new();
    let (ite, _, t, _, _, _) = ite_fixture(&mut terms);
    let g1 = terms.mk_var("g1", Sort::Bool);
    let g2 = terms.mk_var("g2", Sort::Bool);
    let x = terms.mk_var("unrelated", Sort::Bool);
    let not_g1 = terms.mk_not(g1);
    let not_g2 = terms.mk_not(g2);
    // A WEAKER clause than the implication is entailed too, but it is not the
    // producer's form; recognition stays exact and fails closed.
    let widened = terms.mk_or(vec![not_g1, not_g2, t, x]);
    let ites = ites_of(&terms, ite);

    assert!(
        !assumed_is_authored_bool_ite_consequence(&terms, widened, &ites),
        "extra literals are not the producer's implication and must be rejected"
    );
}

#[test]
fn premise_validator_accepts_ite_implications_and_rejects_strong_clauses() {
    let mut terms = TermStore::new();
    let (ite, _, t, _, imp_then, imp_else) = ite_fixture(&mut terms);

    let mut accepted = Proof::new();
    accepted.add_assume(imp_then, None);
    accepted.add_assume(imp_else, None);
    validate_problem_assumptions(&accepted, &terms, &[ite])
        .expect("branch implications of an authored Bool ITE are entailed premises");

    let mut rejected = Proof::new();
    rejected.add_assume(t, None);
    let error = validate_problem_assumptions(&rejected, &terms, &[ite])
        .expect_err("the bare branch is NOT entailed by the ITE and must be rejected");
    assert!(matches!(
        error,
        ProofCheckError::UnauthorizedAssumption { .. }
    ));
}
