// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode coverage for `boolean_negation.rs` split helpers.
//!
//! Tests pin duplicate-sensitive conclusion matching and the desugared
//! `App("ite", ...)` path accepted by `decode_ite()`.

use crate::checker::*;
use ay_core::{AletheRule, ProofId, ProofStep, Sort, Symbol, TermId, TermStore};

fn mk_and_raw(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("and"), args, Sort::Bool)
}

fn mk_eq_raw(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

fn mk_desugared_ite_raw(terms: &mut TermStore, c: TermId, t: TermId, e: TermId) -> TermId {
    terms.mk_app(Symbol::named("ite"), vec![c, t, e], Sort::Bool)
}

fn validate_strict_with_derived(
    terms: &TermStore,
    rule: AletheRule,
    clause: Vec<TermId>,
    premises: Vec<ProofId>,
    prior_derived: Vec<Option<Vec<TermId>>>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::Step {
        rule,
        clause,
        premises,
        args: vec![],
    };
    let mut derived = prior_derived;
    let step_id = ProofId(derived.len() as u32);
    validate_step(terms, &mut derived, step_id, &step, true, None)
}

#[test]
fn test_strict_not_and_rejects_duplicate_conclusion_literal() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let and_ab = mk_and_raw(&mut terms, vec![a, b]);
    let not_and = terms.mk_not_raw(and_ab);
    let not_a = terms.mk_not_raw(a);
    let prior = vec![Some(vec![not_and])];

    let err = validate_strict_with_derived(
        &terms,
        AletheRule::NotAnd,
        vec![not_a, not_a],
        vec![ProofId(0)],
        prior,
    )
    .expect_err("duplicating one conjunct negation must fail");

    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_not_equiv1_rejects_duplicate_operand() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let not_eq = terms.mk_not_raw(eq_ab);
    let prior = vec![Some(vec![not_eq])];

    let err = validate_strict_with_derived(
        &terms,
        AletheRule::NotEquiv1,
        vec![a, a],
        vec![ProofId(0)],
        prior,
    )
    .expect_err("duplicating one equality side must fail");

    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_not_ite1_valid_desugared_app_ite() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = mk_desugared_ite_raw(&mut terms, c, t, e);
    let not_ite = terms.mk_not_raw(ite);
    let not_e = terms.mk_not_raw(e);
    let prior = vec![Some(vec![not_ite])];

    validate_strict_with_derived(
        &terms,
        AletheRule::NotIte1,
        vec![c, not_e],
        vec![ProofId(0)],
        prior,
    )
    .expect("desugared App(ite ...) should be accepted by not_ite1");
}

#[test]
fn test_strict_not_ite2_valid_desugared_app_ite() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let t = terms.mk_var("t", Sort::Bool);
    let e = terms.mk_var("e", Sort::Bool);
    let ite = mk_desugared_ite_raw(&mut terms, c, t, e);
    let not_ite = terms.mk_not_raw(ite);
    let not_c = terms.mk_not_raw(c);
    let not_t = terms.mk_not_raw(t);
    let prior = vec![Some(vec![not_ite])];

    validate_strict_with_derived(
        &terms,
        AletheRule::NotIte2,
        vec![not_c, not_t],
        vec![ProofId(0)],
        prior,
    )
    .expect("desugared App(ite ...) should be accepted by not_ite2");
}
