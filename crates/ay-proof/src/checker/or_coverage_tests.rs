// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode coverage for the `or` clausification rule (Packet B1 of #6537).
//!
//! The `or` rule decomposes `(assume (or l1 l2 ... ln))` into `(cl l1 l2 ... ln)`.
//! SatProofManager emits this for multi-literal input clauses.

use crate::checker::*;
use ay_core::{AletheRule, ProofId, ProofStep, Sort, TermId, TermStore};

/// Helper: create `(or a b ...)` without simplification.
fn mk_or_raw(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    terms.mk_app(ay_core::Symbol::named("or"), args, Sort::Bool)
}

/// Helper: create `(and a b ...)` without simplification.
fn mk_and_raw(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    terms.mk_app(ay_core::Symbol::named("and"), args, Sort::Bool)
}

/// Helper: validate a step in strict mode with prior derived clauses.
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
fn test_strict_or_clausification_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let or_abc = mk_or_raw(&mut terms, vec![a, b, c]);
    // Premise: (assume (or a b c)) — unit clause with one or term
    let prior = vec![Some(vec![or_abc])];
    // Conclusion: (cl a b c)
    validate_strict_with_derived(
        &terms,
        AletheRule::Or,
        vec![a, b, c],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid or clausification should pass");
}

#[test]
fn test_strict_or_clausification_wrong_children() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let d = terms.mk_var("d", Sort::Bool);
    let or_ab = mk_or_raw(&mut terms, vec![a, b]);
    let prior = vec![Some(vec![or_ab])];
    // Wrong: conclusion has 'd' instead of 'b'
    let err =
        validate_strict_with_derived(&terms, AletheRule::Or, vec![a, d], vec![ProofId(0)], prior)
            .expect_err("wrong children must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_or_clausification_premise_not_or() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let and_ab = mk_and_raw(&mut terms, vec![a, b]);
    // Premise is (and a b), not (or a b)
    let prior = vec![Some(vec![and_ab])];
    let err =
        validate_strict_with_derived(&terms, AletheRule::Or, vec![a, b], vec![ProofId(0)], prior)
            .expect_err("non-or premise must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_or_clausification_non_unit_premise() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    // Premise clause has two literals, not one
    let prior = vec![Some(vec![a, b])];
    let err =
        validate_strict_with_derived(&terms, AletheRule::Or, vec![a, b], vec![ProofId(0)], prior)
            .expect_err("non-unit premise must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}
