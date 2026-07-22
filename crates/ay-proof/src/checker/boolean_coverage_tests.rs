// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode coverage for deferred Boolean validators (P1:1553 handoff).
//!
//! Tests for: implies_pos (native =>), implies_neg1/2 (native + desugared),
//! xor_pos2, xor_neg2, not_implies1/2 (native + desugared).

use crate::checker::*;
use ay_core::{AletheRule, ProofId, ProofStep, Sort, TermId, TermStore};

/// Helper: create `(=> a b)` native implication.
fn mk_implies_raw(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(ay_core::Symbol::named("=>"), vec![lhs, rhs], Sort::Bool)
}

/// Helper: create `(or a b)` without simplification.
fn mk_or_raw(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    terms.mk_app(ay_core::Symbol::named("or"), args, Sort::Bool)
}

/// Helper: create `(xor a b)` without simplification.
fn mk_xor_raw(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(ay_core::Symbol::named("xor"), vec![lhs, rhs], Sort::Bool)
}

/// Helper: validate a step in strict mode.
fn validate_strict(
    terms: &TermStore,
    rule: AletheRule,
    clause: Vec<TermId>,
    premises: Vec<ProofId>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::Step {
        rule,
        clause,
        premises,
        args: vec![],
    };
    let mut derived = Vec::new();
    validate_step(terms, &mut derived, ProofId(0), &step, true, None)
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

// --- implies_pos (native =>) ---

#[test]
fn test_strict_implies_pos_valid_native() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    let not_imp = terms.mk_not_raw(imp);
    let not_a = terms.mk_not_raw(a);
    // implies_pos: (cl (not (=> a b)) (not a) b)
    validate_strict(
        &terms,
        AletheRule::ImpliesPos,
        vec![not_imp, not_a, b],
        vec![],
    )
    .expect("valid implies_pos (native) should pass");
}

#[test]
fn test_strict_implies_pos_rejects_wrong_consequent() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    let not_imp = terms.mk_not_raw(imp);
    let not_a = terms.mk_not_raw(a);
    // Wrong: clause has 'c' instead of 'b' as consequent
    let err = validate_strict(
        &terms,
        AletheRule::ImpliesPos,
        vec![not_imp, not_a, c],
        vec![],
    )
    .expect_err("wrong consequent must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_implies_pos_rejects_wrong_arity() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    let not_imp = terms.mk_not_raw(imp);
    let not_a = terms.mk_not_raw(a);
    // Wrong: clause has 4 literals, should have 3
    let err = validate_strict(
        &terms,
        AletheRule::ImpliesPos,
        vec![not_imp, not_a, b, a],
        vec![],
    )
    .expect_err("wrong arity must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// --- implies_neg1 (native =>) ---

#[test]
fn test_strict_implies_neg1_valid_native() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    // implies_neg1: (cl (=> a b) a)
    validate_strict(&terms, AletheRule::ImpliesNeg1, vec![imp, a], vec![])
        .expect("valid implies_neg1 (native) should pass");
}

#[test]
fn test_strict_implies_neg1_valid_desugared() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    // Desugared (=> a b) = (or (not a) b)
    let imp = mk_or_raw(&mut terms, vec![not_a, b]);
    // implies_neg1: (cl (or (not a) b) a)
    validate_strict(&terms, AletheRule::ImpliesNeg1, vec![imp, a], vec![])
        .expect("valid implies_neg1 (desugared) should pass");
}

#[test]
fn test_strict_implies_neg1_rejects_wrong_antecedent() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    // Wrong: clause has 'c' instead of 'a'
    let err = validate_strict(&terms, AletheRule::ImpliesNeg1, vec![imp, c], vec![])
        .expect_err("wrong antecedent must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_implies_neg1_rejects_wrong_arity() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    // Wrong: clause has 3 literals
    let err = validate_strict(&terms, AletheRule::ImpliesNeg1, vec![imp, a, b], vec![])
        .expect_err("wrong arity must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// --- implies_neg2 (native =>) ---

#[test]
fn test_strict_implies_neg2_valid_native() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    let not_b = terms.mk_not_raw(b);
    // implies_neg2: (cl (=> a b) (not b))
    validate_strict(&terms, AletheRule::ImpliesNeg2, vec![imp, not_b], vec![])
        .expect("valid implies_neg2 (native) should pass");
}

#[test]
fn test_strict_implies_neg2_valid_desugared() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    // Desugared (=> a b) = (or (not a) b)
    let imp = mk_or_raw(&mut terms, vec![not_a, b]);
    // implies_neg2: (cl (or (not a) b) (not b))
    validate_strict(&terms, AletheRule::ImpliesNeg2, vec![imp, not_b], vec![])
        .expect("valid implies_neg2 (desugared) should pass");
}

#[test]
fn test_strict_implies_neg2_rejects_wrong_consequent() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    let not_c = terms.mk_not_raw(c);
    // Wrong: clause has (not c) instead of (not b)
    let err = validate_strict(&terms, AletheRule::ImpliesNeg2, vec![imp, not_c], vec![])
        .expect_err("wrong consequent must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_implies_neg2_rejects_positive_consequent() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    // Wrong: clause has 'b' (positive) instead of '(not b)'
    let err = validate_strict(&terms, AletheRule::ImpliesNeg2, vec![imp, b], vec![])
        .expect_err("positive consequent must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// --- xor_pos2 ---

#[test]
fn test_strict_xor_pos2_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let xor_ab = mk_xor_raw(&mut terms, a, b);
    let not_xor = terms.mk_not_raw(xor_ab);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    // xor_pos2: (cl (not (xor a b)) (not a) (not b))
    validate_strict(
        &terms,
        AletheRule::XorPos2,
        vec![not_xor, not_a, not_b],
        vec![],
    )
    .expect("valid xor_pos2 should pass");
}

#[test]
fn test_strict_xor_pos2_accepts_emitted_clause_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let xor_ab = mk_xor_raw(&mut terms, a, b);
    let not_xor = terms.mk_not_raw(xor_ab);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    // Permuted order
    validate_strict(
        &terms,
        AletheRule::XorPos2,
        vec![not_a, not_xor, not_b],
        vec![],
    )
    .expect("emitted xor_pos2 clause order should pass");
}

#[test]
fn test_strict_xor_pos2_rejects_positive_arguments() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let xor_ab = mk_xor_raw(&mut terms, a, b);
    let not_xor = terms.mk_not_raw(xor_ab);
    // Wrong: positive args instead of negated
    let err = validate_strict(&terms, AletheRule::XorPos2, vec![not_xor, a, b], vec![])
        .expect_err("positive args in xor_pos2 must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// --- xor_neg2 ---

#[test]
fn test_strict_xor_neg2_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let xor_ab = mk_xor_raw(&mut terms, a, b);
    let not_a = terms.mk_not_raw(a);
    // xor_neg2: (cl (xor a b) (not a) b)
    validate_strict(&terms, AletheRule::XorNeg2, vec![xor_ab, not_a, b], vec![])
        .expect("valid xor_neg2 should pass");
}

#[test]
fn test_strict_xor_neg2_accepts_emitted_clause_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let xor_ab = mk_xor_raw(&mut terms, a, b);
    let not_a = terms.mk_not_raw(a);
    // Permuted order
    validate_strict(&terms, AletheRule::XorNeg2, vec![not_a, b, xor_ab], vec![])
        .expect("emitted xor_neg2 clause order should pass");
}

#[test]
fn test_strict_xor_neg2_rejects_swapped_polarity() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let xor_ab = mk_xor_raw(&mut terms, a, b);
    let not_b = terms.mk_not_raw(b);
    // Wrong: (cl (xor a b) a (not b)) -- this is xor_neg1, not xor_neg2
    let err = validate_strict(&terms, AletheRule::XorNeg2, vec![xor_ab, a, not_b], vec![])
        .expect_err("swapped polarity must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// --- not_implies1 (premise-based, native =>) ---

#[test]
fn test_strict_not_implies1_valid_native() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    let not_imp = terms.mk_not_raw(imp);
    // Premise: (not (=> a b))
    let prior = vec![Some(vec![not_imp])];
    // not_implies1: (cl a)
    validate_strict_with_derived(
        &terms,
        AletheRule::NotImplies1,
        vec![a],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid not_implies1 (native) should pass");
}

#[test]
fn test_strict_not_implies1_valid_desugared() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    // Desugared (=> a b) = (or (not a) b)
    let imp = mk_or_raw(&mut terms, vec![not_a, b]);
    let not_imp = terms.mk_not_raw(imp);
    // Premise: (not (or (not a) b))
    let prior = vec![Some(vec![not_imp])];
    // not_implies1: (cl a)
    validate_strict_with_derived(
        &terms,
        AletheRule::NotImplies1,
        vec![a],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid not_implies1 (desugared) should pass");
}

#[test]
fn test_strict_not_implies1_rejects_wrong_conclusion() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    let not_imp = terms.mk_not_raw(imp);
    let prior = vec![Some(vec![not_imp])];
    // Wrong: conclusion is 'c' instead of 'a'
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::NotImplies1,
        vec![c],
        vec![ProofId(0)],
        prior,
    )
    .expect_err("wrong conclusion must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_not_implies1_rejects_non_unit_conclusion() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    let not_imp = terms.mk_not_raw(imp);
    let prior = vec![Some(vec![not_imp])];
    // Wrong: conclusion has 2 literals
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::NotImplies1,
        vec![a, b],
        vec![ProofId(0)],
        prior,
    )
    .expect_err("non-unit conclusion must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// --- not_implies2 (premise-based, native =>) ---

#[test]
fn test_strict_not_implies2_valid_native() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    let not_imp = terms.mk_not_raw(imp);
    let not_b = terms.mk_not_raw(b);
    // Premise: (not (=> a b))
    let prior = vec![Some(vec![not_imp])];
    // not_implies2: (cl (not b))
    validate_strict_with_derived(
        &terms,
        AletheRule::NotImplies2,
        vec![not_b],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid not_implies2 (native) should pass");
}

#[test]
fn test_strict_not_implies2_valid_desugared() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    // Desugared (=> a b) = (or (not a) b)
    let imp = mk_or_raw(&mut terms, vec![not_a, b]);
    let not_imp = terms.mk_not_raw(imp);
    // Premise: (not (or (not a) b))
    let prior = vec![Some(vec![not_imp])];
    // not_implies2: (cl (not b))
    validate_strict_with_derived(
        &terms,
        AletheRule::NotImplies2,
        vec![not_b],
        vec![ProofId(0)],
        prior,
    )
    .expect("valid not_implies2 (desugared) should pass");
}

#[test]
fn test_strict_not_implies2_rejects_wrong_conclusion() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    let not_imp = terms.mk_not_raw(imp);
    let not_c = terms.mk_not_raw(c);
    let prior = vec![Some(vec![not_imp])];
    // Wrong: conclusion is (not c) instead of (not b)
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::NotImplies2,
        vec![not_c],
        vec![ProofId(0)],
        prior,
    )
    .expect_err("wrong conclusion must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_not_implies2_rejects_positive_conclusion() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let imp = mk_implies_raw(&mut terms, a, b);
    let not_imp = terms.mk_not_raw(imp);
    let prior = vec![Some(vec![not_imp])];
    // Wrong: conclusion is 'b' (positive) instead of '(not b)'
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::NotImplies2,
        vec![b],
        vec![ProofId(0)],
        prior,
    )
    .expect_err("positive conclusion must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}
