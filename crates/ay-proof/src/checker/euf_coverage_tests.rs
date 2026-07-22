// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode coverage for EUF equality rule validators (P1:1555).
//!
//! Tests for: refl, symm, trans, cong, eq_transitive, eq_congruent,
//! eq_congruent_pred as Step rules in strict mode.

use crate::checker::*;
use ay_core::{AletheRule, ProofId, ProofStep, Sort, TermId, TermStore};

/// Helper: create `(= a b)` without simplification.
fn mk_eq_raw(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(ay_core::Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

/// Helper: create `(f args...)` function application.
fn mk_fun(terms: &mut TermStore, name: &str, args: Vec<TermId>, sort: Sort) -> TermId {
    terms.mk_app(ay_core::Symbol::named(name), args, sort)
}

/// Helper: validate a step in strict mode (zero premises).
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

// ===== refl =====

#[test]
fn test_strict_refl_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let eq_aa = mk_eq_raw(&mut terms, a, a);
    // refl: (cl (= a a))
    validate_strict(&terms, AletheRule::Refl, vec![eq_aa], vec![]).expect("valid refl should pass");
}

#[test]
fn test_strict_refl_rejects_different_sides() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let err = validate_strict(&terms, AletheRule::Refl, vec![eq_ab], vec![])
        .expect_err("different sides must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_refl_rejects_non_equality() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let err = validate_strict(&terms, AletheRule::Refl, vec![a], vec![])
        .expect_err("non-equality must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_refl_rejects_negated_equality() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let eq_aa = mk_eq_raw(&mut terms, a, a);
    let not_eq = terms.mk_not_raw(eq_aa);
    let err = validate_strict(&terms, AletheRule::Refl, vec![not_eq], vec![])
        .expect_err("negated equality must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_refl_rejects_multi_literal() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let eq_aa = mk_eq_raw(&mut terms, a, a);
    let err = validate_strict(&terms, AletheRule::Refl, vec![eq_aa, eq_aa], vec![])
        .expect_err("multi-literal must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// ===== symm =====

#[test]
fn test_strict_symm_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_ba = mk_eq_raw(&mut terms, b, a);
    // premise 0: (= a b), conclusion: (= b a)
    validate_strict_with_derived(
        &terms,
        AletheRule::Symm,
        vec![eq_ba],
        vec![ProofId(0)],
        vec![Some(vec![eq_ab])],
    )
    .expect("valid symm should pass");
}

#[test]
fn test_strict_symm_rejects_same_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    // premise 0: (= a b), conclusion: (= a b) — NOT reversed
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::Symm,
        vec![eq_ab],
        vec![ProofId(0)],
        vec![Some(vec![eq_ab])],
    )
    .expect_err("non-reversed equality must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_symm_valid_negated() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_ba = mk_eq_raw(&mut terms, b, a);
    let not_eq_ab = terms.mk_not_raw(eq_ab);
    let not_eq_ba = terms.mk_not_raw(eq_ba);
    // premise: (not (= a b)), conclusion: (not (= b a))
    validate_strict_with_derived(
        &terms,
        AletheRule::Symm,
        vec![not_eq_ba],
        vec![ProofId(0)],
        vec![Some(vec![not_eq_ab])],
    )
    .expect("negated symm should pass");
}

#[test]
fn test_strict_symm_rejects_polarity_mismatch() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_ba = mk_eq_raw(&mut terms, b, a);
    let not_eq_ba = terms.mk_not_raw(eq_ba);
    // premise: positive (= a b), conclusion: negative (not (= b a))
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::Symm,
        vec![not_eq_ba],
        vec![ProofId(0)],
        vec![Some(vec![eq_ab])],
    )
    .expect_err("polarity mismatch must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// ===== trans =====

#[test]
fn test_strict_trans_valid_two_step() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_bc = mk_eq_raw(&mut terms, b, c);
    let eq_ac = mk_eq_raw(&mut terms, a, c);
    // premises: (= a b), (= b c), conclusion: (= a c)
    validate_strict_with_derived(
        &terms,
        AletheRule::Trans,
        vec![eq_ac],
        vec![ProofId(0), ProofId(1)],
        vec![Some(vec![eq_ab]), Some(vec![eq_bc])],
    )
    .expect("valid 2-step trans should pass");
}

#[test]
fn test_strict_trans_valid_three_step() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let d = terms.mk_var("d", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_bc = mk_eq_raw(&mut terms, b, c);
    let eq_cd = mk_eq_raw(&mut terms, c, d);
    let eq_ad = mk_eq_raw(&mut terms, a, d);
    // premises: (= a b), (= b c), (= c d), conclusion: (= a d)
    validate_strict_with_derived(
        &terms,
        AletheRule::Trans,
        vec![eq_ad],
        vec![ProofId(0), ProofId(1), ProofId(2)],
        vec![Some(vec![eq_ab]), Some(vec![eq_bc]), Some(vec![eq_cd])],
    )
    .expect("valid 3-step trans should pass");
}

#[test]
fn test_strict_trans_rejects_broken_chain() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let d = terms.mk_var("d", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_cd = mk_eq_raw(&mut terms, c, d);
    let eq_ad = mk_eq_raw(&mut terms, a, d);
    // premises: (= a b), (= c d) — no link from b to c
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::Trans,
        vec![eq_ad],
        vec![ProofId(0), ProofId(1)],
        vec![Some(vec![eq_ab]), Some(vec![eq_cd])],
    )
    .expect_err("broken chain must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_trans_rejects_wrong_conclusion() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_bc = mk_eq_raw(&mut terms, b, c);
    let eq_ab2 = mk_eq_raw(&mut terms, a, b);
    // premises: (= a b), (= b c), conclusion: (= a b) — should be (= a c)
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::Trans,
        vec![eq_ab2],
        vec![ProofId(0), ProofId(1)],
        vec![Some(vec![eq_ab]), Some(vec![eq_bc])],
    )
    .expect_err("wrong conclusion must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// ===== cong =====

#[test]
fn test_strict_cong_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let fb = mk_fun(&mut terms, "f", vec![b], Sort::Int);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_fa_fb = mk_eq_raw(&mut terms, fa, fb);
    // premise: (= a b), conclusion: (= (f a) (f b))
    validate_strict_with_derived(
        &terms,
        AletheRule::Cong,
        vec![eq_fa_fb],
        vec![ProofId(0)],
        vec![Some(vec![eq_ab])],
    )
    .expect("valid cong should pass");
}

#[test]
fn test_strict_cong_valid_binary() {
    let mut terms = TermStore::new();
    let a1 = terms.mk_var("a1", Sort::Int);
    let b1 = terms.mk_var("b1", Sort::Int);
    let a2 = terms.mk_var("a2", Sort::Int);
    let b2 = terms.mk_var("b2", Sort::Int);
    let ga1a2 = mk_fun(&mut terms, "g", vec![a1, a2], Sort::Int);
    let gb1b2 = mk_fun(&mut terms, "g", vec![b1, b2], Sort::Int);
    let eq_a1b1 = mk_eq_raw(&mut terms, a1, b1);
    let eq_a2b2 = mk_eq_raw(&mut terms, a2, b2);
    let eq_conc = mk_eq_raw(&mut terms, ga1a2, gb1b2);
    // premises: (= a1 b1), (= a2 b2), conclusion: (= (g a1 a2) (g b1 b2))
    validate_strict_with_derived(
        &terms,
        AletheRule::Cong,
        vec![eq_conc],
        vec![ProofId(0), ProofId(1)],
        vec![Some(vec![eq_a1b1]), Some(vec![eq_a2b2])],
    )
    .expect("valid binary cong should pass");
}

#[test]
fn test_strict_cong_valid_partial_premises() {
    // When some arguments are identical, fewer premises are needed
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let gac = mk_fun(&mut terms, "g", vec![a, c], Sort::Int);
    let gbc = mk_fun(&mut terms, "g", vec![b, c], Sort::Int);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_conc = mk_eq_raw(&mut terms, gac, gbc);
    // Only first argument differs; one premise suffices
    validate_strict_with_derived(
        &terms,
        AletheRule::Cong,
        vec![eq_conc],
        vec![ProofId(0)],
        vec![Some(vec![eq_ab])],
    )
    .expect("partial-premise cong should pass");
}

#[test]
fn test_strict_cong_rejects_different_symbols() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let gb = mk_fun(&mut terms, "g", vec![b], Sort::Int);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_conc = mk_eq_raw(&mut terms, fa, gb);
    // f vs g — different symbols
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::Cong,
        vec![eq_conc],
        vec![ProofId(0)],
        vec![Some(vec![eq_ab])],
    )
    .expect_err("different symbols must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

#[test]
fn test_strict_cong_rejects_missing_premise() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let gac = mk_fun(&mut terms, "g", vec![a, c], Sort::Int);
    let gbd = mk_fun(&mut terms, "g", vec![b, d], Sort::Int);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_conc = mk_eq_raw(&mut terms, gac, gbd);
    // Both args differ but only one premise provided
    let err = validate_strict_with_derived(
        &terms,
        AletheRule::Cong,
        vec![eq_conc],
        vec![ProofId(0)],
        vec![Some(vec![eq_ab])],
    )
    .expect_err("missing premise for second arg must fail");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// ===== eq_transitive as Step rule =====

#[test]
fn test_strict_eq_transitive_step_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_bc = mk_eq_raw(&mut terms, b, c);
    let eq_ac = mk_eq_raw(&mut terms, a, c);
    let not_eq_ab = terms.mk_not_raw(eq_ab);
    let not_eq_bc = terms.mk_not_raw(eq_bc);
    // eq_transitive as Step: (cl (not (= a b)) (not (= b c)) (= a c))
    validate_strict(
        &terms,
        AletheRule::EqTransitive,
        vec![not_eq_ab, not_eq_bc, eq_ac],
        vec![],
    )
    .expect("valid eq_transitive step should pass");
}

#[test]
fn test_strict_eq_transitive_step_rejects_broken_chain() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_cd = mk_eq_raw(&mut terms, c, d);
    let eq_ad = mk_eq_raw(&mut terms, a, d);
    let not_eq_ab = terms.mk_not_raw(eq_ab);
    let not_eq_cd = terms.mk_not_raw(eq_cd);
    // no link from b to c
    let err = validate_strict(
        &terms,
        AletheRule::EqTransitive,
        vec![not_eq_ab, not_eq_cd, eq_ad],
        vec![],
    )
    .expect_err("broken chain must fail");
    assert!(matches!(err, ProofCheckError::InvalidTheoryLemma { .. }));
}

// ===== eq_congruent as Step rule =====

#[test]
fn test_strict_eq_congruent_step_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let fb = mk_fun(&mut terms, "f", vec![b], Sort::Int);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let eq_fa_fb = mk_eq_raw(&mut terms, fa, fb);
    let not_eq_ab = terms.mk_not_raw(eq_ab);
    // eq_congruent: (cl (not (= a b)) (= (f a) (f b)))
    validate_strict(
        &terms,
        AletheRule::EqCongruent,
        vec![not_eq_ab, eq_fa_fb],
        vec![],
    )
    .expect("valid eq_congruent step should pass");
}

// ===== eq_congruent_pred as Step rule =====

#[test]
fn test_strict_eq_congruent_pred_step_valid() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let pa = mk_fun(&mut terms, "p", vec![a], Sort::Bool);
    let pb = mk_fun(&mut terms, "p", vec![b], Sort::Bool);
    let eq_ab = mk_eq_raw(&mut terms, a, b);
    let not_eq_ab = terms.mk_not_raw(eq_ab);
    let not_pa = terms.mk_not_raw(pa);
    // eq_congruent_pred: (cl (not (= a b)) (not (p a)) (p b))
    validate_strict(
        &terms,
        AletheRule::EqCongruentPred,
        vec![not_eq_ab, not_pa, pb],
        vec![],
    )
    .expect("valid eq_congruent_pred step should pass");
}
