// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Sort, Symbol};

use super::*;

include!("tests/forall_inst_sequential.rs");

struct ForallInstFixture {
    terms: TermStore,
    quantified: TermId,
    instance: TermId,
    implication: TermId,
    int_value: TermId,
    bool_value: TermId,
}

fn forall_inst_fixture() -> ForallInstFixture {
    let mut terms = TermStore::new();
    let x = terms.mk_var("fi_x", Sort::Int);
    let b = terms.mk_var("fi_b", Sort::Bool);
    let p_x = terms.mk_app(Symbol::named("fi_p"), [x], Sort::Bool);
    let body = terms.mk_app(Symbol::named("and"), [p_x, b], Sort::Bool);
    let quantified = terms.mk_forall(
        vec![
            ("fi_x".to_string(), Sort::Int),
            ("fi_b".to_string(), Sort::Bool),
        ],
        body,
    );
    let int_value = terms.mk_int(7.into());
    let bool_value = terms.mk_bool(true);
    let p_value = terms.mk_app(Symbol::named("fi_p"), [int_value], Sort::Bool);
    let instance = terms.mk_app(Symbol::named("and"), [p_value, bool_value], Sort::Bool);
    let not_quantified = terms.mk_not_raw(quantified);
    let implication = terms.mk_app(Symbol::named("or"), [not_quantified, instance], Sort::Bool);
    ForallInstFixture {
        terms,
        quantified,
        instance,
        implication,
        int_value,
        bool_value,
    }
}

#[test]
fn exact_multi_binder_forall_instantiation_is_valid() {
    let fixture = forall_inst_fixture();
    validate_forall_inst(
        &fixture.terms,
        ProofId(0),
        &[fixture.implication],
        0,
        &[fixture.int_value, fixture.bool_value],
    )
    .expect("exact simultaneous forall substitution must validate");
}

#[test]
fn forall_inst_rejects_ambiguous_same_name_variable_identities() {
    let mut terms = TermStore::new();
    let bound = terms.mk_var("fi_identity_x", Sort::Int);
    let stale = terms.mk_fresh_named_var("fi_identity_x", Sort::Int);
    assert_ne!(bound, stale);
    let p_bound = terms.mk_app(Symbol::named("fi_identity_p"), [bound], Sort::Bool);
    let p_stale = terms.mk_app(Symbol::named("fi_identity_q"), [stale], Sort::Bool);
    let body = terms.mk_app(Symbol::named("and"), [p_bound, p_stale], Sort::Bool);
    let quantified = terms.mk_forall(vec![("fi_identity_x".to_string(), Sort::Int)], body);
    let value = terms.mk_int(0.into());
    let p_value = terms.mk_app(Symbol::named("fi_identity_p"), [value], Sort::Bool);
    let q_value = terms.mk_app(Symbol::named("fi_identity_q"), [value], Sort::Bool);
    let instance = terms.mk_app(Symbol::named("and"), [p_value, q_value], Sort::Bool);
    let not_quantified = terms.mk_not_raw(quantified);
    let implication = terms.mk_app(Symbol::named("or"), [not_quantified, instance], Sort::Bool);

    assert!(
        validate_forall_inst(&terms, ProofId(0), &[implication], 0, &[value]).is_err(),
        "one binder name must never authorize two stable Var identities"
    );
}

#[test]
fn forall_inst_rejects_substitution_through_a_shadowing_binder() {
    let mut terms = TermStore::new();
    let shadowed = terms.mk_fresh_named_var("fi_shadow_x", Sort::Int);
    let shadowed_body = terms.mk_app(Symbol::named("fi_shadow_p"), [shadowed], Sort::Bool);
    let nested = terms.mk_exists(vec![("fi_shadow_x".to_string(), Sort::Int)], shadowed_body);
    let quantified = terms.mk_forall(vec![("fi_shadow_x".to_string(), Sort::Int)], nested);

    let value = terms.mk_int(0.into());
    let forged_body = terms.mk_app(Symbol::named("fi_shadow_p"), [value], Sort::Bool);
    let forged_instance =
        terms.mk_exists(vec![("fi_shadow_x".to_string(), Sort::Int)], forged_body);
    let not_quantified = terms.mk_not_raw(quantified);
    let implication = terms.mk_app(
        Symbol::named("or"),
        [not_quantified, forged_instance],
        Sort::Bool,
    );

    assert!(
        validate_forall_inst(&terms, ProofId(0), &[implication], 0, &[value]).is_err(),
        "an outer binder must never authorize substitution through a shadowing binder"
    );
}

#[test]
fn forall_inst_or_and_resolution_chain_is_strict_context_valid() {
    let mut fixture = forall_inst_fixture();
    let not_quantified = fixture.terms.mk_not_raw(fixture.quantified);
    let not_instance = fixture.terms.mk_not_raw(fixture.instance);
    let mut proof = Proof::new();
    let quantified_assume = proof.add_assume(fixture.quantified, None);
    let forall_inst = proof.add_rule_step(
        AletheRule::ForallInst,
        vec![fixture.implication],
        Vec::new(),
        vec![fixture.int_value, fixture.bool_value],
    );
    let clausified = proof.add_rule_step(
        AletheRule::Or,
        vec![not_quantified, fixture.instance],
        vec![forall_inst],
        Vec::new(),
    );
    let instance = proof.add_resolution(
        vec![fixture.instance],
        fixture.quantified,
        clausified,
        quantified_assume,
    );
    let negated_instance = proof.add_assume(not_instance, None);
    proof.add_resolution(Vec::new(), fixture.instance, instance, negated_instance);

    let quality = crate::check_proof_strict_with_context(
        &proof,
        &fixture.terms,
        None,
        None,
        Some(&[fixture.quantified, not_instance]),
    )
    .expect("exact forall_inst + or + resolution chain must validate strictly");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn forall_inst_rejects_wrong_source_and_body() {
    let mut fixture = forall_inst_fixture();
    let y = fixture.terms.mk_var("fi_y", Sort::Int);
    let other_body = fixture.terms.mk_app(Symbol::named("fi_q"), [y], Sort::Bool);
    let other_quantified = fixture
        .terms
        .mk_forall(vec![("fi_y".to_string(), Sort::Int)], other_body);
    let not_other = fixture.terms.mk_not_raw(other_quantified);
    let wrong_source = fixture.terms.mk_app(
        Symbol::named("or"),
        [not_other, fixture.instance],
        Sort::Bool,
    );
    assert!(validate_forall_inst(
        &fixture.terms,
        ProofId(0),
        &[wrong_source],
        0,
        &[fixture.int_value],
    )
    .is_err());

    let wrong_instance = fixture.terms.mk_bool(false);
    let not_quantified = fixture.terms.mk_not_raw(fixture.quantified);
    let wrong_body = fixture.terms.mk_app(
        Symbol::named("or"),
        [not_quantified, wrong_instance],
        Sort::Bool,
    );
    assert!(validate_forall_inst(
        &fixture.terms,
        ProofId(0),
        &[wrong_body],
        0,
        &[fixture.int_value, fixture.bool_value],
    )
    .is_err());
}

#[test]
fn forall_inst_rejects_wrong_arity_order_and_sort() {
    let mut fixture = forall_inst_fixture();
    assert!(validate_forall_inst(
        &fixture.terms,
        ProofId(0),
        &[fixture.implication],
        0,
        &[fixture.int_value],
    )
    .is_err());
    assert!(validate_forall_inst(
        &fixture.terms,
        ProofId(0),
        &[fixture.implication],
        0,
        &[fixture.bool_value, fixture.int_value],
    )
    .is_err());

    let not_quantified = fixture.terms.mk_not_raw(fixture.quantified);
    let non_boolean_or = fixture.terms.mk_app(
        Symbol::named("or"),
        [not_quantified, fixture.instance],
        Sort::Int,
    );
    assert!(validate_forall_inst(
        &fixture.terms,
        ProofId(0),
        &[non_boolean_or],
        0,
        &[fixture.int_value, fixture.bool_value],
    )
    .is_err());

    let not_quantified = fixture.terms.mk_not_raw(fixture.quantified);
    let reversed = fixture.terms.mk_app(
        Symbol::named("or"),
        [fixture.instance, not_quantified],
        Sort::Bool,
    );
    assert!(validate_forall_inst(
        &fixture.terms,
        ProofId(0),
        &[reversed],
        0,
        &[fixture.int_value, fixture.bool_value],
    )
    .is_err());
}

#[test]
fn forall_inst_rejects_nested_binder_and_partial_capture() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("outer_x", Sort::Int);
    let inner_x = terms.mk_var("inner_x", Sort::Int);
    let inner_body = terms.mk_app(Symbol::named("nested_p"), [x, inner_x], Sort::Bool);
    let nested = terms.mk_forall(vec![("inner_x".to_string(), Sort::Int)], inner_body);
    let quantified = terms.mk_forall(vec![("outer_x".to_string(), Sort::Int)], nested);
    let value = terms.mk_int(1.into());
    let attempted_instance = nested;
    let not_quantified = terms.mk_not_raw(quantified);
    let implication = terms.mk_app(
        Symbol::named("or"),
        [not_quantified, attempted_instance],
        Sort::Bool,
    );
    assert!(validate_forall_inst(&terms, ProofId(0), &[implication], 0, &[value],).is_err());

    let binder_as_argument = x;
    assert!(
        validate_forall_inst(&terms, ProofId(0), &[implication], 0, &[binder_as_argument],)
            .is_err()
    );
}

#[test]
fn forall_inst_accepts_a_binder_free_body_instantiated_at_a_shadowed_symbol() {
    // `(or (not (forall ((fi_amb_x Int)) (fi_amb_p fi_amb_x))) (fi_amb_p fi_amb_x))`
    // — the conclusion's `fi_amb_x` is FREE (the forall is discharged), so this
    // is `∀x. p x ⊢ p c` at the ambient `c` the binder shadows. The body binds
    // nothing, so the conclusion binds nothing and no name in it can be
    // captured; refusing on the spelling alone rejected a valid instantiation.
    let mut terms = TermStore::new();
    let x = terms.mk_var("fi_amb_x", Sort::Int);
    let body = terms.mk_app(Symbol::named("fi_amb_p"), [x], Sort::Bool);
    let quantified = terms.mk_forall(vec![("fi_amb_x".to_string(), Sort::Int)], body);
    let not_quantified = terms.mk_not_raw(quantified);
    let implication = terms.mk_app(Symbol::named("or"), [not_quantified, body], Sort::Bool);

    validate_forall_inst(&terms, ProofId(0), &[implication], 0, &[x])
        .expect("a binder-free body instantiated at the symbol its binder shadows is valid");
}

#[test]
fn forall_inst_accepts_a_distinct_same_spelled_argument_in_a_binder_free_body() {
    let mut terms = TermStore::new();
    let bound = terms.mk_var("fi_amb2_x", Sort::Int);
    let ambient = terms.mk_fresh_named_var("fi_amb2_x", Sort::Int);
    assert_ne!(bound, ambient);
    let body = terms.mk_app(Symbol::named("fi_amb2_p"), [bound], Sort::Bool);
    let instance = terms.mk_app(Symbol::named("fi_amb2_p"), [ambient], Sort::Bool);
    let quantified = terms.mk_forall(vec![("fi_amb2_x".to_string(), Sort::Int)], body);
    let not_quantified = terms.mk_not_raw(quantified);
    let implication = terms.mk_app(Symbol::named("or"), [not_quantified, instance], Sort::Bool);

    validate_forall_inst(&terms, ProofId(0), &[implication], 0, &[ambient])
        .expect("a binder-free conclusion cannot capture, whatever the argument is spelled");
}

#[test]
fn forall_inst_rejects_an_argument_named_by_a_binder_the_body_rebinds() {
    // `forall ((x Int)) (and (p x) (forall ((x Int)) (q x)))` with argument `x`:
    // the body puts the spelling back in scope over a substitution site, so the
    // source-binder test stays in force here.
    let mut terms = TermStore::new();
    let x = terms.mk_var("fi_rebind_x", Sort::Int);
    let p_x = terms.mk_app(Symbol::named("fi_rebind_p"), [x], Sort::Bool);
    let q_x = terms.mk_app(Symbol::named("fi_rebind_q"), [x], Sort::Bool);
    let inner = terms.mk_forall(vec![("fi_rebind_x".to_string(), Sort::Int)], q_x);
    let body = terms.mk_app(Symbol::named("and"), [p_x, inner], Sort::Bool);
    let quantified = terms.mk_forall(vec![("fi_rebind_x".to_string(), Sort::Int)], body);
    let not_quantified = terms.mk_not_raw(quantified);
    let implication = terms.mk_app(Symbol::named("or"), [not_quantified, body], Sort::Bool);

    assert!(
        validate_forall_inst(&terms, ProofId(0), &[implication], 0, &[x]).is_err(),
        "a source binder the body re-binds is still in scope and must fail closed"
    );
}

// ── qnt_neg_exists (¬∃x⃗.φ ≡ ∀x⃗.¬φ) ─────────────────────────────────────

struct NegExistsFixture {
    terms: TermStore,
    exists: TermId,
    forall: TermId,
    binders: Vec<(String, Sort)>,
    body: TermId,
}

/// `E = (exists ((x U)(y U)) (not (s x y)))`,
/// `F = (forall ((x U)(y U)) (not (not (s x y))))`.
fn neg_exists_fixture() -> NegExistsFixture {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let binders = vec![("qx".to_string(), u.clone()), ("qy".to_string(), u.clone())];
    let x = terms.mk_var("qx", u.clone());
    let y = terms.mk_var("qy", u.clone());
    let s_xy = terms.mk_app(Symbol::named("s"), [x, y], Sort::Bool);
    // φ = (not (s x y)).
    let body = terms.mk_not_raw(s_xy);
    let exists = terms.mk_exists(binders.clone(), body);
    let neg_body = terms.mk_not_raw(body);
    let forall = terms.mk_forall(binders.clone(), neg_body);
    NegExistsFixture {
        terms,
        exists,
        forall,
        binders,
        body,
    }
}

#[test]
fn qnt_neg_exists_accepts_the_exact_dual() {
    let f = neg_exists_fixture();
    validate_qnt_neg_exists(&f.terms, ProofId(0), &[f.exists, f.forall], 0, &[])
        .expect("the exact De Morgan dual (cl E F) must validate");
}

#[test]
fn qnt_neg_exists_rejects_premises_or_args() {
    let f = neg_exists_fixture();
    assert!(
        validate_qnt_neg_exists(&f.terms, ProofId(0), &[f.exists, f.forall], 1, &[]).is_err(),
        "qnt_neg_exists is premiseless"
    );
    assert!(
        validate_qnt_neg_exists(&f.terms, ProofId(0), &[f.exists, f.forall], 0, &[f.exists])
            .is_err(),
        "qnt_neg_exists takes no :args"
    );
}

/// PRECONDITION: `F`'s body is the SINGLE negation of `E`'s body. Violating
/// it (body is `φ` itself, not `¬φ`) makes `(cl E F)` non-tautological and
/// the checker MUST reject.
#[test]
fn qnt_neg_exists_rejects_forall_body_that_is_not_the_negation() {
    let mut f = neg_exists_fixture();
    // F' = (forall (x⃗) φ) — body is φ, not ¬φ.
    let forged = f.terms.mk_forall(f.binders.clone(), f.body);
    assert!(
        validate_qnt_neg_exists(&f.terms, ProofId(0), &[f.exists, forged], 0, &[]).is_err(),
        "forall body must be exactly (not <exists body>)"
    );
}

#[test]
fn qnt_neg_exists_rejects_forall_body_without_a_not_wrapper() {
    let mut f = neg_exists_fixture();
    let TermData::Not(unwrapped) = f.terms.get(f.body) else {
        panic!("fixture body must be the explicit negation of s(x,y)");
    };
    let unwrapped = *unwrapped;
    let forged = f.terms.mk_forall(f.binders.clone(), unwrapped);
    assert!(
        validate_qnt_neg_exists(&f.terms, ProofId(0), &[f.exists, forged], 0, &[]).is_err(),
        "forall body must retain an explicit single Not wrapper"
    );
}

#[test]
fn qnt_neg_exists_rejects_an_empty_binder_vector() {
    let mut terms = TermStore::new();
    let body = terms.true_term();
    let exists = terms.mk_exists(Vec::new(), body);
    let neg_body = terms.mk_not_raw(body);
    let forall = terms.mk_forall(Vec::new(), neg_body);
    assert!(
        validate_qnt_neg_exists(&terms, ProofId(0), &[exists, forall], 0, &[]).is_err(),
        "the rule deliberately requires a non-empty quantifier binder"
    );
}

#[test]
fn qnt_neg_exists_rejects_a_non_boolean_exists_body() {
    let int_body = TermId::new(0);
    let negated_int_body = TermId::new(1);
    let exists = TermId::new(2);
    let forall = TermId::new(3);
    let binders = vec![("malformed_x".to_string(), Sort::Int)];
    let terms = TermStore::from_entries(
        vec![
            (TermData::Const(ay_core::Constant::Int(7.into())), Sort::Int),
            (TermData::Not(int_body), Sort::Bool),
            (
                TermData::Exists(binders.clone(), int_body, Vec::new()),
                Sort::Bool,
            ),
            (
                TermData::Forall(binders, negated_int_body, Vec::new()),
                Sort::Bool,
            ),
        ],
        None,
        None,
        0,
    );
    assert!(
        validate_qnt_neg_exists(&terms, ProofId(0), &[exists, forall], 0, &[]).is_err(),
        "release-mode malformed quantifiers must not acquire Boolean proof authority"
    );
}

/// PRECONDITION: the binder VECTORS are identical. A renamed binder frees
/// the body's variables and breaks `F = ¬E`; the checker MUST reject.
#[test]
fn qnt_neg_exists_rejects_renamed_binder() {
    let mut f = neg_exists_fixture();
    let u = Sort::Uninterpreted("U".to_string());
    // Same body ¬φ but binders (qz, qy) instead of (qx, qy).
    let neg_body = f.terms.mk_not_raw(f.body);
    let forged = f.terms.mk_forall(
        vec![("qz".to_string(), u.clone()), ("qy".to_string(), u)],
        neg_body,
    );
    assert!(
        validate_qnt_neg_exists(&f.terms, ProofId(0), &[f.exists, forged], 0, &[]).is_err(),
        "forall binders must match the exists binders exactly"
    );
}

/// PRECONDITION: the binder SORTS are identical. A widened sort changes the
/// quantified domain and breaks the duality; the checker MUST reject.
#[test]
fn qnt_neg_exists_rejects_mismatched_binder_sort() {
    let mut f = neg_exists_fixture();
    let u = Sort::Uninterpreted("U".to_string());
    let neg_body = f.terms.mk_not_raw(f.body);
    let forged = f.terms.mk_forall(
        vec![("qx".to_string(), u), ("qy".to_string(), Sort::Int)],
        neg_body,
    );
    assert!(
        validate_qnt_neg_exists(&f.terms, ProofId(0), &[f.exists, forged], 0, &[]).is_err(),
        "a binder sort mismatch must be rejected"
    );
}

/// A `forall` on the LEFT and `exists` on the RIGHT is not this rule.
#[test]
fn qnt_neg_exists_rejects_swapped_quantifier_order() {
    let f = neg_exists_fixture();
    assert!(
        validate_qnt_neg_exists(&f.terms, ProofId(0), &[f.forall, f.exists], 0, &[]).is_err(),
        "first literal must be the exists, second the forall"
    );
}

#[test]
fn qnt_neg_exists_rejects_wrong_literal_count() {
    let f = neg_exists_fixture();
    assert!(
        validate_qnt_neg_exists(&f.terms, ProofId(0), &[f.exists], 0, &[]).is_err(),
        "a one-literal clause is not the dual tautology"
    );
}

mod skolem_tests;
