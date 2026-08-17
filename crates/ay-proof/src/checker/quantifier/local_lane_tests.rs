// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{FarkasAnnotation, LiaAnnotation, Sort, Symbol, TheoryLemmaKind};

use super::*;

#[test]
fn forall_inst_accepts_exact_substitution_under_nested_binder() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("fi_outer_x", Sort::Int);
    let y = terms.mk_var("fi_inner_y", Sort::Int);
    let body = terms.mk_app(Symbol::named("fi_nested_p"), [x, y], Sort::Bool);
    let nested = terms.mk_forall(vec![("fi_inner_y".to_string(), Sort::Int)], body);
    let quantified = terms.mk_forall(vec![("fi_outer_x".to_string(), Sort::Int)], nested);

    let value = terms.mk_int(7.into());
    let instance_body = terms.mk_app(Symbol::named("fi_nested_p"), [value, y], Sort::Bool);
    let instance = terms.mk_forall(vec![("fi_inner_y".to_string(), Sort::Int)], instance_body);
    let not_quantified = terms.mk_not_raw(quantified);
    let implication = terms.mk_app(Symbol::named("or"), [not_quantified, instance], Sort::Bool);

    validate_forall_inst(&terms, ProofId(0), &[implication], 0, &[value])
        .expect("capture-free substitution below a preserved nested binder must validate");
}

#[test]
fn forall_inst_preserves_shadowing_nested_binder() {
    let mut terms = TermStore::new();
    let inner_x = terms.mk_var("fi_shadowed_x", Sort::Int);
    let inner_body = terms.mk_app(Symbol::named("fi_shadowed_p"), [inner_x], Sort::Bool);
    let nested = terms.mk_forall(vec![("fi_shadowed_x".to_string(), Sort::Int)], inner_body);
    let quantified = terms.mk_forall(vec![("fi_shadowed_x".to_string(), Sort::Int)], nested);
    let value = terms.mk_int(0.into());
    let not_quantified = terms.mk_not_raw(quantified);
    let implication = terms.mk_app(Symbol::named("or"), [not_quantified, nested], Sort::Bool);

    validate_forall_inst(&terms, ProofId(0), &[implication], 0, &[value])
        .expect("an inner binder with the same name must mask the outer substitution");
}

#[test]
fn forall_inst_rejects_nested_partial_substitution_and_capture() {
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

    let captured_body = terms.mk_app(Symbol::named("nested_p"), [inner_x, inner_x], Sort::Bool);
    let captured_instance =
        terms.mk_forall(vec![("inner_x".to_string(), Sort::Int)], captured_body);
    let captured_implication = terms.mk_app(
        Symbol::named("or"),
        [not_quantified, captured_instance],
        Sort::Bool,
    );
    assert!(
        validate_forall_inst(&terms, ProofId(0), &[captured_implication], 0, &[inner_x],).is_err(),
        "a free argument name must not be captured by a nested binder"
    );
}

#[test]
fn negated_exists_dual_accepts_exact_nnf_bridge_and_rejects_forgery() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("dual_x", Sort::Int);
    let p_x = terms.mk_app(Symbol::named("dual_p"), [x], Sort::Bool);
    let not_p_x = terms.mk_not_raw(p_x);
    let exists = terms.mk_exists_with_triggers(
        vec![("dual_x".to_string(), Sort::Int)],
        not_p_x,
        vec![vec![p_x]],
    );
    let source = terms.mk_not_raw(exists);
    let not_source = terms.mk_not_raw(source);
    let dual = terms.mk_forall_with_triggers(
        vec![("dual_x".to_string(), Sort::Int)],
        p_x,
        vec![vec![p_x]],
    );
    validate_negated_exists_dual(&terms, ProofId(0), &[not_source, dual])
        .expect("the exact one-step NNF dual must validate");

    assert!(validate_negated_exists_dual(&terms, ProofId(0), &[]).is_err());
    assert!(validate_negated_exists_dual(&terms, ProofId(0), &[not_source, dual, dual]).is_err());
    assert!(
        validate_negated_exists_dual(&terms, ProofId(0), &[dual, not_source]).is_err(),
        "literal order is part of the exact bridge schema"
    );
    assert!(
        validate_negated_exists_dual(&terms, ProofId(0), &[source, dual]).is_err(),
        "the first literal must negate the complete authored source"
    );

    let empty_exists = terms.mk_exists(Vec::new(), not_p_x);
    let empty_source = terms.mk_not_raw(empty_exists);
    let not_empty_source = terms.mk_not_raw(empty_source);
    let empty_dual = terms.mk_forall(Vec::new(), p_x);
    assert!(
        validate_negated_exists_dual(&terms, ProofId(0), &[not_empty_source, empty_dual],).is_err(),
        "an empty binding list is outside the quantified dual lane"
    );

    let q_x = terms.mk_app(Symbol::named("dual_q"), [x], Sort::Bool);
    let forged_body = terms.mk_forall_with_triggers(
        vec![("dual_x".to_string(), Sort::Int)],
        q_x,
        vec![vec![p_x]],
    );
    assert!(validate_negated_exists_dual(&terms, ProofId(0), &[not_source, forged_body]).is_err());
    let forged_binder = terms.mk_forall_with_triggers(
        vec![("dual_y".to_string(), Sort::Int)],
        p_x,
        vec![vec![p_x]],
    );
    assert!(
        validate_negated_exists_dual(&terms, ProofId(0), &[not_source, forged_binder]).is_err()
    );
    let forged_trigger = terms.mk_forall_with_triggers(
        vec![("dual_x".to_string(), Sort::Int)],
        p_x,
        vec![vec![q_x]],
    );
    assert!(
        validate_negated_exists_dual(&terms, ProofId(0), &[not_source, forged_trigger]).is_err()
    );

    let mut with_farkas = Proof::new();
    with_farkas.add_theory_lemma_with_farkas_and_kind(
        "QUANT",
        vec![not_source, dual],
        FarkasAnnotation::from_ints(&[1, 1]),
        TheoryLemmaKind::QuantifierNegatedExistsDual,
    );
    assert!(matches!(
        crate::check_proof_strict(&with_farkas, &terms),
        Err(ProofCheckError::InvalidTheoryLemma { ref reason, .. })
            if reason.contains("must not carry unrelated Farkas/LIA evidence")
    ));

    let mut with_lia = Proof::new();
    with_lia.add_theory_lemma_with_lia(
        "QUANT",
        vec![not_source, dual],
        None,
        TheoryLemmaKind::QuantifierNegatedExistsDual,
        LiaAnnotation::LinearIdentity,
    );
    assert!(matches!(
        crate::check_proof_strict(&with_lia, &terms),
        Err(ProofCheckError::InvalidTheoryLemma { ref reason, .. })
            if reason.contains("must not carry unrelated Farkas/LIA evidence")
    ));
}
