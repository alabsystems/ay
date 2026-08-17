// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

type DatatypeNameTable = Vec<(String, Vec<String>)>;
type TypedColorFixture = (
    TermStore,
    Proof,
    DatatypeNameTable,
    DatatypeNameTable,
    Vec<DatatypeMemberSignature>,
    Vec<TermId>,
);
type TypedBoxContext = (
    DatatypeNameTable,
    DatatypeNameTable,
    Vec<DatatypeMemberSignature>,
);

fn typed_color_distinct_fixture() -> TypedColorFixture {
    let mut terms = TermStore::new();
    let color = Sort::Uninterpreted("TypedColor".to_string());
    let red = terms.mk_fresh_named_var("typed-red", color.clone());
    let green = terms.mk_fresh_named_var("typed-green", color.clone());
    let equality = terms.mk_app(Symbol::named("="), [red, green], Sort::Bool);
    let disequality = terms.mk_not_raw(equality);
    let mut proof = Proof::new();
    let theorem = proof.add_theory_lemma_with_kind(
        "DT",
        vec![disequality],
        TheoryLemmaKind::DatatypeDistinct,
    );
    let assumption = proof.add_assume(equality, None);
    proof.add_resolution(Vec::new(), equality, theorem, assumption);
    let declarations = vec![(
        "TypedColor".to_string(),
        vec!["typed-red".to_string(), "typed-green".to_string()],
    )];
    let selectors = vec![
        ("typed-red".to_string(), Vec::new()),
        ("typed-green".to_string(), Vec::new()),
    ];
    let signatures = vec![
        DatatypeMemberSignature {
            identity: "typed-red".to_string(),
            argument_sorts: Vec::new(),
            result_sort: color.clone(),
            nullary_term: Some(red),
        },
        DatatypeMemberSignature {
            identity: "is-typed-red".to_string(),
            argument_sorts: vec![color.clone()],
            result_sort: Sort::Bool,
            nullary_term: None,
        },
        DatatypeMemberSignature {
            identity: "typed-green".to_string(),
            argument_sorts: Vec::new(),
            result_sort: color.clone(),
            nullary_term: Some(green),
        },
        DatatypeMemberSignature {
            identity: "is-typed-green".to_string(),
            argument_sorts: vec![color],
            result_sort: Sort::Bool,
            nullary_term: None,
        },
    ];
    (
        terms,
        proof,
        declarations,
        selectors,
        signatures,
        vec![equality],
    )
}

#[test]
fn typed_datatype_context_accepts_exact_signatures_and_legacy_context_fails_closed() {
    let (terms, proof, declarations, selectors, signatures, assertions) =
        typed_color_distinct_fixture();
    let quality = check_proof_strict_with_typed_context(
        &proof,
        &terms,
        Some(&declarations),
        Some(&selectors),
        &signatures,
        Some(&assertions),
    )
    .expect("an exact typed datatype context must authorize the genuine theorem");
    assert!(quality.is_complete());

    assert!(matches!(
        check_proof_strict_with_context(
            &proof,
            &terms,
            Some(&declarations),
            Some(&selectors),
            Some(&assertions),
        ),
        Err(ProofCheckError::UnsupportedTheoryLemmaKind { .. })
    ));
    assert!(matches!(
        crate::check_proof_collecting_trust_with_context(
            &proof,
            &terms,
            Some(&declarations),
            Some(&selectors),
            Some(&assertions),
        ),
        Err(ProofCheckError::UnsupportedTheoryLemmaKind { .. })
    ));
}

#[test]
fn typed_datatype_context_rejects_incomplete_duplicate_extra_and_conflicting_tables() {
    let (terms, proof, declarations, selectors, signatures, assertions) =
        typed_color_distinct_fixture();
    let check = |candidate: &[DatatypeMemberSignature]| {
        check_proof_strict_with_typed_context(
            &proof,
            &terms,
            Some(&declarations),
            Some(&selectors),
            candidate,
            Some(&assertions),
        )
    };

    assert!(matches!(
        check(&signatures[..signatures.len() - 1]),
        Err(ProofCheckError::InvalidDatatypeSignatureContext { .. })
    ));
    let mut duplicate = signatures.clone();
    duplicate.push(signatures[0].clone());
    assert!(matches!(
        check(&duplicate),
        Err(ProofCheckError::InvalidDatatypeSignatureContext { .. })
    ));
    let mut extra = signatures.clone();
    extra.push(DatatypeMemberSignature {
        identity: "not-a-member".to_string(),
        argument_sorts: Vec::new(),
        result_sort: Sort::Bool,
        nullary_term: None,
    });
    assert!(matches!(
        check(&extra),
        Err(ProofCheckError::InvalidDatatypeSignatureContext { .. })
    ));
    let mut conflicting = signatures.clone();
    conflicting[0].result_sort = Sort::Int;
    assert!(matches!(
        check(&conflicting),
        Err(ProofCheckError::InvalidDatatypeSignatureContext { .. })
    ));
}

#[test]
fn typed_datatype_context_rejects_shadow_of_exact_nullary_constructor_binding() {
    let (mut terms, proof, declarations, selectors, signatures, assertions) =
        typed_color_distinct_fixture();
    let _shadow =
        terms.mk_fresh_named_var("typed-red", Sort::Uninterpreted("TypedColor".to_string()));
    assert!(matches!(
        check_proof_strict_with_typed_context(
            &proof,
            &terms,
            Some(&declarations),
            Some(&selectors),
            &signatures,
            Some(&assertions),
        ),
        Err(ProofCheckError::InvalidDatatypeSignatureContext { .. })
    ));
}

fn typed_box_context() -> TypedBoxContext {
    let carrier = Sort::Uninterpreted("TypedBox".to_string());
    (
        vec![("TypedBox".to_string(), vec!["typed-mk".to_string()])],
        vec![("typed-mk".to_string(), vec!["typed-value".to_string()])],
        vec![
            DatatypeMemberSignature {
                identity: "typed-mk".to_string(),
                argument_sorts: vec![Sort::Int],
                result_sort: carrier.clone(),
                nullary_term: None,
            },
            DatatypeMemberSignature {
                identity: "is-typed-mk".to_string(),
                argument_sorts: vec![carrier.clone()],
                result_sort: Sort::Bool,
                nullary_term: None,
            },
            DatatypeMemberSignature {
                identity: "typed-value".to_string(),
                argument_sorts: vec![carrier],
                result_sort: Sort::Int,
                nullary_term: None,
            },
        ],
    )
}

fn assert_typed_context_rejects_store(terms: &TermStore) {
    let (declarations, selectors, signatures) = typed_box_context();
    let error = validate_datatype_signature_context(
        terms,
        Some(&declarations),
        Some(&selectors),
        &signatures,
    )
    .expect_err("a mistyped datatype member occurrence must fail global preflight");
    assert!(matches!(
        error,
        ProofCheckError::InvalidDatatypeSignatureContext { .. }
    ));
}

#[test]
fn typed_datatype_context_rejects_wrong_constructor_argument_and_nonnullary_var() {
    let carrier = Sort::Uninterpreted("TypedBox".to_string());
    let mut wrong_argument = TermStore::new();
    let box_value = wrong_argument.mk_var("box-value", carrier.clone());
    let _ = wrong_argument.mk_app(Symbol::named("typed-mk"), [box_value], carrier.clone());
    assert_typed_context_rejects_store(&wrong_argument);

    let mut nonnullary_var = TermStore::new();
    let _ = nonnullary_var.mk_var("typed-mk", carrier);
    assert_typed_context_rejects_store(&nonnullary_var);
}

#[test]
fn typed_datatype_context_rejects_wrong_selector_input_result_and_indexed_member() {
    let carrier = Sort::Uninterpreted("TypedBox".to_string());
    let mut wrong_input = TermStore::new();
    let int_value = wrong_input.mk_var("int-value", Sort::Int);
    let _ = wrong_input.mk_app(Symbol::named("typed-value"), [int_value], Sort::Int);
    assert_typed_context_rejects_store(&wrong_input);

    let mut wrong_result = TermStore::new();
    let box_value = wrong_result.mk_var("box-value", carrier.clone());
    let _ = wrong_result.mk_app(Symbol::named("typed-value"), [box_value], carrier.clone());
    assert_typed_context_rejects_store(&wrong_result);

    let mut indexed = TermStore::new();
    let int_value = indexed.mk_var("int-value", Sort::Int);
    let _ = indexed.mk_app(Symbol::indexed("typed-mk", vec![0]), [int_value], carrier);
    assert_typed_context_rejects_store(&indexed);
}

/// A nullary constructor has TWO authenticated core representations and the
/// strict checker must accept both.
///
/// `declare-datatype` binds the constructor as an exact `Var` (the signature's
/// `nullary_term`); the embedder path `try_declare_fun(C, &[], dt)` +
/// `try_apply(&C, &[])` — and the SMT-LIB `(C)` spelling — instead build a
/// ZERO-ARGUMENT `App(Named(C), [])`. `euf::dt` classifies any named
/// application whose head `is_constructor` as a constructor term, arity 0
/// included, so both forms mean the constructor to the solver. Rejecting the
/// application form declined five correct `pushscope_repro` refutations.
///
/// Authority still comes from the exact member identity, exactly as it already
/// does for every non-nullary constructor, selector, and tester application.
#[test]
fn typed_datatype_context_accepts_nullary_constructor_application_form() {
    let color = Sort::Uninterpreted("TypedColor".to_string());
    let mut terms = TermStore::new();
    let red = terms.mk_fresh_named_var("typed-red", color.clone());
    let green = terms.mk_fresh_named_var("typed-green", color.clone());
    // The same nullary constructor, spelled as a zero-argument application.
    let red_app = terms.mk_app(
        Symbol::named("typed-red"),
        Vec::<TermId>::new(),
        color.clone(),
    );
    assert_ne!(
        red, red_app,
        "the two representations must be distinct terms"
    );
    let _ = terms.mk_app(Symbol::named("="), [red_app, green], Sort::Bool);

    let (declarations, selectors, signatures) = typed_color_context(red, green, &color);
    validate_datatype_signature_context(&terms, Some(&declarations), Some(&selectors), &signatures)
        .expect("a zero-argument application of a nullary constructor is the constructor");
}

/// The relaxation above is exactly one representation, not a hole: a nullary
/// constructor applied to arguments, applied at the wrong result sort, or a
/// same-spelling variable that is NOT the pinned binding all still fail closed.
/// The last one is the shadowing guard the `nullary_term` pin exists for.
#[test]
fn typed_datatype_context_still_rejects_misapplied_and_shadowed_nullary_constructors() {
    let color = Sort::Uninterpreted("TypedColor".to_string());

    let assert_rejects = |terms: &TermStore, red: TermId, green: TermId| {
        let (declarations, selectors, signatures) = typed_color_context(red, green, &color);
        let error = validate_datatype_signature_context(
            terms,
            Some(&declarations),
            Some(&selectors),
            &signatures,
        )
        .expect_err("a malformed nullary-constructor occurrence must fail global preflight");
        assert!(matches!(
            error,
            ProofCheckError::InvalidDatatypeSignatureContext { .. }
        ));
    };

    let mut applied = TermStore::new();
    let red = applied.mk_fresh_named_var("typed-red", color.clone());
    let green = applied.mk_fresh_named_var("typed-green", color.clone());
    let _ = applied.mk_app(Symbol::named("typed-red"), [green], color.clone());
    assert_rejects(&applied, red, green);

    let mut wrong_sort = TermStore::new();
    let red = wrong_sort.mk_fresh_named_var("typed-red", color.clone());
    let green = wrong_sort.mk_fresh_named_var("typed-green", color.clone());
    let _ = wrong_sort.mk_app(Symbol::named("typed-red"), Vec::<TermId>::new(), Sort::Int);
    assert_rejects(&wrong_sort, red, green);

    let mut shadowed = TermStore::new();
    let red = shadowed.mk_fresh_named_var("typed-red", color.clone());
    let green = shadowed.mk_fresh_named_var("typed-green", color.clone());
    let _ = shadowed.mk_fresh_named_var("typed-red", color.clone());
    assert_rejects(&shadowed, red, green);
}

/// Exact declaration/selector/signature tables for the two-constructor
/// `TypedColor` enum, with `red`/`green` as the pinned nullary bindings.
fn typed_color_context(
    red: TermId,
    green: TermId,
    color: &Sort,
) -> (
    DatatypeNameTable,
    DatatypeNameTable,
    Vec<DatatypeMemberSignature>,
) {
    let declarations = vec![(
        "TypedColor".to_string(),
        vec!["typed-red".to_string(), "typed-green".to_string()],
    )];
    let selectors = vec![
        ("typed-red".to_string(), Vec::new()),
        ("typed-green".to_string(), Vec::new()),
    ];
    let signatures = vec![
        DatatypeMemberSignature {
            identity: "typed-red".to_string(),
            argument_sorts: Vec::new(),
            result_sort: color.clone(),
            nullary_term: Some(red),
        },
        DatatypeMemberSignature {
            identity: "is-typed-red".to_string(),
            argument_sorts: vec![color.clone()],
            result_sort: Sort::Bool,
            nullary_term: None,
        },
        DatatypeMemberSignature {
            identity: "typed-green".to_string(),
            argument_sorts: Vec::new(),
            result_sort: color.clone(),
            nullary_term: Some(green),
        },
        DatatypeMemberSignature {
            identity: "is-typed-green".to_string(),
            argument_sorts: vec![color.clone()],
            result_sort: Sort::Bool,
            nullary_term: None,
        },
    ];
    (declarations, selectors, signatures)
}
