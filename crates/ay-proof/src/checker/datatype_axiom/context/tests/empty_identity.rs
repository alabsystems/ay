// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The empty identity, the raw text of the SMT-LIB symbol `||`, passes or
//! fails the same exactness, duplicate, ambiguity and occurrence checks as any
//! other datatype member name.

use super::*;

fn signature(
    identity: &str,
    argument_sorts: Vec<Sort>,
    result_sort: Sort,
    nullary_term: Option<TermId>,
) -> DatatypeMemberSignature {
    DatatypeMemberSignature {
        identity: identity.into(),
        argument_sorts,
        result_sort,
        nullary_term,
    }
}

fn empty_carrier() -> Sort {
    Sort::Uninterpreted(String::new())
}

/// F1: datatype `""` with the nullary constructor `""` (tester `is-`) and the
/// constructor `mk` with selector `val: Int`. Returns the fixture and the
/// nullary constructor's bound term.
fn empty_constructor_fixture() -> (Fixture, TermId) {
    let mut terms = TermStore::new();
    let carrier = empty_carrier();
    let empty = terms.mk_fresh_named_var("", carrier.clone());
    let payload = terms.mk_var("payload", Sort::Int);
    let boxed = terms.mk_app(Symbol::named("mk"), [payload], carrier.clone());
    let _ = terms.mk_app(Symbol::named("is-"), [empty], Sort::Bool);
    let _ = terms.mk_app(Symbol::named("val"), [boxed], Sort::Int);
    let fixture = Fixture {
        terms,
        declarations: vec![(String::new(), vec![String::new(), "mk".into()])],
        selectors: vec![
            (String::new(), Vec::new()),
            ("mk".into(), vec!["val".into()]),
        ],
        signatures: vec![
            signature("", Vec::new(), carrier.clone(), Some(empty)),
            signature("is-", vec![carrier.clone()], Sort::Bool, None),
            signature("mk", vec![Sort::Int], carrier.clone(), None),
            signature("is-mk", vec![carrier.clone()], Sort::Bool, None),
            signature("val", vec![carrier], Sort::Int, None),
        ],
    };
    (fixture, empty)
}

/// F2: datatype `D` with the nullary constructor `nil` and the constructor
/// `mk` whose one selector `""` returns `Int`.
fn empty_selector_fixture() -> Fixture {
    let mut terms = TermStore::new();
    let carrier = Sort::Uninterpreted("D".into());
    let nil = terms.mk_fresh_named_var("nil", carrier.clone());
    let payload = terms.mk_var("payload", Sort::Int);
    let boxed = terms.mk_app(Symbol::named("mk"), [payload], carrier.clone());
    let _ = terms.mk_app(Symbol::named(""), [boxed], Sort::Int);
    Fixture {
        terms,
        declarations: vec![("D".into(), vec!["nil".into(), "mk".into()])],
        selectors: vec![
            ("nil".into(), Vec::new()),
            ("mk".into(), vec![String::new()]),
        ],
        signatures: vec![
            signature("nil", Vec::new(), carrier.clone(), Some(nil)),
            signature("is-nil", vec![carrier.clone()], Sort::Bool, None),
            signature("mk", vec![Sort::Int], carrier.clone(), None),
            signature("is-mk", vec![carrier.clone()], Sort::Bool, None),
            signature("", vec![carrier], Sort::Int, None),
        ],
    }
}

fn assert_reason(fixture: &Fixture, expected: &str) {
    let result = check(fixture, &mut |_, _| true);
    assert!(
        matches!(
            &result,
            Err(ProofCheckError::InvalidDatatypeSignatureContext { reason }) if reason == expected
        ),
        "expected {expected:?}, got {result:?}"
    );
}

#[test]
fn empty_symbol_members_authenticate_like_any_other() {
    let (constructor, _) = empty_constructor_fixture();
    for fixture in [constructor, empty_selector_fixture()] {
        check(&fixture, &mut |_, _| true).unwrap();
        validate_datatype_signature_context(
            &fixture.terms,
            Some(&fixture.declarations),
            Some(&fixture.selectors),
            &fixture.signatures,
        )
        .unwrap();
    }
}

#[test]
fn empty_symbol_extra_and_missing_members_fail_exactness() {
    // (a) "" sorts before every other name, so beside declared members an
    // undeclared "" signature is the first unequal pair of the ordered walk.
    let mut fixture = fixture();
    fixture
        .signatures
        .push(signature("", Vec::new(), Sort::Int, None));
    assert_reason(
        &fixture,
        "typed datatype member table is not exact (actual, expected): [\"\", \"is-meter-mk\"]",
    );
    let lone = Fixture {
        terms: TermStore::new(),
        declarations: Vec::new(),
        selectors: Vec::new(),
        signatures: vec![signature("", Vec::new(), Sort::Int, None)],
    };
    assert_reason(
        &lone,
        "typed datatype member table has an extra member: [\"\"]",
    );
    // (b) The declared "" constructor keeps its ("", []) selector entry but
    // has no signature, which `signatures::validate_declared` refuses.
    let (mut fixture, _) = empty_constructor_fixture();
    fixture.signatures.remove(0);
    assert_reason(
        &fixture,
        "datatype member is missing its exact typed signature: [\"\"]",
    );
}

#[test]
fn empty_symbol_duplicates_and_ambiguities_are_refused() {
    // (c) Two "" signatures.
    let (mut fixture, _) = empty_constructor_fixture();
    fixture.signatures.push(fixture.signatures[0].clone());
    assert_reason(&fixture, "datatype member signature is duplicated: [\"\"]");
    // (d) Constructor "" and selector "" share one term namespace.
    let (mut fixture, _) = empty_constructor_fixture();
    fixture.selectors[1].1[0].clear();
    assert_reason(&fixture, "datatype member identity is ambiguous: [\"\"]");
    // (e) The tester of constructor "" is `is-`, so a constructor `is-`
    // collides with it.
    let (mut fixture, _) = empty_constructor_fixture();
    fixture.declarations[0].1.push("is-".into());
    assert_reason(&fixture, "datatype member identity is ambiguous: [\"is-\"]");
    // (h) Two datatypes named "".
    let (mut fixture, _) = empty_constructor_fixture();
    fixture.declarations.push(fixture.declarations[0].clone());
    assert_reason(&fixture, "datatype declaration name is duplicated: [\"\"]");
    // Constructor "" declared by two datatypes.
    let (mut fixture, _) = empty_constructor_fixture();
    fixture.declarations.push(("E".into(), vec![String::new()]));
    assert_reason(
        &fixture,
        "constructor declaration name is duplicated: [\"\"]",
    );
}

#[test]
fn empty_symbol_occurrences_are_authenticated_against_their_signature() {
    // (f) A second variable spelled "" is not the bound nullary constructor.
    let (mut fixture, _) = empty_constructor_fixture();
    let _ = fixture.terms.mk_fresh_named_var("", empty_carrier());
    assert_reason(
        &fixture,
        "datatype member variable is not its declaration's exact nullary constructor binding: [\"\"]",
    );
    // (g) The nullary constructor "" applied to an argument.
    let (mut fixture, empty) = empty_constructor_fixture();
    let _ = fixture
        .terms
        .mk_app(Symbol::named(""), [empty], empty_carrier());
    assert_reason(
        &fixture,
        "datatype member application has an incorrect arity: [\"\"]",
    );
    // (g) The selector "" applied to a Bool instead of a `D`.
    let mut fixture = empty_selector_fixture();
    let wrong = fixture.terms.false_term();
    let _ = fixture.terms.mk_app(Symbol::named(""), [wrong], Sort::Int);
    assert_reason(
        &fixture,
        "datatype member application has an incorrect argument sort: [\"\"]",
    );
}
