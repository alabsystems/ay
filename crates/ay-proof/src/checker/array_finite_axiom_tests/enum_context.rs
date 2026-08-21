// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Authenticated enum-carrier finite-array schema tests.

use super::*;
use ay_core::{DatatypeConstructor, DatatypeSort};

struct EnumFixture {
    terms: TermStore,
    index_sort: Sort,
    members: Vec<TermId>,
    datatype_declarations: Vec<(String, Vec<String>)>,
    constructor_selectors: Vec<(String, Vec<String>)>,
    member_signatures: Vec<DatatypeMemberSignature>,
}

impl EnumFixture {
    fn new() -> Self {
        let datatype = "FiniteColor".to_string();
        let constructors = vec![
            "FiniteRed".to_string(),
            "FiniteGreen".to_string(),
            "FiniteBlue".to_string(),
        ];
        let index_sort = Sort::Uninterpreted(datatype.clone());
        Self::with_index_sort(datatype, constructors, index_sort)
    }

    fn with_index_sort(datatype: String, constructors: Vec<String>, index_sort: Sort) -> Self {
        let mut terms = TermStore::new();
        let members: Vec<TermId> = constructors
            .iter()
            .map(|constructor| terms.mk_var(constructor.clone(), index_sort.clone()))
            .collect();
        let member_signatures = constructors
            .iter()
            .zip(members.iter().copied())
            .flat_map(|(constructor, member)| {
                [
                    DatatypeMemberSignature {
                        identity: constructor.clone(),
                        argument_sorts: Vec::new(),
                        result_sort: index_sort.clone(),
                        nullary_term: Some(member),
                    },
                    DatatypeMemberSignature {
                        identity: format!("is-{constructor}"),
                        argument_sorts: vec![index_sort.clone()],
                        result_sort: Sort::Bool,
                        nullary_term: None,
                    },
                ]
            })
            .collect();
        let constructor_selectors = constructors
            .iter()
            .cloned()
            .map(|constructor| (constructor, Vec::new()))
            .collect();
        Self {
            terms,
            index_sort,
            members,
            datatype_declarations: vec![(datatype, constructors)],
            constructor_selectors,
            member_signatures,
        }
    }

    fn recognize_extensionality(&self, axiom: TermId) -> bool {
        recognize_array_finite_extensionality_with_typed_context(
            &self.terms,
            &[axiom],
            &self.datatype_declarations,
            &self.constructor_selectors,
            &self.member_signatures,
        )
    }

    fn recognize_select_expansion(&self, axiom: TermId) -> bool {
        recognize_array_finite_select_expansion_with_typed_context(
            &self.terms,
            &[axiom],
            &self.datatype_declarations,
            &self.constructor_selectors,
            &self.member_signatures,
        )
    }
}

fn validate_strict_typed(
    fixture: &EnumFixture,
    axiom: TermId,
    kind: TheoryLemmaKind,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::TheoryLemma {
        theory: "arrays".to_string(),
        clause: vec![axiom],
        farkas: None,
        kind,
        lia: None,
    };
    let mut derived = Vec::new();
    validate_step_with_datatypes(
        &fixture.terms,
        &mut derived,
        ProofId(0),
        &step,
        true,
        Some(fixture.datatype_declarations.as_slice()),
        Some(fixture.constructor_selectors.as_slice()),
        Some(fixture.member_signatures.as_slice()),
        None,
        None,
        None,
        None,
    )
}

#[test]
fn finite_extensionality_requires_and_accepts_authenticated_enum_context() {
    let mut fixture = EnumFixture::new();
    let sort = Sort::array(fixture.index_sort.clone(), Sort::Int);
    let array_a = fixture.terms.mk_var("finite_enum_a", sort.clone());
    let array_b = fixture.terms.mk_var("finite_enum_b", sort);
    let axiom = finite_extensionality(&mut fixture.terms, array_a, array_b, &fixture.members);

    assert!(!recognize_array_finite_extensionality(
        &fixture.terms,
        &[axiom]
    ));
    validate_strict(
        &fixture.terms,
        axiom,
        TheoryLemmaKind::ArrayFiniteExtensionality,
    )
    .expect_err("an enum-shaped term store without authenticated declarations fails closed");
    assert!(fixture.recognize_extensionality(axiom));
    assert_eq!(
        recognize_array_theory_lemma_with_typed_context(
            &fixture.terms,
            &[axiom],
            &fixture.datatype_declarations,
            &fixture.constructor_selectors,
            &fixture.member_signatures,
        ),
        Some(TheoryLemmaKind::ArrayFiniteExtensionality)
    );
    validate_strict_typed(&fixture, axiom, TheoryLemmaKind::ArrayFiniteExtensionality)
        .expect("the typed enum registry authenticates the complete carrier");

    let not_axiom = fixture.terms.mk_not_raw(axiom);
    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind(
        "arrays",
        vec![axiom],
        TheoryLemmaKind::ArrayFiniteExtensionality,
    );
    let premise = proof.add_assume(not_axiom, None);
    proof.add_resolution(Vec::new(), axiom, lemma, premise);
    let quality = crate::check_proof_strict_with_typed_context(
        &proof,
        &fixture.terms,
        Some(&fixture.datatype_declarations),
        Some(&fixture.constructor_selectors),
        &fixture.member_signatures,
        None,
    )
    .expect("the whole-proof typed entry point authenticates the enum context");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn finite_extensionality_rejects_enum_constructor_omission() {
    let mut fixture = EnumFixture::new();
    let sort = Sort::array(fixture.index_sort.clone(), Sort::Int);
    let array_a = fixture.terms.mk_var("finite_enum_missing_a", sort.clone());
    let array_b = fixture.terms.mk_var("finite_enum_missing_b", sort);
    let axiom = finite_extensionality(&mut fixture.terms, array_a, array_b, &fixture.members[..2]);

    assert!(!fixture.recognize_extensionality(axiom));
    validate_strict_typed(&fixture, axiom, TheoryLemmaKind::ArrayFiniteExtensionality)
        .expect_err("omitting one authenticated constructor must fail closed");
}

#[test]
fn finite_array_schemas_reject_a_field_bearing_datatype() {
    let mut fixture = EnumFixture::new();
    fixture.constructor_selectors[0]
        .1
        .push("finite_payload".to_string());
    let sort = Sort::array(fixture.index_sort.clone(), Sort::Int);
    let array_a = fixture.terms.mk_var("finite_non_enum_a", sort.clone());
    let array_b = fixture.terms.mk_var("finite_non_enum_b", sort);
    let axiom = finite_extensionality(&mut fixture.terms, array_a, array_b, &fixture.members);

    assert!(!fixture.recognize_extensionality(axiom));
    validate_strict_typed(&fixture, axiom, TheoryLemmaKind::ArrayFiniteExtensionality)
        .expect_err("a constructor with a selector is not an enum carrier");
}

#[test]
fn finite_array_schemas_reject_duplicate_native_constructor_metadata() {
    let datatype = "FiniteColor".to_string();
    let constructors = vec![
        "FiniteRed".to_string(),
        "FiniteGreen".to_string(),
        "FiniteBlue".to_string(),
    ];
    let forged_sort = Sort::Datatype(DatatypeSort::new(
        datatype.clone(),
        vec![
            DatatypeConstructor::unit("FiniteRed"),
            DatatypeConstructor::unit("FiniteRed"),
            DatatypeConstructor::unit("FiniteBlue"),
        ],
    ));
    let mut fixture = EnumFixture::with_index_sort(datatype, constructors, forged_sort);
    let sort = Sort::array(fixture.index_sort.clone(), Sort::Int);
    let array_a = fixture.terms.mk_var("finite_native_dup_a", sort.clone());
    let array_b = fixture.terms.mk_var("finite_native_dup_b", sort);
    let axiom = finite_extensionality(&mut fixture.terms, array_a, array_b, &fixture.members);

    assert!(!fixture.recognize_extensionality(axiom));
    validate_strict_typed(&fixture, axiom, TheoryLemmaKind::ArrayFiniteExtensionality)
        .expect_err("duplicate rich-sort constructor metadata cannot stand in for a full enum");
}

#[test]
fn finite_select_expansion_requires_and_accepts_complete_enum_context() {
    let mut fixture = EnumFixture::new();
    let sort = Sort::array(fixture.index_sort.clone(), Sort::Int);
    let array = fixture.terms.mk_var("finite_enum_select_a", sort);
    let index = fixture
        .terms
        .mk_var("finite_enum_select_i", fixture.index_sort.clone());
    let symbolic_select = fixture.terms.mk_select(array, index);
    let mut expansion = fixture
        .terms
        .mk_select(array, *fixture.members.last().expect("three enum members"));
    for &member in fixture.members[..fixture.members.len() - 1].iter().rev() {
        let condition = fixture.terms.mk_eq(index, member);
        let branch = fixture.terms.mk_select(array, member);
        expansion = fixture.terms.mk_ite(condition, branch, expansion);
    }
    let axiom = fixture.terms.mk_eq(symbolic_select, expansion);

    assert!(!recognize_array_finite_select_expansion(
        &fixture.terms,
        &[axiom]
    ));
    validate_strict(
        &fixture.terms,
        axiom,
        TheoryLemmaKind::ArrayFiniteSelectExpansion,
    )
    .expect_err("an enum expansion without authenticated declarations fails closed");
    assert!(fixture.recognize_select_expansion(axiom));
    validate_strict_typed(&fixture, axiom, TheoryLemmaKind::ArrayFiniteSelectExpansion)
        .expect("the complete authenticated enum ITE is exact");
}

#[test]
fn finite_select_expansion_rejects_partial_enum_chain() {
    let mut fixture = EnumFixture::new();
    let sort = Sort::array(fixture.index_sort.clone(), Sort::Int);
    let array = fixture.terms.mk_var("finite_enum_partial_a", sort);
    let index = fixture
        .terms
        .mk_var("finite_enum_partial_i", fixture.index_sort.clone());
    let symbolic_select = fixture.terms.mk_select(array, index);
    let red = fixture.members[0];
    let green = fixture.members[1];
    let condition = fixture.terms.mk_eq(index, red);
    let red_select = fixture.terms.mk_select(array, red);
    let green_select = fixture.terms.mk_select(array, green);
    let partial = fixture.terms.mk_ite(condition, red_select, green_select);
    let axiom = fixture.terms.mk_eq(symbolic_select, partial);

    assert!(!fixture.recognize_select_expansion(axiom));
    validate_strict_typed(&fixture, axiom, TheoryLemmaKind::ArrayFiniteSelectExpansion)
        .expect_err("the final enum constructor cannot be omitted");
}
