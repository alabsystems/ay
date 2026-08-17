// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict positive and forgery tests for the two complete finite-array schemas.

use crate::checker::*;
use ay_core::{
    ArraySort, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind,
};
use num_bigint::BigInt;

mod enum_context;

fn equality(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![left, right], Sort::Bool)
}

fn select(terms: &mut TermStore, array: TermId, index: TermId) -> TermId {
    let element_sort = match terms.sort(array).array_element() {
        Some(sort) => sort.clone(),
        None => Sort::Bool,
    };
    terms.mk_app(Symbol::named("select"), vec![array, index], element_sort)
}

fn finite_extensionality(
    terms: &mut TermStore,
    array_a: TermId,
    array_b: TermId,
    indices: &[TermId],
) -> TermId {
    let array_equality = terms.mk_eq(array_a, array_b);
    let pointwise: Vec<TermId> = indices
        .iter()
        .map(|&index| {
            let left = terms.mk_select(array_a, index);
            let right = terms.mk_select(array_b, index);
            terms.mk_eq(left, right)
        })
        .collect();
    let conjunction = terms.mk_and(pointwise);
    terms.mk_eq(array_equality, conjunction)
}

fn validate_strict(
    terms: &TermStore,
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
    validate_step(terms, &mut derived, ProofId(0), &step, true, None)
}

#[test]
fn finite_extensionality_accepts_complete_bool_carrier() {
    let mut terms = TermStore::new();
    let sort = Sort::Array(Box::new(ArraySort::new(Sort::Bool, Sort::Int)));
    let array_a = terms.mk_var("finite_bool_a", sort.clone());
    let array_b = terms.mk_var("finite_bool_b", sort);
    let false_term = terms.mk_bool(false);
    let true_term = terms.mk_bool(true);
    let axiom = finite_extensionality(&mut terms, array_a, array_b, &[false_term, true_term]);

    assert!(recognize_array_finite_extensionality(&terms, &[axiom]));
    assert_eq!(
        recognize_array_theory_lemma(&terms, &[axiom]),
        Some(TheoryLemmaKind::ArrayFiniteExtensionality)
    );
    validate_strict(&terms, axiom, TheoryLemmaKind::ArrayFiniteExtensionality)
        .expect("the complete Bool carrier is exact");
}

#[test]
fn finite_array_kind_is_complete_native_quality_not_trust() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Bool, Sort::Int);
    let array_a = terms.mk_var("finite_quality_a", sort.clone());
    let array_b = terms.mk_var("finite_quality_b", sort);
    let false_term = terms.mk_bool(false);
    let true_term = terms.mk_bool(true);
    let axiom = finite_extensionality(&mut terms, array_a, array_b, &[false_term, true_term]);
    let not_axiom = terms.mk_not_raw(axiom);

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind(
        "arrays",
        vec![axiom],
        TheoryLemmaKind::ArrayFiniteExtensionality,
    );
    let premise = proof.add_assume(not_axiom, None);
    proof.add_resolution(Vec::new(), axiom, lemma, premise);

    let quality = crate::check_proof_strict(&proof, &terms)
        .expect("the finite-array rule is fully native-checkable");
    assert!(quality.is_complete());
    assert_eq!(quality.theory_lemma_count, 1);
    assert_eq!(quality.trust_count, 0);
    assert!(quality.trust_theory_kinds.is_empty());
}

#[test]
fn finite_extensionality_accepts_every_bv2_point() {
    let mut terms = TermStore::new();
    let index_sort = Sort::bitvec(2);
    let sort = Sort::array(index_sort, Sort::Int);
    let array_a = terms.mk_var("finite_bv_a", sort.clone());
    let array_b = terms.mk_var("finite_bv_b", sort);
    let indices: Vec<_> = (0..4)
        .map(|value| terms.mk_bitvec(BigInt::from(value), 2))
        .collect();
    let axiom = finite_extensionality(&mut terms, array_a, array_b, &indices);

    assert!(recognize_array_finite_extensionality(&terms, &[axiom]));
    validate_strict(&terms, axiom, TheoryLemmaKind::ArrayFiniteExtensionality)
        .expect("all four BV2 points are present");
}

#[test]
fn finite_extensionality_rejects_even_complete_bv9_carrier() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(9), Sort::Int);
    let array_a = terms.mk_var("finite_bv9_a", sort.clone());
    let array_b = terms.mk_var("finite_bv9_b", sort);
    let indices: Vec<_> = (0..512)
        .map(|value| terms.mk_bitvec(BigInt::from(value), 9))
        .collect();
    let axiom = finite_extensionality(&mut terms, array_a, array_b, &indices);

    assert!(!recognize_array_finite_extensionality(&terms, &[axiom]));
    validate_strict(&terms, axiom, TheoryLemmaKind::ArrayFiniteExtensionality)
        .expect_err("the strict schema must retain the producer's width-8 cap");
}

#[test]
fn finite_extensionality_rejects_missing_and_duplicate_bool_points() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Bool, Sort::Int);
    let array_a = terms.mk_var("finite_missing_a", sort.clone());
    let array_b = terms.mk_var("finite_missing_b", sort);
    let false_term = terms.mk_bool(false);
    let array_equality = terms.mk_eq(array_a, array_b);
    let left = terms.mk_select(array_a, false_term);
    let right = terms.mk_select(array_b, false_term);
    let cell = terms.mk_eq(left, right);
    let missing = equality(&mut terms, array_equality, cell);
    let duplicate_conjunction = terms.mk_app(Symbol::named("and"), vec![cell, cell], Sort::Bool);
    let duplicate = equality(&mut terms, array_equality, duplicate_conjunction);

    for forged in [missing, duplicate] {
        assert!(!recognize_array_finite_extensionality(&terms, &[forged]));
        validate_strict(&terms, forged, TheoryLemmaKind::ArrayFiniteExtensionality)
            .expect_err("partial or duplicate coverage must fail closed");
    }
}

#[test]
fn finite_extensionality_rejects_a_foreign_array_cell() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Bool, Sort::Int);
    let array_a = terms.mk_var("finite_foreign_a", sort.clone());
    let array_b = terms.mk_var("finite_foreign_b", sort.clone());
    let foreign = terms.mk_var("finite_foreign_c", sort);
    let false_term = terms.mk_bool(false);
    let true_term = terms.mk_bool(true);
    let root = terms.mk_eq(array_a, array_b);
    let a_false = terms.mk_select(array_a, false_term);
    let b_false = terms.mk_select(array_b, false_term);
    let false_cell = terms.mk_eq(a_false, b_false);
    let a_true = terms.mk_select(array_a, true_term);
    let foreign_true = terms.mk_select(foreign, true_term);
    let forged_cell = terms.mk_eq(a_true, foreign_true);
    let conjunction = terms.mk_and(vec![false_cell, forged_cell]);
    let forged = terms.mk_eq(root, conjunction);

    validate_strict(&terms, forged, TheoryLemmaKind::ArrayFiniteExtensionality)
        .expect_err("every pointwise equality must use the root array pair");
}

fn bool_select_expansion(terms: &mut TermStore, array: TermId, symbolic_index: TermId) -> TermId {
    let false_term = terms.mk_bool(false);
    let true_term = terms.mk_bool(true);
    let symbolic_select = terms.mk_select(array, symbolic_index);
    let false_select = terms.mk_select(array, false_term);
    let true_select = terms.mk_select(array, true_term);
    let condition = terms.mk_eq(symbolic_index, false_term);
    let expansion = terms.mk_ite(condition, false_select, true_select);
    terms.mk_eq(symbolic_select, expansion)
}

#[test]
fn finite_select_expansion_accepts_actual_bool_normal_form() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Bool, Sort::Int);
    let array = terms.mk_var("finite_select_bool_a", sort);
    let index = terms.mk_var("finite_select_bool_i", Sort::Bool);
    let axiom = bool_select_expansion(&mut terms, array, index);

    assert!(recognize_array_finite_select_expansion(&terms, &[axiom]));
    assert_eq!(
        recognize_array_theory_lemma(&terms, &[axiom]),
        Some(TheoryLemmaKind::ArrayFiniteSelectExpansion)
    );
    validate_strict(&terms, axiom, TheoryLemmaKind::ArrayFiniteSelectExpansion)
        .expect("the checker accepts mk_eq's exact equality-over-ITE normal form");
}

#[test]
fn finite_select_expansion_rejects_duplicate_and_mismatched_bool_branches() {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Bool, Sort::Int);
    let array = terms.mk_var("finite_select_forged_a", sort);
    let index = terms.mk_var("finite_select_forged_i", Sort::Bool);
    let false_term = terms.mk_bool(false);
    let true_term = terms.mk_bool(true);
    let symbolic_select = select(&mut terms, array, index);
    let false_select = select(&mut terms, array, false_term);
    let true_select = select(&mut terms, array, true_term);

    let duplicate_value = terms.mk_ite_raw(index, true_select, true_select);
    let duplicate = equality(&mut terms, symbolic_select, duplicate_value);
    let mismatched_value = terms.mk_ite_raw(index, false_select, true_select);
    let mismatched = equality(&mut terms, symbolic_select, mismatched_value);

    for forged in [duplicate, mismatched] {
        assert!(!recognize_array_finite_select_expansion(&terms, &[forged]));
        validate_strict(&terms, forged, TheoryLemmaKind::ArrayFiniteSelectExpansion)
            .expect_err("duplicate or condition/branch mismatch must fail closed");
    }
}

#[test]
fn finite_select_expansion_rejects_bitvector_indices() {
    let mut terms = TermStore::new();
    let index_sort = Sort::bitvec(2);
    let sort = Sort::array(index_sort.clone(), Sort::Int);
    let array = terms.mk_var("finite_select_bv_a", sort);
    let index = terms.mk_var("finite_select_bv_i", index_sort);
    let symbolic_select = terms.mk_select(array, index);
    let domain: Vec<_> = (0..4)
        .map(|value| terms.mk_bitvec(BigInt::from(value), 2))
        .collect();
    let mut expansion = terms.mk_select(array, domain[3]);
    for &point in domain[..3].iter().rev() {
        let condition = terms.mk_eq(index, point);
        let branch = terms.mk_select(array, point);
        expansion = terms.mk_ite(condition, branch, expansion);
    }
    let axiom = terms.mk_eq(symbolic_select, expansion);

    assert!(!recognize_array_finite_select_expansion(&terms, &[axiom]));
    validate_strict(&terms, axiom, TheoryLemmaKind::ArrayFiniteSelectExpansion)
        .expect_err("the live symbolic-select lane enumerates Bool/enums, not BV indices");
}
