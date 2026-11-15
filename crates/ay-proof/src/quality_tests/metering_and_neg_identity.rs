// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::metering_and_neg::{and_neg_step, validate_one};
use super::*;
use crate::checker::boolean_and_neg_shape::and_neg_is_emitted_identity_shape;

fn fixture() -> (TermStore, TermId, TermId, TermId, Vec<TermId>) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let source = terms.mk_app(Symbol::named("and"), [a, b], Sort::Bool);
    let na = terms.mk_not_raw(a);
    let nb = terms.mk_not_raw(b);
    (terms, source, a, b, vec![source, na, nb])
}

#[test]
fn and_neg_identity_shape_validates_without_recursive_matching() {
    let (terms, source, _, _, clause) = fixture();
    let step = and_neg_step(clause.clone(), source);
    assert!(and_neg_is_emitted_identity_shape(
        &terms,
        &clause,
        Some(source)
    ));
    assert_eq!(
        select_semantic_charge_class(&step, &terms),
        SemanticChargeClass::AndNegIdentityShape
    );
    validate_one(&terms, &step).unwrap();
}

#[test]
fn and_neg_identity_shape_rejects_wrong_cover_source_and_missing_literals() {
    let (mut terms, source, a, _, clause) = fixture();
    let c = terms.mk_var("c", Sort::Bool);
    let foreign = terms.mk_app(Symbol::named("and"), [a, c], Sort::Bool);
    for (candidate, claimed) in [
        (vec![source, clause[1], clause[1]], source),
        (vec![source, clause[1]], source),
        (clause.clone(), foreign),
    ] {
        let step = and_neg_step(candidate.clone(), claimed);
        assert!(!and_neg_is_emitted_identity_shape(
            &terms,
            &candidate,
            Some(claimed)
        ));
        assert_eq!(
            select_semantic_charge_class(&step, &terms),
            SemanticChargeClass::General
        );
        assert!(validate_one(&terms, &step).is_err());
    }
}

#[test]
fn and_neg_identity_shape_keeps_valid_permutations_on_the_general_route() {
    let (terms, source, _, _, mut clause) = fixture();
    clause.swap(0, 2);
    let step = and_neg_step(clause.clone(), source);
    assert!(!and_neg_is_emitted_identity_shape(
        &terms,
        &clause,
        Some(source)
    ));
    assert_eq!(
        select_semantic_charge_class(&step, &terms),
        SemanticChargeClass::General
    );
    validate_one(&terms, &step).unwrap();
}

#[test]
fn and_neg_identity_shape_preserves_duplicate_occurrences_and_shared_children() {
    let mut terms = TermStore::new();
    let mut child = terms.mk_var("a", Sort::Bool);
    for _ in 0..12 {
        child = terms.mk_app(Symbol::named("and"), [child, child], Sort::Bool);
    }
    let source = terms.mk_app(Symbol::named("and"), [child, child], Sort::Bool);
    let negative = terms.mk_not_raw(child);
    let clause = vec![source, negative, negative];
    let step = and_neg_step(clause.clone(), source);
    assert!(and_neg_is_emitted_identity_shape(
        &terms,
        &clause,
        Some(source)
    ));
    assert_eq!(
        select_semantic_charge_class(&step, &terms),
        SemanticChargeClass::AndNegIdentityShape
    );
    validate_one(&terms, &step).unwrap();
}
