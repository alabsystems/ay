// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn prepared_combiner_preserves_every_legacy_field_and_real_array_classes() {
    let end = Instant::now() + Duration::from_secs(20);
    let original = owner(UNITS, BYTES, end);
    for cell in [Sort::bitvec(8), Sort::bitvec(64), Sort::bitvec(128)] {
        let fixture = Fixture::new(cell, Shape::Reads);
        let (source, expected) = fixture.prepared();
        let actual = original
            .with_work(|work| {
                source.try_extract_prepared_euf_array_models_with_budget(&fixture.roots, work)
            })
            .unwrap();
        same(&actual, &expected);
        assert!(actual.1.array_values.contains_key(&fixture.base));
        assert!(actual.1.array_values[&fixture.constant].default.is_some());
        assert!(!actual.0.function_table_terms.is_empty());
        assert!(Instant::now() < end);
    }
}

#[test]
fn prepared_store_composition_borrows_exact_euf_values_without_model_fixup() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new(Sort::bitvec(8), Shape::Store);
    let (source, expected) = fixture.prepared();
    let original = owner(UNITS, BYTES, end);
    let actual = original
        .with_work(|work| {
            source.try_extract_prepared_euf_array_models_with_budget(&fixture.roots, work)
        })
        .unwrap();
    same(&actual, &expected);
    assert!(!actual.0.function_tables["store"].is_empty());
    assert!(actual.0.term_values.contains_key(&fixture.read));
    assert!(!actual.1.array_values.is_empty());
}

#[test]
fn dirty_array_after_clean_euf_refuses_and_original_clone_cannot_retry() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new(Sort::bitvec(8), Shape::Reads);
    let (mut source, _) = fixture.prepared();
    source
        .arrays
        .as_mut()
        .unwrap()
        .assert_literal(fixture.roots[2], false);
    let original = owner(UNITS, BYTES, end);
    let clone = original.clone();
    let result = original.with_work(|work| {
        source.try_extract_prepared_euf_array_models_with_budget(&fixture.roots, work)
    });
    assert!(matches!(
        result,
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
    assert_eq!(
        clone.check(),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    let _ = source.extract_euf_array_models();
    assert!(clone
        .with_work(|work| {
            source.try_extract_prepared_euf_array_models_with_budget(&fixture.roots, work)
        })
        .is_err());
}

#[test]
fn dirty_euf_or_unsupported_original_domain_never_falls_back_to_legacy() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut fixture = Fixture::new(Sort::bitvec(8), Shape::Reads);
    fixture.terms.mk_var("unscoped-int", Sort::Int);
    let (source, _) = fixture.prepared();
    let original = owner(UNITS, BYTES, end);
    assert!(matches!(
        original.with_work(|work| {
            source.try_extract_prepared_euf_array_models_with_budget(&fixture.roots, work)
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
    let fixture = Fixture::new(Sort::bitvec(8), Shape::Reads);
    let (mut source, _) = fixture.prepared();
    source.euf.assert_literal(fixture.roots[2], false);
    let separate = owner(UNITS, BYTES, end);
    assert!(matches!(
        separate.with_work(|work| {
            source.try_extract_prepared_euf_array_models_with_budget(&fixture.roots, work)
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
}

#[test]
fn missing_array_or_arithmetic_combiner_is_terminal_not_an_empty_model() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new(Sort::bitvec(8), Shape::Reads);
    let (mut source, _) = fixture.prepared();
    source.arrays = None;
    let original = owner(UNITS, BYTES, end);
    assert!(matches!(
        original.with_work(|work| {
            source.try_extract_prepared_euf_array_models_with_budget(&fixture.roots, work)
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
    let source = TheoryCombiner::uf_lia(&fixture.terms);
    let separate = owner(UNITS, BYTES, end);
    assert!(matches!(
        separate.with_work(|work| {
            source.try_extract_prepared_euf_array_models_with_budget(&fixture.roots, work)
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
}

#[test]
fn current_prepared_scalar_equality_adjacency_refuses_without_a_silent_projection() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut fixture = Fixture::new(Sort::bitvec(8), Shape::Reads);
    let literal = fixture.terms.mk_bitvec(42u8.into(), 8);
    let equal = fixture
        .terms
        .mk_app(Symbol::named("="), [fixture.read, literal], Sort::Bool);
    fixture.roots.push(equal);
    fixture.assignments.push((equal, true));
    // Historical control identity retained; genuine scalar pins now compose.
    // No edge projection or guessed model: compare every legacy DATA field.
    let (source, expected) = fixture.prepared();
    let original = owner(UNITS, BYTES, end);
    let actual = original
        .with_work(|work| {
            source.try_extract_prepared_euf_array_models_with_budget(&fixture.roots, work)
        })
        .unwrap();
    same(&actual, &expected);
    assert!(actual.0.term_values.contains_key(&fixture.read));
    assert!(actual.1.array_values.contains_key(&fixture.base));
    drop(actual);
    original.check().unwrap();
}
