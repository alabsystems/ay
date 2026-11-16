// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn actual_cold_registration_matches_every_legacy_model_field() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut source = ArraySolver::new(&fixture.terms);
    let values = fixture.values();
    let original = owner(end, 1_000_000, 128 << 20);
    let output = original
        .with_work(|work| source.try_extract_registered_model_with_budget(&values, work))
        .unwrap();
    assert!(source.dirty && source.assign_dirty);
    assert_eq!(source.populated_terms, 0);
    assert!(source.select_cache.is_empty() && source.array_vars.is_empty());
    same(&output, &source.extract_model(&values));
    assert_eq!(output.array_values[&fixture.base].stores.len(), 4);
    assert_eq!(
        output.array_values[&fixture.constant].default.as_deref(),
        Some("else")
    );
    assert!(output.store_chain_class_candidate.is_none());
    drop(output);
    original.check().unwrap();
}

#[test]
fn exact_registered_scope_ignores_dead_store_terms_not_in_that_scope() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut fixture = Fixture::new();
    let dead = fixture.terms.mk_app(
        Symbol::named("store"),
        [fixture.base, fixture.indices[0], fixture.otherwise],
        Sort::array(Sort::Int, Sort::Int),
    );
    let mut source = ArraySolver::new(&fixture.terms);
    source.enable_registered_atom_scope(true);
    for &term in fixture
        .reads
        .iter()
        .chain([fixture.constant_read, fixture.default].iter())
    {
        source.register_atom(term);
    }
    assert!(!source.term_in_scope(dead));
    let scope = source.registered_term_scope.as_ref().unwrap().clone();
    let values = fixture.values();
    let original = owner(end, 1_000_000, 128 << 20);
    let output = original
        .with_work(|work| source.try_extract_registered_model_with_budget(&values, work))
        .unwrap();
    assert_eq!(source.registered_term_scope.as_ref(), Some(&scope));
    same(&output, &source.extract_model(&values));
    assert!(!output.array_values.contains_key(&dead));
    drop(output);
    original.check().unwrap();
}

#[test]
fn actual_false_assignment_and_external_disequality_are_rebuilt_without_a_class() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut source = ArraySolver::new(&fixture.terms);
    source.register_atom(fixture.equality);
    source.assert_literal(fixture.equality, false);
    source.assert_external_disequality(fixture.indices[0], fixture.indices[1]);
    let values = fixture.values();
    let original = owner(end, 1_000_000, 128 << 20);
    let mut view = ArraySolver::new(&fixture.terms); // Test fixture, not production preparation.
    original
        .with_work(|work| {
            prepare(&source, &mut view, work)?;
            assert_eq!(view.assigns, source.assigns);
            assert!(view.eq_adj.is_empty());
            assert!(view.diseq_set.contains(&ArraySolver::ordered_pair(
                fixture.indices[0],
                fixture.indices[1]
            )));
            assert!(view.diseq_set.contains(&ArraySolver::ordered_pair(
                match fixture.terms.get(fixture.equality) {
                    TermData::App(_, args) => args[0],
                    _ => unreachable!(),
                },
                match fixture.terms.get(fixture.equality) {
                    TermData::App(_, args) => args[1],
                    _ => unreachable!(),
                }
            )));
            drop(view);
            work.charge(0)
        })
        .unwrap();
    let output = original
        .with_work(|work| source.try_extract_registered_model_with_budget(&values, work))
        .unwrap();
    same(&output, &source.extract_model(&values));
    drop(output);
    original.check().unwrap();
}

#[test]
fn retained_cleared_backing_preserves_exact_select_order_and_partial_poison() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut source = ArraySolver::new(&fixture.terms);
    source.populate_caches();
    source.reset(); // Real legacy teardown retains structural table allocations.
    let allocation = source.select_cache.allocation_size();
    assert!(allocation > 0 && source.select_cache.is_empty());
    let mut values = fixture.values();
    for &index in &fixture.indices {
        values.insert(index, "same-cell".into());
    }
    let original = owner(end, 1_000_000, 128 << 20);
    let mut view = ArraySolver::new(&fixture.terms); // Test fixture, before controlled instrumentation.
    original
        .with_work(|work| prepare(&source, &mut view, work))
        .unwrap();
    source.populate_caches(); // Separate unchanged legacy oracle, not priced preparation.
    assert_eq!(
        view.select_cache.allocation_size(),
        source.select_cache.allocation_size()
    );
    assert_eq!(
        view.select_cache.iter().collect::<Vec<_>>(),
        source.select_cache.iter().collect::<Vec<_>>()
    );
    drop(view);
    original.check().unwrap();
    source.reset();
    let output = original
        .with_work(|work| source.try_extract_registered_model_with_budget(&values, work))
        .unwrap();
    assert_eq!(source.select_cache.allocation_size(), allocation);
    same(&output, &source.extract_model(&values));
    assert_eq!(output.array_values[&fixture.base].stores.len(), 0);
    assert!(output.read_conflicted.contains(&fixture.base));
    drop(output);
    original.check().unwrap();
}

#[test]
fn absent_values_and_untracked_constants_do_not_get_invented_interpretations() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let value = terms.mk_int(9.into());
    let constant = terms.mk_const_array(Sort::Int, value);
    let mut source = ArraySolver::new(&terms);
    let values = HashMap::from_iter([(value, "9".into())]);
    let original = owner(end, 1_000_000, 128 << 20);
    let output = original
        .with_work(|work| source.try_extract_registered_model_with_budget(&values, work))
        .unwrap();
    same(&output, &source.extract_model(&values));
    assert!(!output.array_values.contains_key(&constant));
    assert!(output.array_values.is_empty());
    drop(output);
    original.check().unwrap();
}

#[test]
fn existing_warm_class_api_remains_the_exact_delegated_lane() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut source = ArraySolver::new(&fixture.terms);
    source.populate_caches();
    source.register_atom(fixture.equality);
    source.assert_literal(fixture.equality, true);
    let _ = source.check();
    source.rebuild_assign_indices();
    assert!(!source.eq_adj.is_empty() && !source.dirty);
    let values = HashMap::default();
    let original = owner(end, 1_000_000, 128 << 20);
    let old = original
        .with_work(|work| source.try_extract_prepared_model_with_budget(&values, work))
        .unwrap();
    let new = original
        .with_work(|work| source.try_extract_registered_model_with_budget(&values, work))
        .unwrap();
    same(&old, &new);
    drop((old, new));
    original.check().unwrap();
}
