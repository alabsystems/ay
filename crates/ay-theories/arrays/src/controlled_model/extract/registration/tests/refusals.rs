// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn stores_maps_as_array_lambda_and_nested_forms_never_get_a_cold_success() {
    let end = Instant::now() + Duration::from_secs(20);
    for name in [
        "store",
        "map[f]",
        "as-array[f]",
        "lambda-array",
        "opaque-array",
    ] {
        let mut fixture = Fixture::new();
        let _unsupported_array_term = fixture.terms.mk_app(
            Symbol::named(name),
            [fixture.base, fixture.indices[0], fixture.otherwise],
            Sort::array(Sort::Int, Sort::Int),
        );
        let source = ArraySolver::new(&fixture.terms);
        refused(&source, end);
        assert!(source.dirty && source.select_cache.is_empty());
    }
    let mut terms = TermStore::new();
    let _nested_array = terms.mk_var(
        "nested",
        Sort::array(Sort::Int, Sort::array(Sort::Int, Sort::Int)),
    );
    refused(&ArraySolver::new(&terms), end);
}

#[test]
fn active_true_equality_or_external_merge_refuses_not_an_empty_proof_forest() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut source = ArraySolver::new(&fixture.terms);
    // Genuine assertion route can itself prepare caches; it is not a cold lane.
    // Injecting an already-active assignment tests the cold replay guard itself.
    source.assigns.insert(fixture.equality, true);
    refused(&source, end);
    assert_eq!(source.assigns.get(&fixture.equality), Some(&true));
    let mut external = ArraySolver::new(&fixture.terms);
    external.assert_external_equality(fixture.indices[0], fixture.indices[1]);
    refused(&external, end);
    assert_eq!(external.external_eqs.len(), 1);
}

#[test]
fn scoped_parent_without_a_live_registered_child_is_terminal_refusal() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut source = ArraySolver::new(&fixture.terms);
    source.enable_registered_atom_scope(true);
    source.register_atom(fixture.reads[0]);
    source
        .registered_term_scope
        .as_mut()
        .unwrap()
        .remove(&fixture.base);
    refused(&source, end);
    assert!(source.term_in_scope(fixture.reads[0]));
    assert!(!source.term_in_scope(fixture.base));
}

#[test]
fn dirty_partial_assignment_era_and_stale_scope_ids_cannot_be_repaired_silently() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut source = ArraySolver::new(&fixture.terms);
    source.assign_dirty = false;
    refused(&source, end);
    assert!(source.dirty && !source.assign_dirty);
    let mut stale = ArraySolver::new(&fixture.terms);
    stale.enable_registered_atom_scope(true);
    stale
        .registered_term_scope
        .as_mut()
        .unwrap()
        .insert(TermId(u32::MAX));
    refused(&stale, end);
}

#[test]
fn tombstone_under_reconstruction_refuses_before_any_registration_replay() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut source = ArraySolver::new(&fixture.terms);
    use std::hash::BuildHasher;
    // Same authenticated dense-probe construction as the existing borrowed
    // scan regression: 112 equal h1 starts in 128 buckets force DELETED bytes.
    // Synthetic keys are never replayed; this negative must refuse at backing.
    let extra: Vec<_> = (0..524_288u32)
        .map(TermId)
        .filter(|key| {
            assert!(Instant::now() < end);
            source.select_cache.hasher().hash_one(key) & 127 == 0
        })
        .take(112)
        .collect();
    assert_eq!(extra.len(), 112);
    source.select_cache.try_reserve(112).unwrap();
    for &read in &extra {
        source
            .select_cache
            .insert(read, (fixture.base, fixture.indices[0]));
    }
    let allocation = source.select_cache.allocation_size();
    for &read in &extra[..96] {
        source.select_cache.remove(&read);
    }
    let mut candidate: HashMap<TermId, (TermId, TermId)> = HashMap::default();
    candidate
        .try_reserve(source.select_cache.capacity())
        .unwrap();
    // If this layout does not produce under-reconstruction, the fixture is
    // not evidence for that negative frontier: fail the test, never skip it.
    assert_ne!(candidate.allocation_size(), allocation);
    refused(&source, end);
    assert!(source.select_pair_index.is_empty() && source.array_vars.is_empty());
    assert_eq!(source.select_cache.allocation_size(), allocation);
}

#[test]
fn source_stamp_append_and_foreign_store_cannot_reuse_a_preparation_binding() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut fixture = Fixture::new();
    let source = ArraySolver::new(&fixture.terms);
    let original = owner(end, 1_000_000, 128 << 20);
    let stamp = original
        .with_work(|work| binding::Binding::capture(&source, work))
        .unwrap();
    drop(source);
    let _new_term = fixture.terms.mk_var("new", Sort::Int);
    let changed = ArraySolver::new(&fixture.terms);
    assert!(original
        .with_work(|work| stamp.verify(&changed, work))
        .is_err());
    assert!(original.clone().check().is_err());
    let foreign = Fixture::new();
    let other = ArraySolver::new(&foreign.terms);
    let second = owner(end, 1_000_000, 128 << 20);
    let fresh = second
        .with_work(|work| binding::Binding::capture(&changed, work))
        .unwrap();
    assert!(second.with_work(|work| fresh.verify(&other, work)).is_err());
}
