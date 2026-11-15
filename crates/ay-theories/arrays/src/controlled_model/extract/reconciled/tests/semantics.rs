// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn real_flat_store_class_candidate_matches_every_legacy_model_field() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    let values = fixture.values();
    let original = owner(end, 1_000_000, 128 << 20);
    let before = (
        solver.eq_adj_version,
        solver.equiv_class_cache_version,
        solver.array_var_merge_log.len(),
    );
    let output = run(&solver, &values, &original);
    assert_eq!(
        (
            solver.eq_adj_version,
            solver.equiv_class_cache_version,
            solver.array_var_merge_log.len()
        ),
        before
    );
    same(&output, &solver.extract_model(&values));
    assert_eq!(
        output.array_values[&fixture.stores[1]].stores[0].1,
        values[&fixture.writes[1]]
    );
    assert!(output.store_chain_class_candidate.is_some());
    drop(output);
    original.check().unwrap();
}

#[test]
fn duplicate_written_indices_keep_outermost_first_and_base_cells_unwritten_only() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    let mut values = fixture.values();
    values.insert(fixture.indices[1], "0".into());
    let original = owner(end, 1_000_000, 128 << 20);
    let output = run(&solver, &values, &original);
    same(&output, &solver.extract_model(&values));
    let stores = &output.array_values[&fixture.stores[1]].stores;
    assert_eq!(stores[0], ("0".into(), values[&fixture.writes[1]].clone()));
    assert_eq!(stores[1], ("0".into(), "soft".into()));
    let candidate = output.store_chain_class_candidate.as_ref().unwrap();
    assert!(!candidate[&fixture.bases[0]]
        .stores
        .iter()
        .any(|(k, _)| k == "0"));
    drop(output);
    original.check().unwrap();
}

#[test]
fn partial_valued_chain_is_excluded_without_fabricating_a_write() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    let mut values = fixture.values();
    values.remove(&fixture.writes[0]);
    let original = owner(end, 1_000_000, 128 << 20);
    let output = run(&solver, &values, &original);
    same(&output, &solver.extract_model(&values));
    assert!(!output.array_values[&fixture.stores[1]]
        .stores
        .iter()
        .any(|(_, v)| v == "soft"));
    drop(output);
    original.check().unwrap();
}

#[test]
fn fresh_and_cached_lifo_classes_preserve_last_rank_tie_and_map_layout() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut values = fixture.values();
    values.remove(&fixture.writes[0]);
    for cached in [false, true] {
        let mut solver = fixture.solver();
        if cached {
            solver.build_equiv_class_cache();
        }
        let original = owner(end, 1_000_000, 128 << 20);
        let output = run(&solver, &values, &original);
        let legacy = solver.extract_model(&values);
        same(&output, &legacy);
        let class = solver
            .equiv_classes
            .iter()
            .find(|c| c.contains(&fixture.missing))
            .unwrap();
        let winner = class
            .iter()
            .copied()
            .filter(|&t| t == fixture.alias || t == fixture.stores[1] || t == fixture.stores[2])
            .last()
            .unwrap();
        assert_eq!(
            output.array_values[&fixture.missing],
            output.array_values[&winner]
        );
        assert_eq!(
            output.array_values.keys().copied().collect::<Vec<_>>(),
            legacy.array_values.keys().copied().collect::<Vec<_>>()
        );
        assert_eq!(
            output.array_values.allocation_size(),
            legacy.array_values.allocation_size()
        );
        let candidate = output.store_chain_class_candidate.as_ref().unwrap();
        let legacy = legacy.store_chain_class_candidate.as_ref().unwrap();
        assert_eq!(
            candidate.keys().copied().collect::<Vec<_>>(),
            legacy.keys().copied().collect::<Vec<_>>()
        );
        drop(output);
        original.check().unwrap();
    }
}

#[test]
fn full_text_cells_and_read_poison_remain_local_under_class_propagation() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    let mut values = fixture.values();
    // Two distinct original select terms resolve to the same base/index.
    let large = "é".repeat(257);
    values.insert(fixture.indices[2], large.clone());
    values.insert(fixture.indices[3], large.clone());
    values.insert(fixture.selects[0], large.clone());
    let original = owner(end, 1_000_000, 128 << 20);
    let output = run(&solver, &values, &original);
    same(&output, &solver.extract_model(&values));
    assert!(output.array_values[&fixture.bases[0]].stores.is_empty());
    assert!(output.read_conflicted.contains(&fixture.bases[0]));
    assert!(!output.read_conflicted.contains(&fixture.alias));
    assert_eq!(
        output.read_conflicted,
        solver.extract_model(&values).read_conflicted
    );
    drop(output);
    original.check().unwrap();
}
