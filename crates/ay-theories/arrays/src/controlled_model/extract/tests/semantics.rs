// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn prepared_real_store_default_select_inventories_match_legacy_data() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    let values = fixture.values();
    let owner = owner(end, 1_000_000, 128 << 20);
    let output = owner
        .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
        .unwrap();
    let legacy = solver.extract_model(&values);
    same(&output, &legacy);
    assert_eq!(
        output.array_values[&fixture.chain].stores,
        vec![
            ("cell".into(), "concrete".into()),
            ("cell".into(), "soft".into())
        ]
    );
    assert_eq!(
        output.array_values[&fixture.constant].default.as_deref(),
        Some("else")
    );
    assert!(output.store_chain_class_candidate.is_none());
    drop(output);
    owner.check().unwrap();
}

#[test]
fn real_select_iteration_conflict_is_partial_poison_not_a_fabricated_winner() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    let mut values = fixture.values();
    for (&select, word) in fixture.selects.iter().zip(["one", "two", "repair"]) {
        values.insert(select, word.into());
    }
    let owner = owner(end, 1_000_000, 128 << 20);
    let output = owner
        .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
        .unwrap();
    let legacy = solver.extract_model(&values);
    same(&output, &legacy);
    assert_eq!(output.array_values[&fixture.base].stores.len(), 0);
    assert!(output.read_conflicted.contains(&fixture.base));
    drop(output);
    owner.check().unwrap();
}

#[test]
fn absent_committed_defaults_and_cells_remain_absent_without_completion() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    let mut values = fixture.values();
    values.clear();
    let owner = owner(end, 1_000_000, 128 << 20);
    let output = owner
        .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
        .unwrap();
    same(&output, &solver.extract_model(&values));
    assert!(output.array_values.is_empty());
    assert!(output.read_conflicted.is_empty());
    drop(output);
    owner.check().unwrap();
}

#[test]
fn constant_empty_default_is_not_overwritten_by_scalar_default() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    let mut values = fixture.values();
    values.insert(fixture.default, String::new());
    solver
        .default_cache
        .insert(fixture.constant, fixture.written[0]);
    let owner = owner(end, 1_000_000, 128 << 20);
    let output = owner
        .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
        .unwrap();
    same(&output, &solver.extract_model(&values));
    assert_eq!(
        output.array_values[&fixture.constant].default.as_deref(),
        Some("")
    );
    drop(output);
    owner.check().unwrap();
}

#[test]
fn hit_or_uncommitted_store_index_never_fabricates_a_base_read() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    for target in solver.select_cache.values_mut() {
        target.0 = fixture.chain;
    }
    let mut values = fixture.values();
    let owner = owner(end, 1_000_000, 128 << 20);
    for uncommitted in [false, true] {
        if uncommitted {
            values.remove(&fixture.indices[1]);
        }
        let output = owner
            .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
            .unwrap();
        same(&output, &solver.extract_model(&values));
        assert!(!output.array_values.contains_key(&fixture.base));
        assert!(output.read_conflicted.is_empty());
        drop(output);
    }
    owner.check().unwrap();
}

#[test]
fn complete_text_key_windows_preserve_all_prefix_bytes() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    let mut values = fixture.values();
    for (position, &index) in fixture.indices.iter().enumerate() {
        values.insert(index, format!("{}🙂{}", "k".repeat(129), position));
    }
    let owner = owner(end, 1_000_000, 128 << 20);
    let output = owner
        .with_work(|work| solver.try_extract_prepared_model_with_budget(&values, work))
        .unwrap();
    same(&output, &solver.extract_model(&values));
    assert_eq!(output.array_values[&fixture.base].stores.len(), 3);
    assert!(output.read_conflicted.is_empty());
    drop(output);
    owner.check().unwrap();
}
