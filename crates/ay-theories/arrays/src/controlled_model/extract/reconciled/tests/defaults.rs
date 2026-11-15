// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn two_free_bases_share_only_the_legacy_candidate_else_choice() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    let values = fixture.values();
    let original = owner(end, 1_000_000, 128 << 20);
    let output = run(&solver, &values, &original);
    same(&output, &solver.extract_model(&values));
    assert!(output.array_values[&fixture.bases[0]].default.is_none());
    let candidate = output.store_chain_class_candidate.as_ref().unwrap();
    assert!(candidate[&fixture.bases[0]].default.is_some());
    assert_eq!(
        candidate[&fixture.bases[0]].default,
        candidate[&fixture.bases[1]].default
    );
    drop(output);
    original.check().unwrap();
}

#[test]
fn mixed_defaults_complete_both_directions_without_changing_the_old_partial_api() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    let mut values = fixture.values();
    values.insert(fixture.defaults[0], "agreed".into());
    let original = owner(end, 1_000_000, 128 << 20);
    let output = run(&solver, &values, &original);
    same(&output, &solver.extract_model(&values));
    assert_eq!(
        output.array_values[&fixture.stores[1]].default.as_deref(),
        Some("agreed")
    );
    assert_eq!(
        output.array_values[&fixture.alias].default.as_deref(),
        Some("agreed")
    );
    let legacy_partial_owner = owner(end, 1_000_000, 128 << 20);
    assert!(legacy_partial_owner
        .with_work(|w| solver.try_extract_prepared_model_with_budget(&values, w))
        .is_err());
    drop(output);
    original.check().unwrap();
}

#[test]
fn conflicting_class_and_parent_defaults_never_replace_existing_values() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    let mut values = fixture.values();
    values.insert(fixture.defaults[3], "left-default".into());
    values.insert(fixture.defaults[4], "right-default".into());
    let original = owner(end, 1_000_000, 128 << 20);
    let output = run(&solver, &values, &original);
    same(&output, &solver.extract_model(&values));
    assert_eq!(
        output.array_values[&fixture.stores[1]].default.as_deref(),
        Some("left-default")
    );
    assert_eq!(
        output.array_values[&fixture.stores[2]].default.as_deref(),
        Some("right-default")
    );
    drop(output);
    original.check().unwrap();
}

#[test]
fn some_empty_const_default_remains_distinct_from_no_default() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    let mut values = fixture.values();
    values.insert(fixture.else_value, String::new());
    let original = owner(end, 1_000_000, 128 << 20);
    let output = run(&solver, &values, &original);
    same(&output, &solver.extract_model(&values));
    assert_eq!(
        output.array_values[&fixture.constant].default.as_deref(),
        Some("")
    );
    assert!(output.array_values[&fixture.bases[0]].default.is_none());
    drop(output);
    original.check().unwrap();
}
