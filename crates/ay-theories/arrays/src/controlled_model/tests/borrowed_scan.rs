// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::hash::BuildHasher;
use std::mem::size_of;

fn collision_keys(hasher: &impl BuildHasher) -> Vec<TermId> {
    // Pinned hashbrown: reserve(112) uses 128 buckets. One h1 start makes
    // dense probe groups so removal leaves genuine DELETED control bytes.
    let keys: Vec<_> = (0..524_288u32)
        .map(TermId)
        .filter(|key| hasher.hash_one(key) & 127 == 0)
        .take(112)
        .collect();
    assert_eq!(keys.len(), 112);
    keys
}

fn sparse_model() -> ArrayModel {
    let mut result = ArrayModel::default();
    result.array_values.reserve(112);
    result.read_conflicted.reserve(112);
    let keys = collision_keys(result.array_values.hasher());
    for &key in &keys {
        result
            .array_values
            .insert(key, ArrayInterpretation::default());
        result.read_conflicted.insert(key);
    }
    let map_capacity = result.array_values.capacity();
    let set_capacity = result.read_conflicted.capacity();
    let map_bytes = result.array_values.allocation_size();
    let set_bytes = result.read_conflicted.allocation_size();
    for key in &keys[..96] {
        result.array_values.remove(key);
        result.read_conflicted.remove(key);
    }
    assert!(result.array_values.capacity() < map_capacity);
    assert!(result.read_conflicted.capacity() < set_capacity);
    assert_eq!(result.array_values.allocation_size(), map_bytes);
    assert_eq!(result.read_conflicted.allocation_size(), set_bytes);
    assert_eq!(result.array_values.len(), 16);
    assert_eq!(result.read_conflicted.len(), 16);
    result.store_chain_class_candidate = Some(result.array_values.clone());
    result
}

fn scan_units<T>(allocation_bytes: usize) -> usize {
    let expected = (allocation_bytes / size_of::<T>() + 32) * 8 + 1;
    let charged = Cell::new(0usize);
    let mut sink = |units, bytes| {
        assert_eq!(bytes, 0);
        charged.set(charged.get() + units);
        Ok(())
    };
    let allowance = u64::try_from(expected).expect("fixture allowance fits u64");
    let mut work = WorkBudget::with_admission(allowance, &mut sink);
    owned::scan_table::<T>(allocation_bytes, &mut work).unwrap();
    drop(work);
    assert_eq!(charged.get(), expected);
    expected
}

#[test]
fn deleted_model_map_scan_is_charged_from_retained_allocation() {
    let source = sparse_model();
    let actual = scan_units::<(TermId, ArrayInterpretation)>(source.array_values.allocation_size());
    assert!(actual > (source.array_values.len() * 8 + 1));
    let output = healthy(|work| source.try_clone_with_budget(work)).unwrap();
    assert_eq!(output.array_values, source.array_values);
    assert_eq!(
        output.store_chain_class_candidate,
        source.store_chain_class_candidate
    );
}

#[test]
fn deleted_conflict_set_scan_uses_its_actual_entry_layout() {
    let source = sparse_model();
    let actual = scan_units::<(TermId, ())>(source.read_conflicted.allocation_size());
    assert!(actual > (source.read_conflicted.len() * 8 + 1));
    let output = healthy(|work| source.try_clone_with_budget(work)).unwrap();
    assert_eq!(output.read_conflicted, source.read_conflicted);
}

#[test]
fn retained_sparse_maps_share_one_original_grant_across_clones() {
    let source = sparse_model();
    let (units, bytes, _) = costs(&source);
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(units as u64 * 2 - 1, bytes * 2),
        Instant::now() + Duration::from_secs(20),
        Arc::new(|| false),
    );
    let first = owner
        .with_work(|work| source.try_clone_with_budget(work))
        .unwrap();
    assert_eq!(first.array_values, source.array_values);
    assert_eq!(first.read_conflicted, source.read_conflicted);
    assert_eq!(
        first.store_chain_class_candidate,
        source.store_chain_class_candidate
    );
    assert!(owner
        .clone()
        .with_work(|work| source.try_clone_with_budget(work))
        .is_err());
    assert!(owner.with_work(|_| Ok(())).is_err());
    assert_eq!(source.array_values.len(), 16);
}

#[test]
fn zero_sized_entry_layout_refuses_before_division_or_iteration() {
    healthy(|work| {
        assert_eq!(owned::scan_table::<()>(0, work), Err(QueryError::Exhausted));
        assert_eq!(work.charge(0), Err(QueryError::Exhausted));
    });
}

#[test]
fn overflowing_allocated_scan_bound_is_terminal_before_iteration() {
    healthy(|work| {
        assert_eq!(
            owned::scan_table::<u8>(usize::MAX, work),
            Err(QueryError::Exhausted)
        );
        assert_eq!(work.charge(0), Err(QueryError::Exhausted));
    });
}

#[test]
fn empty_singleton_scan_keeps_group_slack_without_a_byte_debit() {
    assert_eq!(scan_units::<(TermId, ArrayInterpretation)>(0), 257);
    assert_eq!(scan_units::<(TermId, ())>(0), 257);
}
