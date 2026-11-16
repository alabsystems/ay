// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded real hashbrown DATA fixtures; no native solver or new grant.

use super::super::super::{Admission, TermStore};
use super::*;
use std::hash::BuildHasher;

fn collision_store() -> (TermStore, Vec<u64>) {
    let mut store = TermStore::new();
    store.hash_cons = Default::default();
    store.hash_cons.try_reserve(112).expect("bounded fixture");
    let mut candidates: [Vec<u64>; 256] = std::array::from_fn(|_| Vec::new());
    // Pigeonhole, not assumed hash distribution: at least one h1 class has
    // 113 members. Low eight equal bits collide at BOTH B=128 and F=256.
    for key in 0..(256 * 113u64) {
        let hash = store.hash_cons.hasher().hash_one(key);
        candidates[(hash & 255) as usize].push(key);
    }
    let keys = candidates
        .into_iter()
        .find(|keys| keys.len() >= 113)
        .expect("pigeonhole")
        .into_iter()
        .take(112)
        .collect::<Vec<_>>();
    for &key in &keys {
        store
            .hash_cons
            .insert(key, vec![store.true_term(), store.false_term()]);
    }
    assert_eq!(store.hash_cons.len(), 112);
    assert_eq!(store.hash_cons.capacity(), 112);
    (store, keys)
}

fn charge(store: &TermStore) -> (usize, usize) {
    let old = store.controlled_slots().expect("actual allocation");
    let future = 4 * (old + store.hash_cons.len() + 1 + 32);
    let bytes = 8 * (old + future) * (size_of::<(u64, Vec<TermId>)>() + 32);
    let units = product(
        scans(store.hash_cons.allocation_size(), store.hash_cons.len()).expect("primary layout"),
        128,
    )
    .expect("bounded fixture");
    (units, bytes)
}

fn assert_rows(store: &TermStore, keys: &[u64], pointers: &[usize]) {
    for (&key, &pointer) in keys.iter().zip(pointers) {
        let row = store.hash_cons.get(&key).expect("complete retained row");
        assert_eq!(row, &[store.true_term(), store.false_term()]);
        assert_eq!(
            row.as_ptr() as usize,
            pointer,
            "header move, no payload copy"
        );
    }
}

fn pointers(store: &TermStore, keys: &[u64]) -> Vec<usize> {
    keys.iter()
        .map(|key| store.hash_cons.get(key).expect("fixture row").as_ptr() as usize)
        .collect()
}

fn deleted_rows(store: &mut TermStore, keys: &[u64]) -> Vec<u64> {
    let allocation = store.hash_cons.allocation_size();
    let mut deleted = Vec::new();
    // Equal h1 fills complete g-wide groups:112 is divisible by4/8/16.
    // Every non-EMPTY run has length>=g; erase must retain DELETED.
    for &key in keys.iter().take(80) {
        let row = store.hash_cons.remove(&key).expect("fixture row");
        assert_eq!(row, &[store.true_term(), store.false_term()]);
        assert_eq!(
            store.hash_cons.capacity(),
            store.hash_cons.len(),
            "real DELETED event"
        );
        deleted.push(key);
        assert_eq!(store.hash_cons.allocation_size(), allocation);
    }
    assert_eq!(deleted.len(), 80, "bounded real DELETED events");
    deleted
}

#[test]
fn real_full_collision_resize_prepays_and_preserves_every_owned_row() {
    let (mut store, keys) = collision_store();
    let pointers = pointers(&store, &keys);
    let expected = charge(&store);
    assert_eq!(expected.1, 716_800, "old bytes remain exact");
    let old = store.hash_cons.allocation_size();
    let mut checkpoint = || ControlFlow::Continue(());
    let mut owner = WorkBudget::new(1_048_576, &mut checkpoint);
    let mut observed = Vec::new();
    let mut sink = |work, bytes| {
        observed.push((work, bytes));
        owner.admit(work, bytes).is_ok()
    };
    let mut admission = Admission {
        progress: &mut sink,
        refused: false,
    };
    assert_eq!(store.controlled_map_reserve(&mut admission), Ok(()));
    drop(sink);
    assert_eq!(observed, vec![expected]);
    assert!(store.hash_cons.allocation_size() > old);
    assert_eq!(store.hash_cons.capacity(), 224);
    assert_rows(&store, &keys, &pointers);
}

#[test]
fn real_collision_tombstones_keep_allocation_and_rehash_in_place() {
    let (mut store, keys) = collision_store();
    let deleted = deleted_rows(&mut store, &keys);
    let retained = keys
        .iter()
        .copied()
        .filter(|key| store.hash_cons.contains_key(key))
        .collect::<Vec<_>>();
    assert_eq!(retained.len(), 32);
    assert_eq!(store.hash_cons.len(), 32);
    assert_eq!(
        store.hash_cons.capacity(),
        32,
        "DELETED slots retain exhausted growth"
    );
    let old = store.hash_cons.allocation_size();
    let pointers = pointers(&store, &retained);
    let expected = charge(&store);
    let mut checkpoint = || ControlFlow::Continue(());
    let mut owner = WorkBudget::new(1_048_576, &mut checkpoint);
    let mut observed = Vec::new();
    let mut sink = |work, bytes| {
        observed.push((work, bytes));
        owner.admit(work, bytes).is_ok()
    };
    let mut admission = Admission {
        progress: &mut sink,
        refused: false,
    };
    assert_eq!(store.controlled_map_reserve(&mut admission), Ok(()));
    drop(sink);
    assert_eq!(observed, vec![expected]);
    assert_eq!(store.hash_cons.allocation_size(), old);
    assert_eq!(store.hash_cons.capacity(), 112);
    assert_rows(&store, &retained, &pointers);
    assert!(deleted.iter().all(|key| !store.hash_cons.contains_key(key)));
}

#[test]
fn original_one_short_sticky_refusal_happens_before_real_growth() {
    let (mut store, keys) = collision_store();
    let pointers = pointers(&store, &keys);
    let expected = charge(&store);
    let old = store.hash_cons.allocation_size();
    let mut checkpoint = || ControlFlow::Continue(());
    let mut owner = WorkBudget::new(
        u64::try_from(expected.0 - 1).expect("fixture"),
        &mut checkpoint,
    );
    let mut sink = |work, bytes| owner.admit(work, bytes).is_ok();
    let mut admission = Admission {
        progress: &mut sink,
        refused: false,
    };
    for _ in 0..2 {
        assert_eq!(store.controlled_map_reserve(&mut admission), Err(limit()));
    }
    drop(sink);
    assert_eq!(owner.charge(0), Err(QueryError::Exhausted));
    assert_eq!(store.hash_cons.allocation_size(), old);
    assert_eq!(store.hash_cons.capacity(), 112);
    assert_rows(&store, &keys, &pointers);
}

#[test]
fn nonfull_table_preserves_the_old_unit_charge_and_zero_storage() {
    let mut store = TermStore::new();
    store.hash_cons.try_reserve(16).expect("bounded fixture");
    let old = store.hash_cons.allocation_size();
    let mut observed = Vec::new();
    let mut sink = |work, bytes| {
        observed.push((work, bytes));
        true
    };
    let mut admission = Admission {
        progress: &mut sink,
        refused: false,
    };
    assert_eq!(store.controlled_map_reserve(&mut admission), Ok(()));
    drop(sink);
    assert_eq!(observed, vec![(1, 0)]);
    assert_eq!(store.hash_cons.allocation_size(), old);
}
