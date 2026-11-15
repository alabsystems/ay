// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual fixed-key hashbrown fixtures; no solver or result credential.

use super::*;
use crate::sort::Sort;
use crate::term::{ControlledTermInternError, Symbol, TermData};
use std::hash::{BuildHasher, Hash, Hasher};

pub(super) fn collision_store() -> (TermStore, Vec<u64>, u64) {
    let mut store = TermStore::new();
    store.hash_cons = Default::default();
    store.hash_cons.try_reserve(112).expect("bounded fixture");
    let mut classes: [Vec<u64>; 256] = std::array::from_fn(|_| Vec::new());
    for key in 0..(256 * 113u64) {
        let mut hash = store.hash_cons.hasher().build_hasher();
        key.hash(&mut hash);
        classes[(hash.finish() & 255) as usize].push(key);
    }
    let mut keys = classes
        .into_iter()
        .find(|keys| keys.len() >= 113)
        .expect("deterministic pigeonhole");
    keys.truncate(113);
    let missing = keys.pop().expect("113th key");
    for &key in &keys {
        store
            .hash_cons
            .insert(key, vec![store.true_term(), store.false_term()]);
    }
    assert_eq!(store.hash_cons.len(), 112);
    assert_eq!(store.hash_cons.capacity(), 112);
    (store, keys, missing)
}

pub(super) fn paid(store: &TermStore) -> usize {
    let mut offered = Vec::new();
    let mut sink = |work, bytes| {
        offered.push((work, bytes));
        true
    };
    let mut admission = Admission {
        progress: &mut sink,
        refused: false,
    };
    assert_eq!(store.controlled_probe_fee(&mut admission), Ok(()));
    drop(admission);
    drop(sink);
    let expected = work(store.hash_cons.allocation_size(), store.hash_cons.len())
        .expect("pinned actual layout");
    assert_eq!(offered, vec![(expected, 0)]);
    expected
}

fn row(store: &TermStore) -> Vec<TermId> {
    vec![store.true_term(), store.false_term()]
}

fn malformed_bucket() {
    let mut store = TermStore::new();
    let term = TermData::App(Symbol::named("dead_collision_row"), Vec::new());
    let hash = TermStore::compute_hash(&term);
    store.hash_cons.insert(hash, vec![TermId(u32::MAX)]);
    let before = store.len();
    let mut collision_rows = 0;
    assert_eq!(
        store.try_intern_with_progress(&term, &Sort::Bool, &mut |work, _| {
            collision_rows += usize::from(work == 256);
            true
        }),
        Err(ControlledTermInternError::InvalidInput)
    );
    assert_eq!(
        collision_rows, 1,
        "full row equality prepaid before live-ID check"
    );
    assert_eq!(store.len(), before);
}

#[test]
fn real_fixed_hash_complete_missing_and_malformed_rows_keep_owned_headers() {
    let (store, keys, missing) = collision_store();
    let pointers = keys
        .iter()
        .map(|key| store.hash_cons.get(key).expect("fixture").as_ptr())
        .collect::<Vec<_>>();
    for (&key, &pointer) in keys.iter().zip(&pointers) {
        paid(&store);
        let found = store.hash_cons.get(&key).expect("complete row");
        assert_eq!(found, &row(&store));
        assert_eq!(found.as_ptr(), pointer);
    }
    paid(&store);
    assert!(store.hash_cons.get(&missing).is_none());
    malformed_bucket();
}

#[test]
fn real_deleted_groups_keep_whole_backing_domain_for_missing_queries() {
    let (mut store, keys, missing) = collision_store();
    let allocation = store.hash_cons.allocation_size();
    for &key in keys.iter().take(80) {
        assert_eq!(store.hash_cons.remove(&key), Some(row(&store)));
        assert_eq!(
            store.hash_cons.capacity(),
            store.hash_cons.len(),
            "real DELETED"
        );
        assert_eq!(store.hash_cons.allocation_size(), allocation);
    }
    assert_eq!(store.hash_cons.len(), 32);
    let full = work(allocation, 112).expect("primary layout");
    assert_eq!(paid(&store) + 32 * 80, full);
    assert!(store.hash_cons.get(&missing).is_none());
    for &key in &keys {
        paid(&store);
        assert_eq!(
            store.hash_cons.contains_key(&key),
            !keys[..80].contains(&key)
        );
    }
}

#[test]
fn real_small_table_queries_include_padded_and_mirrored_control_tags() {
    let mut store = TermStore::new();
    store.hash_cons = Default::default();
    store.hash_cons.try_reserve(3).expect("four buckets");
    for key in [0u64, 1, 2] {
        store.hash_cons.insert(key, row(&store));
    }
    assert_eq!(store.hash_cons.capacity(), 3);
    let allocation = store.hash_cons.allocation_size();
    let group = allocation % 33;
    assert_eq!(allocation / 33, 4);
    assert!(matches!(group, 4 | 8 | 16));
    for key in 0..16 {
        paid(&store);
        assert_eq!(store.hash_cons.get(&key).is_some(), key < 3);
    }
}

#[test]
fn prepaid_get_mut_and_reserved_insert_preserve_complete_owned_headers() {
    let (mut store, keys, missing) = collision_store();
    store
        .hash_cons
        .try_reserve(1)
        .expect("separately priced reserve fixture");
    let allocation = store.hash_cons.allocation_size();
    let true_term = store.true_term();
    paid(&store);
    store
        .hash_cons
        .get_mut(&keys[0])
        .expect("complete row")
        .push(true_term);
    let new_row = row(&store);
    paid(&store);
    assert_eq!(store.hash_cons.insert(missing, new_row), None);
    assert_eq!(
        store.hash_cons.allocation_size(),
        allocation,
        "reserved commit"
    );
    assert_eq!(store.hash_cons.get(&missing), Some(&row(&store)));
    assert_eq!(
        store.hash_cons.get(&keys[0]).expect("retained"),
        &[store.true_term(), store.false_term(), store.true_term()]
    );
}
