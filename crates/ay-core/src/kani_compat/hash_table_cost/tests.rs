// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::kani_compat::DetHashMap;
use std::hash::{BuildHasher, Hash, Hasher};

#[test]
fn hash_table_cost_pinned_layouts_keep_group_fee_and_small_mirrors() {
    type Header = (String, Vec<u8>);
    for group in [4, 8, 16] {
        for buckets in [4, 8, 16, 128] {
            let bytes = allocation::<Header>(buckets, group).unwrap();
            let len = capacity(buckets).unwrap();
            let (groups, candidates) = search(
                Geometry {
                    buckets,
                    group,
                    allocation: bytes,
                },
                len,
            )
            .unwrap();
            assert_eq!(
                fixed_lookup::<Header>(bytes, len),
                Some(512 + 128 * groups + 32 * candidates)
            );
            assert_eq!(
                string_lookup::<Header>(bytes, len, 100),
                Some(1024 + 1600 + 128 * groups + 264 * candidates)
            );
            let cost = reserve_one::<Header>(bytes, len, len).unwrap();
            assert!(cost.rehashes);
            assert_eq!(
                cost.storage_bytes,
                bytes + allocation::<Header>(buckets * 2, group).unwrap()
            );
            assert!(cost.work >= 128 * (3 * buckets + 96 + 32 * len));
        }
    }
}

#[test]
fn hash_table_cost_empty_and_actual_remaining_growth_have_no_virtual_slots() {
    type Header = (String, Vec<u8>);
    let empty = reserve_one::<Header>(0, 0, 0).unwrap();
    assert_eq!(empty.work, 100 * 128);
    assert!(!empty.rehashes);
    assert_eq!(empty.storage_bytes, allocation::<Header>(4, 16).unwrap());
    assert_eq!(fixed_lookup::<Header>(0, 0), Some(640));
    let mut map = DetHashMap::<String, Vec<u8>>::default();
    map.try_reserve(16).unwrap();
    let cost = reserve_one::<Header>(map.allocation_size(), map.len(), map.capacity()).unwrap();
    assert_eq!(
        cost,
        ReserveCost {
            work: 512,
            storage_bytes: 0,
            rehashes: false
        }
    );
}

#[test]
fn hash_table_cost_ambiguous_small_layout_keeps_only_compatible_capacity() {
    // e=1: L36 could mean B4/g16 (capacity3) or B16/g4 (capacity14).
    // The actual capacity excludes the former without vetoing the latter.
    assert_eq!(allocation::<u8>(4, 16), Some(36));
    assert_eq!(allocation::<u8>(16, 4), Some(36));
    assert_eq!(
        reserve_one::<u8>(36, 1, 14),
        Some(ReserveCost {
            work: 512,
            storage_bytes: 0,
            rehashes: false,
        })
    );
    assert!(reserve_one::<u8>(36, 1, 15).is_none());
}

#[test]
fn hash_table_cost_rejects_invalid_layout_overflow_and_inconsistent_lengths() {
    type Header = (String, Vec<u8>);
    for bytes in [1, 32, 129, usize::MAX] {
        assert!(fixed_lookup::<Header>(bytes, 0).is_none());
        assert!(reserve_one::<Header>(bytes, 0, 0).is_none());
    }
    assert!(fixed_lookup::<Header>(0, 1).is_none());
    assert!(reserve_one::<Header>(0, 1, 1).is_none());
    let bytes = allocation::<Header>(4, 8).unwrap();
    assert!(reserve_one::<Header>(bytes, 4, 4).is_none());
    assert!(reserve_one::<Header>(bytes, 2, 1).is_none());
    assert!(reserve_one::<Header>(bytes, 1, 4).is_none());
    assert!(string_lookup::<Header>(bytes, 2, usize::MAX).is_none());
    assert!(string_hash_payload(usize::MAX).is_none());
}

fn collisions<K: Hash + Eq + Clone>(key: impl Fn(usize) -> K) -> DetHashMap<K, Vec<u8>> {
    let mut map = DetHashMap::default();
    map.try_reserve(112).unwrap();
    let mut classes: [Vec<K>; 256] = std::array::from_fn(|_| Vec::new());
    // Pigeonhole supplies actual low-eight-bit collisions, also after doubling.
    for i in 0..(256 * 113) {
        let value = key(i);
        let mut hash = map.hasher().build_hasher();
        value.hash(&mut hash);
        classes[(hash.finish() & 255) as usize].push(value);
    }
    let class = classes.into_iter().find(|row| row.len() >= 113).unwrap();
    for (i, key) in class.into_iter().take(112).enumerate() {
        map.insert(key, vec![i as u8, 17, 29]);
    }
    assert_eq!(map.len(), 112);
    assert_eq!(map.capacity(), 112);
    map
}

fn preserve_rows<K: Eq + Hash + Clone>(map: &mut DetHashMap<K, Vec<u8>>) {
    let before: Vec<_> = map
        .iter()
        .map(|(k, v)| (k.clone(), v.clone(), v.as_ptr()))
        .collect();
    let cost =
        reserve_one::<(K, Vec<u8>)>(map.allocation_size(), map.len(), map.capacity()).unwrap();
    assert!(cost.rehashes);
    assert!(cost.work > 0);
    map.try_reserve(1).unwrap();
    for (key, value, pointer) in before {
        let row = map.get(&key).unwrap();
        assert_eq!(*row, value);
        assert_eq!(
            row.as_ptr(),
            pointer,
            "rehash moves the header, never its payload"
        );
    }
}

#[test]
fn hash_table_cost_real_colliding_fixed_and_string_resizes_preserve_owned_rows() {
    let mut fixed = collisions(|i| i as u64);
    let old_fixed = fixed.allocation_size();
    preserve_rows(&mut fixed);
    assert!(fixed.allocation_size() > old_fixed);
    let mut strings = collisions(|i| format!("retained-key-{i}"));
    let old_strings = strings.allocation_size();
    let payload = strings
        .keys()
        .map(|key| string_hash_payload(key.len()).unwrap())
        .sum::<usize>();
    assert!(payload > strings.len());
    preserve_rows(&mut strings);
    assert!(strings.allocation_size() > old_strings);
}

#[test]
fn hash_table_cost_real_string_tombstones_keep_full_domain_and_rehash_in_place() {
    let mut map = collisions(|i| format!("deleted-key-{i}"));
    let keys: Vec<_> = map.keys().take(80).cloned().collect();
    let allocation = map.allocation_size();
    for key in keys {
        map.remove(&key).unwrap();
        assert_eq!(
            map.capacity(),
            map.len(),
            "actual DELETED tags keep growth exhausted"
        );
        assert_eq!(map.allocation_size(), allocation);
    }
    let cost = reserve_one::<(String, Vec<u8>)>(allocation, map.len(), map.capacity()).unwrap();
    assert!(cost.rehashes);
    assert_eq!(
        cost.storage_bytes, 0,
        "in-place reserve allocates no backing"
    );
    assert!(
        string_lookup::<(String, Vec<u8>)>(allocation, map.len(), 20).unwrap() > 1024 + 16 * 20
    );
    preserve_rows(&mut map);
    assert_eq!(map.allocation_size(), allocation);
}

#[test]
fn hash_table_cost_wide_headers_pay_moves_but_not_owned_payload_copies() {
    type Header = (String, [u64; 128]);
    let mut map = DetHashMap::<String, [u64; 128]>::default();
    for i in 0..3 {
        map.insert(format!("wide-{i}"), [i; 128]);
    }
    assert_eq!(map.len(), map.capacity());
    let cost = reserve_one::<Header>(map.allocation_size(), map.len(), map.capacity()).unwrap();
    assert!(cost.work >= 8 * size_of::<Header>() * map.len());
    let before = map.allocation_size();
    map.try_reserve(1).unwrap();
    assert_eq!(cost.storage_bytes, before + map.allocation_size());
}
