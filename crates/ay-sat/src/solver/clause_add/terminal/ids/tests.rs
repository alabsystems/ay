// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::test_owner;

const SMALL_BUCKETS: [usize; 16] = [4, 4, 4, 4, 8, 8, 8, 8, 16, 16, 16, 16, 16, 16, 16, 32];

fn bytes(buckets: usize) -> usize {
    buckets * (std::mem::size_of::<u64>() + 1) + 31
}

#[test]
fn small_table_reservation_has_exact_admitted_capacity_and_real_layout() {
    for (len, &buckets) in SMALL_BUCKETS.iter().enumerate() {
        assert_eq!(reserved_buckets(len), Some(buckets));
        let storage = bytes(buckets);
        let owner = test_owner((8 + storage * 2) as u64, storage);
        let mut actual = new(len, &owner).unwrap();
        let mut ordinary = crate::kani_compat::det_hash_set_with_capacity(len);
        assert_eq!(actual.capacity(), ordinary.capacity());
        assert_eq!(actual.allocation_size(), ordinary.allocation_size());
        assert!(actual.allocation_size() <= storage);
        let initial_size = actual.allocation_size();
        for index in 0..len {
            let value = index as u64;
            assert_eq!(actual.insert(value), ordinary.insert(value));
        }
        assert_eq!(actual.allocation_size(), initial_size);
        assert_eq!(actual, ordinary);
        let usage = owner.usage().unwrap();
        assert_eq!(usage.work_remaining, 0);
        assert_eq!(usage.storage_remaining, 0);
    }
}

#[test]
fn small_table_one_short_storage_refuses_before_reservation_charge() {
    for (len, &buckets) in SMALL_BUCKETS.iter().enumerate() {
        let owner = test_owner(1_000_000, bytes(buckets) - 1);
        assert!(matches!(
            new(len, &owner),
            Err(CountedAdmissionError::StorageExhausted)
        ));
        let usage = owner.usage().unwrap();
        assert_eq!(usage.storage_admitted, 0);
        assert_eq!(usage.work_admitted, 8);
        assert!(new(len, &owner).is_err());
        assert_eq!(owner.usage().unwrap(), usage);
    }
}

#[test]
fn small_table_one_short_work_refuses_before_reservation_charge() {
    for (len, &buckets) in SMALL_BUCKETS.iter().enumerate() {
        let storage = bytes(buckets);
        let owner = test_owner((8 + storage * 2 - 1) as u64, storage);
        assert!(matches!(
            new(len, &owner),
            Err(CountedAdmissionError::WorkExhausted)
        ));
        assert_eq!(owner.usage().unwrap().storage_admitted, 0);
        assert_eq!(owner.usage().unwrap().work_admitted, 8);
    }
}

#[test]
fn small_table_bound_covers_pinned_eight_and_sixteen_byte_control_layouts() {
    let element = std::mem::size_of::<u64>();
    assert!(element >= 4);
    for (len, &expected) in SMALL_BUCKETS.iter().enumerate() {
        let buckets = reserved_buckets(len).unwrap();
        assert_eq!(buckets, expected);
        for group in [8usize, 16] {
            // Pinned TableLayout::calculate_layout_for, excluding the empty
            // set's actual zero allocation: alignment padding plus controls.
            let alignment = group.max(std::mem::align_of::<u64>());
            let controls = (buckets * element + alignment - 1) & !(alignment - 1);
            let actual = controls + buckets + group;
            assert!(bytes(buckets) >= actual, "len={len}, group={group}");
        }
    }
}

#[test]
fn large_capacity_bound_and_overflow_do_not_allocate_or_renew_allowance() {
    for (len, buckets) in [(16, 32), (28, 32), (29, 64), (56, 64), (57, 128)] {
        assert_eq!(reserved_buckets(len), Some(buckets));
    }
    assert_eq!(reserved_buckets(usize::MAX), None);
    let owner = test_owner(1_000_000, 1_000_000);
    assert!(matches!(
        new(usize::MAX, &owner),
        Err(CountedAdmissionError::StorageExhausted)
    ));
    assert_eq!(owner.usage().unwrap().storage_admitted, 0);
    let before = owner.usage().unwrap();
    assert!(new(4, &owner).is_err());
    assert_eq!(owner.usage().unwrap(), before);
}
