// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::test_owner;

fn queued() -> Reap {
    let mut queue = Reap::new();
    for value in [16, 17, 18, 20, 24, 31, 31] {
        queue.push(value);
    }
    queue
}

fn contents(mut queue: Reap) -> Vec<u32> {
    let mut values = Vec::new();
    while !queue.is_empty() {
        values.push(queue.pop());
    }
    values
}

#[test]
fn actual_redistribution_reserves_multiple_destinations_and_preserves_duplicate_order() {
    let mut actual = queued();
    let expected = contents(actual.clone());
    let owner = test_owner(1_000_000, 1_000_000);
    let mut values = Vec::new();
    while !actual.is_empty() {
        values.push(actual.pop_counted(&owner).unwrap());
    }
    assert_eq!(values, expected);
    assert!(owner.usage().unwrap().storage_admitted > size_of::<[usize; 33]>());
    assert!(
        actual
            .buckets
            .iter()
            .filter(|bucket| bucket.capacity() > 0)
            .count()
            > 3
    );
}

#[test]
fn every_redistribution_work_and_storage_cut_preserves_atomic_queue_contents() {
    let mut baseline = queued();
    let owner = test_owner(1_000_000, 1_000_000);
    assert_eq!(baseline.pop_counted(&owner), Ok(16));
    let used = owner.usage().unwrap();
    for work in 0..used.work_admitted {
        let mut actual = queued();
        let before = contents(actual.clone());
        let owner = test_owner(work, used.storage_admitted);
        assert_eq!(
            actual.pop_counted(&owner),
            Err(CountedAdmissionError::WorkExhausted)
        );
        assert_eq!(contents(actual), before);
        assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
    }
    for storage in 0..used.storage_admitted {
        let mut actual = queued();
        let before = contents(actual.clone());
        let owner = test_owner(used.work_admitted, storage);
        assert_eq!(
            actual.pop_counted(&owner),
            Err(CountedAdmissionError::StorageExhausted)
        );
        assert_eq!(contents(actual), before);
    }
    let mut exact = queued();
    let owner = test_owner(used.work_admitted, used.storage_admitted);
    assert_eq!(exact.pop_counted(&owner), Ok(16));
}

#[test]
fn counted_push_and_pop_match_ordinary_for_every_u32_radix_bucket() {
    let owner = test_owner(1_000_000, 1_000_000);
    let mut actual = Reap::new();
    let mut ordinary = Reap::new();
    for value in (0..32).map(|bit| 1u32 << bit).chain([0, 0, u32::MAX]) {
        ordinary.push(value);
        actual.push_counted(value, &owner).unwrap();
    }
    while !ordinary.is_empty() {
        assert_eq!(actual.pop_counted(&owner).unwrap(), ordinary.pop());
    }
    assert_eq!(actual.len(), 0);
}

#[test]
fn invalid_monotone_push_is_sticky_without_changing_real_queue() {
    let mut queue = queued();
    assert_eq!(queue.pop(), 16);
    let expected = contents(queue.clone());
    let owner = test_owner(1_000_000, 1_000_000);
    assert!(queue.push_counted(15, &owner).is_err());
    assert_eq!(contents(queue.clone()), expected);
    let receipt = owner.usage().unwrap();
    assert!(queue.push_counted(32, &owner).is_err());
    assert_eq!(owner.usage().unwrap(), receipt);
    assert_eq!(contents(queue), expected);
}
