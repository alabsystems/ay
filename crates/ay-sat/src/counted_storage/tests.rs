// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn reserve_refusal_leaves_buffer_and_capacity_unchanged() {
    let owner = test_owner(1, 100_000);
    let mut values = vec![1u32, 2, 3];
    let capacity = values.capacity();
    assert_eq!(
        try_reserve(&owner, &mut values, capacity),
        Err(CountedAdmissionError::WorkExhausted)
    );
    assert_eq!(values, [1, 2, 3]);
    assert_eq!(values.capacity(), capacity);
    assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
}

#[test]
fn allocation_charge_precedes_even_the_first_value() {
    let owner = test_owner(100_000, 7);
    let mut created = 0;
    let result = try_vec_with(&owner, 8, |_| {
        created += 1;
        0u8
    });
    assert_eq!(result, Err(CountedAdmissionError::StorageExhausted));
    assert_eq!(created, 0);
}

#[test]
fn each_value_is_admitted_before_its_initializer() {
    let baseline = test_owner(100_000, 100_000);
    drop(try_reserved_exact::<u8>(&baseline, 4).unwrap());
    // Pay the measured reservation and exactly two element initializers.
    let owner = test_owner(baseline.usage().unwrap().work_admitted + 2, 100_000);
    let mut created = 0;
    let result = try_vec_with(&owner, 4, |_| {
        created += 1;
        0u8
    });
    assert_eq!(result, Err(CountedAdmissionError::WorkExhausted));
    assert_eq!(created, 2);
}

#[test]
fn initial_capacity_matches_ordinary_construction() {
    for size in [0, 1, 3, 8, 13] {
        let owner = test_owner(100_000, 100_000);
        let bytes = try_vec_with(&owner, size, |_| 0u8).unwrap();
        let ordinary_bytes = vec![0u8; size];
        assert_eq!(bytes.capacity(), ordinary_bytes.capacity());
        let words = try_vec_with(&owner, size, |_| 0u64).unwrap();
        let ordinary_words = vec![0u64; size];
        assert_eq!(words.capacity(), ordinary_words.capacity());
        let large = try_reserved_exact::<[u8; 1025]>(&owner, size).unwrap();
        assert_eq!(
            large.capacity(),
            Vec::<[u8; 1025]>::with_capacity(size).capacity()
        );
    }
}

#[test]
fn growth_capacity_matches_ordinary_vec_for_small_and_large_elements() {
    fn compare<T: Clone>(value: T) {
        let owner = test_owner(1_000_000, 1_000_000);
        let mut counted = Vec::new();
        let mut ordinary = Vec::new();
        for _ in 0..17 {
            try_reserve(&owner, &mut counted, 1).unwrap();
            counted.push(value.clone());
            ordinary.push(value.clone());
            assert_eq!(counted.capacity(), ordinary.capacity());
        }
    }
    compare(0u8);
    compare(0u64);
    compare([0u8; 1025]);
}

#[test]
fn overflow_latches_the_same_owner_before_allocating() {
    let owner = test_owner(100_000, usize::MAX);
    let mut values = Vec::<u64>::new();
    assert_eq!(
        try_reserve(&owner, &mut values, usize::MAX),
        Err(CountedAdmissionError::StorageExhausted)
    );
    assert_eq!(values.capacity(), 0);
    assert_eq!(owner.usage().unwrap().storage_admitted, 0);
    assert_eq!(
        checked_double(&owner, 0),
        Err(CountedAdmissionError::StorageExhausted)
    );
}
