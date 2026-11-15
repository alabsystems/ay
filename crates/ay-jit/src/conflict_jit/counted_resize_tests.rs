// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, FiniteAdmissionGrant};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

fn owner(work: u64, storage: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, storage),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

fn filled(capacity: usize) -> ConflictProcessorOutput {
    let mut output = ConflictProcessorOutput::new(capacity);
    for (at, slot) in output.buf.iter_mut().enumerate() {
        *slot = at as u32 + 1;
    }
    output
}

#[test]
fn actual_resize_growth_shrink_and_reset_match_unadmitted_layout_and_capacity() {
    for (old, new) in [(64, 96), (128, 65), (64, 64)] {
        let mut expected = filled(old);
        expected.resize(new);
        let mut actual = filled(old);
        let original = actual.buf.clone();
        let owner = owner(100_000, 100_000);
        actual.prepare_counted_resize(new, &owner).unwrap();
        assert_eq!(actual.capacity(), old);
        assert_eq!(
            actual.buf, original,
            "preparation may reserve, not execute the operation"
        );
        actual.resize(new);
        assert_eq!(actual.capacity(), expected.capacity());
        assert_eq!(actual.buf, expected.buf);
        assert_eq!(actual.buf.capacity(), expected.buf.capacity());
        if old == new {
            assert_eq!(owner.usage().unwrap().work_admitted, 4);
        }
    }
}

#[test]
fn real_resize_exact_and_one_short_work_storage_preserve_pre_mutation_boundary() {
    let owner = owner(100_000, 100_000);
    let mut baseline = filled(64);
    baseline.prepare_counted_resize(96, &owner).unwrap();
    baseline.resize(96);
    let used = owner.usage().unwrap();
    assert!(used.work_admitted > 4 && used.storage_admitted > 0);
    for (work, storage, refusal) in [
        (used.work_admitted, used.storage_admitted, None),
        (
            used.work_admitted - 1,
            used.storage_admitted,
            Some(CountedAdmissionError::WorkExhausted),
        ),
        (
            used.work_admitted,
            used.storage_admitted - 1,
            Some(CountedAdmissionError::StorageExhausted),
        ),
    ] {
        let owner = self::owner(work, storage);
        let mut actual = filled(64);
        let before = actual.buf.clone();
        let result = actual.prepare_counted_resize(96, &owner);
        if let Some(error) = refusal {
            assert_eq!(result, Err(error));
            assert_eq!(actual.buf, before);
            assert_eq!(actual.capacity(), 64);
            let frozen = owner.usage().unwrap();
            assert_eq!(actual.prepare_counted_resize(96, &owner), Err(error));
            assert_eq!(owner.usage().unwrap(), frozen);
        } else {
            result.unwrap();
            actual.resize(96);
            assert_eq!(actual.buf, baseline.buf);
            assert_eq!(owner.usage().unwrap().work_remaining, 0);
            assert_eq!(owner.usage().unwrap().storage_remaining, 0);
        }
    }
}

#[test]
fn each_real_resize_reservation_poll_can_stop_before_buffer_mutation() {
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let baseline_owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000, 100_000),
        None,
        Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst);
            false
        }),
    )
    .unwrap();
    filled(64)
        .prepare_counted_resize(96, &baseline_owner)
        .unwrap();
    let total = calls.load(Ordering::SeqCst);
    assert!(total >= 2);
    for cut in 0..total {
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(100_000, 100_000),
            None,
            Arc::new(move || observed.fetch_add(1, Ordering::SeqCst) == cut),
        )
        .unwrap();
        let mut actual = filled(64);
        let before = actual.buf.clone();
        assert!(actual.prepare_counted_resize(96, &owner).is_err());
        assert_eq!(actual.buf, before);
        assert_eq!(actual.capacity(), 64);
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
    }
}
