// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]
use super::*;

#[test]
fn every_work_cut_and_exact_boundary_cover_the_real_trace_append() {
    let owner = test_owner(1_000_000, 1_000_000);
    add(&mut fixture(), &owner).unwrap();
    let total = owner.usage().unwrap().work_admitted;
    assert!(total > 50);
    for work in 0..=total {
        let mut trace = fixture();
        let before = rows(&trace);
        let owner = test_owner(work, 1_000_000);
        let result = add(&mut trace, &owner);
        if work == total {
            result.unwrap();
            assert_eq!(owner.usage().unwrap().work_remaining, 0);
        } else {
            assert_eq!(result, Err(CountedAdmissionError::WorkExhausted));
            assert_eq!(rows(&trace), before);
            let receipt = owner.usage().unwrap();
            assert!(add(&mut trace, &owner).is_err());
            assert_eq!(owner.usage().unwrap(), receipt);
        }
    }
}

#[test]
fn exact_and_one_short_storage_pay_real_replacement_peak_copies() {
    let owner = test_owner(1_000_000, 1_000_000);
    add(&mut fixture(), &owner).unwrap();
    let total = owner.usage().unwrap().storage_admitted;
    assert!(total > 0);
    for storage in [total - 1, total] {
        let mut trace = fixture();
        let before = rows(&trace);
        let owner = test_owner(1_000_000, storage);
        let result = add(&mut trace, &owner);
        if storage == total {
            result.unwrap();
            assert_eq!(owner.usage().unwrap().storage_remaining, 0);
        } else {
            assert_eq!(result, Err(CountedAdmissionError::StorageExhausted));
            assert_eq!(rows(&trace), before);
        }
    }
}

fn observer(cut: usize, calls: &Arc<AtomicUsize>) -> CountedAdmission {
    let calls = Arc::clone(calls);
    CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        None,
        Arc::new(move || calls.fetch_add(1, Ordering::SeqCst) == cut),
    )
    .unwrap()
}

#[test]
fn every_preparation_poll_refuses_before_semantic_row_publication() {
    let calls = Arc::new(AtomicUsize::new(0));
    let mut baseline = fixture();
    let owner = observer(usize::MAX, &calls);
    let literals = [pos(0)];
    let token = baseline
        .prepare_counted_add(9, &literals, false, &[1, 2], &owner)
        .unwrap();
    drop(token);
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 10);
    for cut in 0..total {
        let mut trace = fixture();
        let before = rows(&trace);
        let calls = Arc::new(AtomicUsize::new(0));
        let owner = observer(cut, &calls);
        assert!(trace
            .prepare_counted_add(9, &[pos(0)], false, &[1, 2], &owner)
            .is_err());
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        assert_eq!(rows(&trace), before);
        assert_eq!(
            owner.check(),
            Err(CountedAdmissionError::Original(
                OriginalAdmissionError::ObserverStopped
            ))
        );
    }
}

#[test]
fn already_poisoned_trace_cannot_gain_a_new_admitted_row() {
    for storage_poison in [false, true] {
        let mut trace = fixture();
        if storage_poison {
            trace.is_truncated = true;
        } else {
            trace.mark_proof_work_exhausted();
        }
        let before = rows(&trace);
        assert!(add(&mut trace, &test_owner(1_000_000, 1_000_000)).is_err());
        assert_eq!(rows(&trace), before);
    }
}
