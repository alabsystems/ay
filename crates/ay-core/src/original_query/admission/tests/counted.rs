// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod controls;
mod current_callback;
mod deadlines;
mod waiting;

fn counted(work: u64, bytes: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        None,
        Arc::new(|| false),
    )
    .expect("capture counted owner")
}

#[test]
fn absent_deadline_stays_absent_and_zero_grant_cannot_admit_a_decision() {
    let owner = counted(0, 0);
    assert_eq!(owner.deadline(), None);
    owner
        .check()
        .expect("a zero-cost final poll is not a decision");
    assert_eq!(owner.admit(1, 0), Err(CountedAdmissionError::WorkExhausted));
    assert_eq!(
        owner.clone().check(),
        Err(CountedAdmissionError::WorkExhausted)
    );
    let usage = owner.usage().unwrap();
    assert_eq!(usage.version, COUNTED_ADMISSION_USAGE_VERSION);
    assert_eq!((usage.work_admitted, usage.storage_admitted), (0, 0));
    assert_eq!(usage.refusal, Some(CountedAdmissionError::WorkExhausted));
}

#[test]
fn direct_and_scoped_clone_admissions_share_the_exact_original_grant() {
    let owner = counted(9, 13);
    let clone = owner.clone();
    owner.admit(4, 7).unwrap();
    clone.with_work(|work| work.admit(5, 6)).unwrap();
    owner.check().unwrap();
    let usage = owner.usage().unwrap();
    assert_eq!((usage.work_granted, usage.storage_granted), (9, 13));
    assert_eq!((usage.work_admitted, usage.storage_admitted), (9, 13));
    assert_eq!((usage.work_remaining, usage.storage_remaining), (0, 0));
    assert_eq!(usage.refusal, None);
    assert_eq!(
        clone.admit(0, 1),
        Err(CountedAdmissionError::StorageExhausted)
    );
    assert_eq!(owner.check(), Err(CountedAdmissionError::StorageExhausted));
}

#[test]
fn short_paired_grants_are_typed_atomic_and_terminal() {
    for (work, bytes, expected) in [
        (2, 8, CountedAdmissionError::WorkExhausted),
        (8, 2, CountedAdmissionError::StorageExhausted),
    ] {
        let owner = counted(work, bytes);
        assert_eq!(owner.with_work(|work| work.admit(3, 3)), Err(expected));
        let usage = owner.usage().unwrap();
        assert_eq!((usage.work_admitted, usage.storage_admitted), (0, 0));
        assert_eq!(
            (usage.work_remaining, usage.storage_remaining),
            (work, bytes)
        );
        assert_eq!(owner.clone().with_work(|_| Ok(())), Err(expected));
    }
}

#[test]
fn concurrent_counted_clones_cannot_create_nested_credit() {
    let owner = counted(120, 200);
    let barrier = Arc::new(std::sync::Barrier::new(3));
    let mut threads = Vec::new();
    for _ in 0..2 {
        let clone = owner.clone();
        let barrier = Arc::clone(&barrier);
        threads.push(std::thread::spawn(move || {
            barrier.wait();
            clone.with_work(|work| {
                for _ in 0..10 {
                    work.admit(6, 10)?;
                }
                Ok(())
            })
        }));
    }
    barrier.wait();
    for thread in threads {
        assert_eq!(thread.join().unwrap(), Ok(()));
    }
    let usage = owner.usage().unwrap();
    assert_eq!((usage.work_admitted, usage.storage_admitted), (120, 200));
    assert_eq!(owner.admit(1, 0), Err(CountedAdmissionError::WorkExhausted));
}

#[test]
fn explicit_refusal_and_ignored_adapter_failure_remain_original() {
    let owner = counted(20, 20);
    assert_eq!(
        owner.with_work(|work| {
            work.refuse_exhaustion();
            Ok(())
        }),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::Query(QueryError::Exhausted)
        ))
    );
    assert_eq!(
        owner.refuse(CountedAdmissionError::StorageExhausted),
        CountedAdmissionError::Original(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(owner.usage().unwrap().work_admitted, 0);
}

#[test]
fn a_receipt_does_not_poll_or_authorize_after_external_cancellation() {
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(1, 1),
        None,
        Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst);
            true
        }),
    )
    .unwrap();
    assert_eq!(owner.usage().unwrap().refusal, None);
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    let expected = CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped);
    assert_eq!(owner.check(), Err(expected));
    assert_eq!(owner.usage().unwrap().refusal, Some(expected));
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}
