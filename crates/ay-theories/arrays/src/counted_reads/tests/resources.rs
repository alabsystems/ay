// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::OriginalAdmissionError;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

fn sequence(original: &CountedAdmission) -> Result<()> {
    let mut f = fixture(original, IndexRelation::Symbolic)?;
    let closure = CountedArrayReadClosure::derive(&mut f.terms, &[f.root], original)?;
    closure.validate_source(&f.terms)?;
    closure.finish()?;
    drop(f);
    original.check()?;
    Ok(())
}

fn watched(flag: &Arc<AtomicBool>) -> CountedAdmission {
    let observed = Arc::clone(flag);
    CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 256 * 1024 * 1024),
        None,
        Arc::new(move || observed.load(Ordering::SeqCst)),
    )
    .unwrap()
}

#[test]
fn exact_and_one_short_grants_cover_raw_input_closure_validation_and_disposal() {
    let original = ample();
    sequence(&original).unwrap();
    let used = original.usage().unwrap();
    assert!(used.work_admitted > 0 && used.storage_admitted > 0);
    for (work, bytes, expected) in [
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
        let original = owner(work, bytes);
        let result = sequence(&original);
        if let Some(error) = expected {
            assert_eq!(result, Err(Error::Stopped(error)));
            assert_eq!(original.clone().check(), Err(error));
            assert_eq!(original.usage().unwrap().refusal, Some(error));
        } else {
            result.unwrap();
            let actual = original.usage().unwrap();
            assert_eq!((actual.work_remaining, actual.storage_remaining), (0, 0));
        }
    }
}

#[test]
fn repeated_fresh_sequences_have_identical_versioned_receipts() {
    let first = ample();
    let second = ample();
    sequence(&first).unwrap();
    sequence(&second).unwrap();
    assert_eq!(COUNTED_ARRAY_READ_WORK_VERSION, 3);
    assert_eq!(first.usage().unwrap(), second.usage().unwrap());
    assert_eq!(first.deadline(), None);
}

#[test]
fn zero_work_refuses_before_source_mutation() {
    let mut f = fixture(&ample(), IndexRelation::Symbolic).unwrap();
    let before = f.terms.snapshot_stamp();
    let original = owner(0, usize::MAX);
    assert!(matches!(
        CountedArrayReadClosure::derive(&mut f.terms, &[f.root], &original),
        Err(Error::Stopped(CountedAdmissionError::WorkExhausted))
    ));
    assert_eq!(f.terms.snapshot_stamp(), before);
    assert_eq!(original.usage().unwrap().work_admitted, 0);
}

#[test]
fn cancellation_during_closure_stays_terminal_after_the_flag_is_reset() {
    let enabled = Arc::new(AtomicBool::new(false));
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&enabled);
    let counted = Arc::clone(&calls);
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 256 * 1024 * 1024),
        None,
        Arc::new(move || {
            observed.load(Ordering::SeqCst) && counted.fetch_add(1, Ordering::SeqCst) >= 12
        }),
    )
    .unwrap();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    enabled.store(true, Ordering::SeqCst);
    let result = CountedArrayReadClosure::derive(&mut f.terms, &[f.root], &original);
    let error = CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped);
    assert!(matches!(result, Err(Error::Stopped(actual)) if actual == error));
    assert!(calls.load(Ordering::SeqCst) > 12);
    enabled.store(false, Ordering::SeqCst);
    assert_eq!(original.clone().check(), Err(error));
    assert!(
        matches!(CountedArrayReadClosure::derive(&mut f.terms, &[f.root], &original),
        Err(Error::Stopped(actual)) if actual == error)
    );
}

#[test]
fn successful_closure_is_vetoed_by_its_original_cleanup_fence() {
    let stopped = Arc::new(AtomicBool::new(false));
    let original = watched(&stopped);
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let closure = derive_fixture(&mut f, &original);
    let before = original.usage().unwrap();
    stopped.store(true, Ordering::SeqCst);
    let error = CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped);
    assert_eq!(closure.finish(), Err(Error::Stopped(error)));
    stopped.store(false, Ordering::SeqCst);
    assert_eq!(original.clone().check(), Err(error));
    let after = original.usage().unwrap();
    assert_eq!(after.work_admitted, before.work_admitted);
    assert_eq!(
        after.storage_admitted, before.storage_admitted,
        "cleanup cannot refund credit"
    );
}

#[test]
fn replacing_ambient_callback_cannot_remove_the_original_stop() {
    let stopped = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&stopped);
    let scope =
        ay_core::resource::enter_check_stop(Arc::new(move || observed.load(Ordering::SeqCst)));
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    drop(scope);
    let _replacement = ay_core::resource::enter_check_stop(Arc::new(|| false));
    stopped.store(true, Ordering::SeqCst);
    assert!(matches!(
        CountedArrayReadClosure::derive(&mut f.terms, &[f.root], &original),
        Err(Error::Stopped(_))
    ));
    stopped.store(false, Ordering::SeqCst);
    assert!(original.clone().check().is_err());
}

#[test]
fn observer_panic_is_a_sticky_refusal_not_a_closure_result() {
    let enabled = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&enabled);
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 256 * 1024 * 1024),
        None,
        Arc::new(move || {
            assert!(!observed.load(Ordering::SeqCst), "test observer panic");
            false
        }),
    )
    .unwrap();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    enabled.store(true, Ordering::SeqCst);
    let error = CountedAdmissionError::Original(OriginalAdmissionError::ObserverPanicked);
    assert!(
        matches!(CountedArrayReadClosure::derive(&mut f.terms, &[f.root], &original),
        Err(Error::Stopped(actual)) if actual == error)
    );
    enabled.store(false, Ordering::SeqCst);
    assert_eq!(original.check(), Err(error));
}
