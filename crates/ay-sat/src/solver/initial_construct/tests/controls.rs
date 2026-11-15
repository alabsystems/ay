// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn combined_preparation_construction_ingestion_bcp_has_exact_one_short_boundaries() {
    let rows = [&[lit(0, false)][..], &[lit(0, true), lit(1, false)][..]];
    let measured = owner(10_000_000, 10_000_000);
    drop(construct(2, &rows, measured.clone()).unwrap());
    let used = measured.usage().unwrap();
    let exact = owner(used.work_admitted, used.storage_admitted);
    drop(construct(2, &rows, exact.clone()).unwrap());
    assert_eq!(exact.usage().unwrap().work_remaining, 0);
    assert_eq!(exact.usage().unwrap().storage_remaining, 0);
    for (work, bytes, expected) in [
        (
            used.work_admitted - 1,
            used.storage_admitted,
            CountedAdmissionError::WorkExhausted,
        ),
        (
            used.work_admitted,
            used.storage_admitted - 1,
            CountedAdmissionError::StorageExhausted,
        ),
    ] {
        let short = owner(work, bytes);
        assert_eq!(construct(2, &rows, short.clone()).err(), Some(expected));
        assert_eq!(short.check(), Err(expected));
        assert!(construct(0, &[], short).is_err());
    }
}

#[test]
fn paid_preparation_does_not_supply_a_fresh_constructor_allowance() {
    let original = owner(10000, 10000);
    let prepared = CountedInitialCnf::try_new(1, &[&[lit(0, false)]], original.clone()).unwrap();
    let remaining = original.usage().unwrap().work_remaining as usize;
    original.admit(remaining, 0).unwrap();
    assert_eq!(
        prepared.construct().err(),
        Some(CountedAdmissionError::WorkExhausted)
    );
}

#[test]
fn actual_scratch_cleanup_can_cancel_before_any_engine_is_published() {
    let _ = ay_core::misc_cli_flags();
    let stop = Arc::new(AtomicBool::new(false));
    let watched = Arc::clone(&stop);
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(10_000_000, 10_000_000),
        None,
        Arc::new(move || watched.load(Ordering::SeqCst)),
    )
    .unwrap();
    let prepared = CountedInitialCnf::try_new(1, &[&[lit(0, false)]], original.clone()).unwrap();
    AFTER_SCRATCH_DROP.with(|slot| {
        let stop = Arc::clone(&stop);
        *slot.borrow_mut() = Some(Box::new(move || stop.store(true, Ordering::SeqCst)));
    });
    assert_eq!(
        prepared.construct().err(),
        Some(CountedAdmissionError::Original(
            OriginalAdmissionError::ObserverStopped
        ))
    );
    assert!(stop.load(Ordering::SeqCst));
    stop.store(false, Ordering::SeqCst);
    assert!(construct(0, &[], original).is_err());
}

#[test]
fn failed_partial_engine_is_destroyed_before_cleanup_hook_and_first_refusal_wins() {
    let rows = [&[lit(0, false)][..], &[lit(0, true), lit(1, false)][..]];
    let baseline = owner(10_000_000, 10_000_000);
    drop(construct(2, &rows, baseline.clone()).unwrap());
    let used = baseline.usage().unwrap();
    let short = owner(used.work_admitted - 1, used.storage_admitted);
    let disposed = Arc::new(AtomicBool::new(false));
    AFTER_SCRATCH_DROP.with(|slot| {
        let disposed = Arc::clone(&disposed);
        let short = short.clone();
        *slot.borrow_mut() = Some(Box::new(move || {
            disposed.store(true, Ordering::SeqCst);
            short.refuse(CountedAdmissionError::Original(
                OriginalAdmissionError::ObserverStopped,
            ));
        }));
    });
    assert_eq!(
        construct(2, &rows, short.clone()).err(),
        Some(CountedAdmissionError::WorkExhausted)
    );
    assert!(disposed.load(Ordering::SeqCst));
    assert_eq!(short.check(), Err(CountedAdmissionError::WorkExhausted));
}

#[test]
fn oversized_namespace_refuses_before_eager_variable_allocation() {
    let original = owner(1_000_000, 1_000_000);
    let prepared = CountedInitialCnf::try_new((1 << 30) + 1, &[], original.clone()).unwrap();
    let before = original.usage().unwrap().storage_admitted;
    assert!(prepared.construct().is_err());
    assert_eq!(original.usage().unwrap().storage_admitted, before);
}

#[test]
fn oversized_clause_is_not_truncated_or_silently_skipped() {
    let literals: Vec<_> = (0..60_001).map(|v| lit(v, false)).collect();
    let original = owner(100_000_000, 100_000_000);
    let prepared =
        CountedInitialCnf::try_new(literals.len(), &[&literals], original.clone()).unwrap();
    assert_eq!(
        prepared
            .clause(0)
            .unwrap()
            .unwrap()
            .normalized()
            .unwrap()
            .len(),
        literals.len()
    );
    let before = original.usage().unwrap().storage_admitted;
    assert!(matches!(
        prepared.construct().err(),
        Some(CountedAdmissionError::Original(
            OriginalAdmissionError::Query(QueryError::Invalid(_))
        ))
    ));
    assert_eq!(original.usage().unwrap().storage_admitted, before);
}
