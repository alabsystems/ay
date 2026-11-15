// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn zero_grants_do_not_acquire_even_an_empty_formula() {
    for (work, storage, expected) in [
        (0, 1000, CountedAdmissionError::WorkExhausted),
        (1000, 0, CountedAdmissionError::StorageExhausted),
    ] {
        let original = owner(work, storage);
        assert_eq!(
            CountedInitialCnf::try_new(0, &[], original.clone()).err(),
            Some(expected)
        );
        assert_eq!(original.usage().unwrap().work_admitted, 0);
        assert_eq!(original.usage().unwrap().storage_admitted, 0);
    }
}

#[test]
fn malformed_literals_and_namespace_refuse_the_same_owner_permanently() {
    for (variables, literals) in [
        (1, vec![literal(1, false)]),
        (i32::MAX as usize + 1, Vec::new()),
    ] {
        let original = owner(1000, 1000);
        let result = CountedInitialCnf::try_new(variables, &[&literals], original.clone());
        assert!(matches!(
            result.err(),
            Some(CountedAdmissionError::Original(
                OriginalAdmissionError::Query(QueryError::Invalid(_))
            ))
        ));
        assert!(CountedInitialCnf::try_new(0, &[], original.clone()).is_err());
        assert!(original.check().is_err());
    }
}

#[test]
fn refused_growth_does_not_resize_or_modify_the_buffer() {
    let mut values = vec![literal(0, true), literal(1, false)];
    let before = values.clone();
    let capacity = values.capacity();
    let original = owner(1, 10000);
    assert_eq!(
        storage::reserve_append(&mut values, capacity + 1, &original),
        Err(CountedAdmissionError::WorkExhausted)
    );
    assert_eq!(values, before);
    assert_eq!(values.capacity(), capacity);
}

#[test]
fn overflow_refuses_before_allocation() {
    let mut values = vec![literal(0, true)];
    let original = owner(1000, usize::MAX);
    assert_eq!(
        storage::reserve_append(&mut values, usize::MAX, &original),
        Err(CountedAdmissionError::StorageExhausted)
    );
    assert_eq!(values, [literal(0, true)]);
    assert_eq!(original.usage().unwrap().storage_admitted, 0);
}

#[test]
fn scratch_disposal_can_veto_success_after_real_normalization() {
    let stopped = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&stopped);
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(10000, 10000),
        None,
        Arc::new(move || observed.load(Ordering::SeqCst)),
    )
    .unwrap();
    normalize::AFTER_SCRATCH_DROP.with(|hook| {
        let stopped = Arc::clone(&stopped);
        *hook.borrow_mut() = Some(Box::new(move || stopped.store(true, Ordering::SeqCst)));
    });
    assert_eq!(
        prepare(&input(), original.clone()).err(),
        Some(CountedAdmissionError::Original(
            OriginalAdmissionError::ObserverStopped
        ))
    );
    assert!(stopped.load(Ordering::SeqCst));
    assert!(original.usage().unwrap().work_admitted > 20);
    stopped.store(false, Ordering::SeqCst);
    assert!(prepare(&input(), original.clone()).is_err());
}

#[test]
fn observer_refusal_during_preparation_discards_partial_buffers_and_cannot_revive() {
    let calls = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&calls);
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(10000, 10000),
        None,
        Arc::new(move || counted.fetch_add(1, Ordering::SeqCst) == 45),
    )
    .unwrap();
    let clauses = input();
    let before = clauses.clone();
    let discarded = Arc::new(AtomicBool::new(false));
    normalize::AFTER_SCRATCH_DROP.with(|hook| {
        let discarded = Arc::clone(&discarded);
        *hook.borrow_mut() = Some(Box::new(move || discarded.store(true, Ordering::SeqCst)));
    });
    assert!(prepare(&clauses, original.clone()).is_err());
    assert!(discarded.load(Ordering::SeqCst));
    assert_eq!(clauses, before);
    assert!(prepare(&clauses, original.clone()).is_err());
    assert_eq!(calls.load(Ordering::SeqCst), 46);
}

#[test]
fn prepared_views_and_other_consumers_share_one_terminal_balance() {
    let original = owner(10000, 10000);
    let prepared = prepare(&input(), original.clone()).unwrap();
    let remaining = original.usage().unwrap().work_remaining;
    original.admit(remaining as usize, 0).unwrap();
    assert_eq!(
        prepared.clause(0).err(),
        Some(CountedAdmissionError::WorkExhausted)
    );
    assert_eq!(
        prepared.dispose(),
        Err(CountedAdmissionError::WorkExhausted)
    );
    assert_eq!(original.check(), Err(CountedAdmissionError::WorkExhausted));
}

#[test]
fn large_input_with_short_credit_stops_before_copying_or_sorting_it() {
    let clause = vec![literal(0, true); 100_000];
    let original = owner(100, 10_000_000);
    assert_eq!(
        CountedInitialCnf::try_new(1, &[&clause], original.clone()).err(),
        Some(CountedAdmissionError::WorkExhausted)
    );
    let usage = original.usage().unwrap();
    assert!(usage.work_admitted < 10);
    assert!(usage.storage_admitted < 1000);
}
