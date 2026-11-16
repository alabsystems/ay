// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::test_util::lit;
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmissionError};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

fn owner(work: u64, storage: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, storage),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

#[test]
fn measured_bootstrap_has_exact_work_and_storage_controls() {
    for num_vars in [0, 3, 2049] {
        let baseline = owner(1_000_000, 1_000_000);
        drop(ForwardChecker::try_new_counted(num_vars, 0, &baseline).unwrap());
        let used = baseline.usage().unwrap();
        assert!(used.work_admitted > 0);
        assert!(used.storage_admitted >= 1024 * size_of::<Vec<usize>>());
        let exact = owner(used.work_admitted, used.storage_admitted);
        drop(ForwardChecker::try_new_counted(num_vars, 0, &exact).unwrap());
        assert_eq!(exact.usage().unwrap().work_remaining, 0);
        assert_eq!(exact.usage().unwrap().storage_remaining, 0);
        for (work, storage, error) in [
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
            let short = owner(work, storage);
            assert!(
                matches!(ForwardChecker::try_new_counted(num_vars, 0, &short), Err(e) if e == error)
            );
            let before_retry = short.usage().unwrap();
            assert!(ForwardChecker::try_new_counted(0, 0, &short).is_err());
            assert_eq!(short.usage().unwrap(), before_retry);
        }
    }
}

#[test]
fn no_positive_grant_means_no_even_empty_bootstrap() {
    let original = owner(0, 1_000_000);
    assert!(matches!(
        ForwardChecker::try_new_counted(0, 0, &original),
        Err(CountedAdmissionError::WorkExhausted)
    ));
    let usage = original.usage().unwrap();
    assert_eq!(usage.work_admitted, 0);
    assert_eq!(usage.storage_admitted, 0);
}

fn observing_owner(stop_at: usize, calls: &Arc<AtomicUsize>) -> CountedAdmission {
    let observed = Arc::clone(calls);
    CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        None,
        Arc::new(move || observed.fetch_add(1, Ordering::SeqCst) == stop_at),
    )
    .unwrap()
}

#[test]
fn every_one_shot_callback_and_final_fence_refusal_stays_stopped() {
    let calls = Arc::new(AtomicUsize::new(0));
    let baseline = observing_owner(usize::MAX, &calls);
    drop(ForwardChecker::try_new_counted(2049, 0, &baseline).unwrap());
    let total = calls.load(Ordering::SeqCst);
    assert!(
        total > 20,
        "includes chunk initialization and cleanup fences"
    );
    for stop_at in 0..total {
        let calls = Arc::new(AtomicUsize::new(0));
        let original = observing_owner(stop_at, &calls);
        let error = CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped);
        assert!(
            matches!(ForwardChecker::try_new_counted(2049, 0, &original), Err(e) if e == error)
        );
        let before_retry = original.usage().unwrap();
        let callback_count = calls.load(Ordering::SeqCst);
        assert!(ForwardChecker::try_new_counted(0, 17, &original).is_err());
        assert_eq!(original.check(), Err(error));
        assert_eq!(original.usage().unwrap(), before_retry);
        assert_eq!(calls.load(Ordering::SeqCst), callback_count);
    }
}

#[test]
fn callback_panic_cannot_publish_or_revive_a_checker() {
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        None,
        Arc::new(|| panic!("bootstrap observer panic")),
    )
    .unwrap();
    let error = CountedAdmissionError::Original(OriginalAdmissionError::ObserverPanicked);
    assert!(matches!(ForwardChecker::try_new_counted(2, 0, &original), Err(e) if e == error));
    assert_eq!(original.check(), Err(error));
    assert!(ForwardChecker::try_new_counted(0, 0, &original).is_err());
    assert_eq!(original.usage().unwrap().work_admitted, 0);
}

#[test]
fn universe_or_allocator_refusal_is_terminal_not_an_empty_checker() {
    let original = owner(1_000_000, 1_000_000);
    let result =
        ForwardChecker::try_new_counted(ay_drat_check::checker::MAX_DENSE_VARS + 1, 0, &original);
    let error = CountedAdmissionError::Original(QueryError::Exhausted.into());
    assert!(matches!(result, Err(e) if e == error));
    assert_eq!(original.check(), Err(error));
    assert_eq!(original.usage().unwrap().storage_admitted, 0);
    let failure = Vec::<u64>::new().try_reserve_exact(usize::MAX).unwrap_err();
    assert_eq!(
        construction_error(CheckerConstructionError::Allocation(failure)),
        error
    );
    assert_eq!(
        construction_error(CheckerConstructionError::SizeOverflow),
        error
    );
}

#[test]
fn ordinary_and_counted_sampling_and_rup_behavior_agree() {
    for period in [0, 1, 3] {
        let original = owner(1_000_000, 1_000_000);
        let mut counted = ForwardChecker::try_new_counted(3, period, &original).unwrap();
        let mut ordinary = ForwardChecker::new_sampled(3, period);
        for checker in [&mut counted, &mut ordinary] {
            checker.add_original(&[lit(0, true), lit(1, true)]);
            checker.add_original(&[lit(0, false), lit(1, true)]);
            for _ in 0..6 {
                checker.add_derived(&[lit(1, true)]);
            }
        }
        assert_eq!(counted.sample_period(), ordinary.sample_period());
        assert_eq!(counted.derived_count(), ordinary.derived_count());
        assert_eq!(counted.sampled_checks, ordinary.sampled_checks);
        assert_eq!(counted.sampled_skips, ordinary.sampled_skips);
        assert_eq!(counted.inner.stats(), ordinary.inner.stats());
        assert_eq!(counted.rup_failures(), 0);
        // This parity exercise does not claim post-bootstrap work was counted.
        assert!(original.check().is_ok());
    }
}
