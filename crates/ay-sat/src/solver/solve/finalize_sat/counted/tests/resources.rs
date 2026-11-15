// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;

fn baseline() -> ay_core::original_query::AdmissionUsage {
    let mut s = reconstructed();
    let admission = owner();
    attach(&mut s, &admission);
    assert_eq!(
        s.declare_counted_complete_assignment_sat(&admission),
        Ok(SatResult::Sat(vec![true, false, true]))
    );
    admission.usage().unwrap()
}

#[test]
fn every_short_original_work_allowance_refuses_without_model_publication() {
    let usage = baseline();
    assert!(usage.work_admitted > 64);
    for limit in 0..usage.work_admitted {
        let mut s = reconstructed();
        let admission = test_owner(limit, usage.storage_admitted);
        attach(&mut s, &admission);
        assert!(
            s.declare_counted_complete_assignment_sat(&admission)
                .is_err(),
            "{limit}"
        );
        assert_eq!(admission.check(), Err(CountedAdmissionError::WorkExhausted));
        refused(&s, &admission);
    }
}

#[test]
fn every_short_original_storage_allowance_refuses_before_allocation() {
    let usage = baseline();
    assert!(usage.storage_admitted >= 9);
    for limit in 0..usage.storage_admitted {
        let mut s = reconstructed();
        let admission = test_owner(usage.work_admitted, limit);
        attach(&mut s, &admission);
        assert!(
            s.declare_counted_complete_assignment_sat(&admission)
                .is_err(),
            "{limit}"
        );
        assert_eq!(
            admission.check(),
            Err(CountedAdmissionError::StorageExhausted)
        );
        refused(&s, &admission);
    }
}

#[test]
fn exact_grant_succeeds_and_preconsumed_original_credit_is_not_refreshed() {
    let usage = baseline();
    let mut s = reconstructed();
    let admission = test_owner(usage.work_admitted + 7, usage.storage_admitted + 5);
    admission.admit(7, 5).unwrap();
    attach(&mut s, &admission);
    assert_eq!(
        s.declare_counted_complete_assignment_sat(&admission),
        Ok(SatResult::Sat(vec![true, false, true]))
    );
    assert_eq!(admission.usage().unwrap().work_remaining, 0);
    assert_eq!(admission.usage().unwrap().storage_remaining, 0);
    assert!(admission.shares_ledger_with(s.cold.counted_admission.as_ref().unwrap()));
}

#[test]
fn every_observer_cut_including_after_final_validation_is_sticky() {
    let mut s = reconstructed();
    let calls = Arc::new(AtomicUsize::new(0));
    let admission = observed(usize::MAX, &calls);
    attach(&mut s, &admission);
    assert!(matches!(
        s.declare_counted_complete_assignment_sat(&admission),
        Ok(SatResult::Sat(_))
    ));
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 20);
    for cut in 0..total {
        let mut s = reconstructed();
        let calls = Arc::new(AtomicUsize::new(0));
        let admission = observed(cut, &calls);
        attach(&mut s, &admission);
        assert!(
            s.declare_counted_complete_assignment_sat(&admission)
                .is_err(),
            "{cut}/{total}"
        );
        let before = calls.load(Ordering::SeqCst);
        assert!(s
            .declare_counted_complete_assignment_sat(&admission)
            .is_err());
        assert_eq!(calls.load(Ordering::SeqCst), before);
        assert_eq!(
            admission.check(),
            Err(CountedAdmissionError::Original(
                OriginalAdmissionError::ObserverStopped
            ))
        );
        refused(&s, &admission);
    }
}

#[test]
fn expired_original_deadline_cannot_be_renewed_for_model_validation() {
    let mut s = assigned();
    let admission = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        Some(ay_core::time::Instant::now() - std::time::Duration::from_secs(1)),
        Arc::new(|| false),
    )
    .unwrap();
    attach(&mut s, &admission);
    assert_eq!(
        s.declare_counted_complete_assignment_sat(&admission),
        Err(SatUnknownReason::DeadlineExceeded)
    );
    refused(&s, &admission);
}
