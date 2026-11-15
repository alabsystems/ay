// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_and_short_work_storage_account_for_resolution_lbd_and_retirement() {
    let (mut baseline, conflict, _) = fixture(2, Reasons::Long);
    let original = test_owner(10_000_000, 10_000_000);
    attach(&mut baseline, &original);
    let expected = run(&mut baseline, conflict).unwrap();
    let used = original.usage().unwrap();
    assert!(used.storage_admitted > 0);
    for (work, storage, error) in [
        (
            0,
            used.storage_admitted,
            Some(CountedAdmissionError::WorkExhausted),
        ),
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
        (used.work_admitted, used.storage_admitted, None),
    ] {
        let (mut s, conflict, _) = fixture(2, Reasons::Long);
        let before = state(&s);
        let owner = test_owner(work, storage);
        attach(&mut s, &owner);
        let result = run(&mut s, conflict);
        if let Some(error) = error {
            assert_eq!(result, Err(SatUnknownReason::ResourceBudget));
            assert_eq!(owner.check(), Err(error));
            let receipt = owner.usage().unwrap();
            assert_eq!(run(&mut s, conflict), result);
            assert_eq!(owner.usage().unwrap(), receipt);
        } else {
            assert_eq!(result, Ok(expected.clone()));
            assert_eq!(owner.usage().unwrap().work_remaining, 0);
            assert_eq!(owner.usage().unwrap().storage_remaining, 0);
        }
        assert_eq!(state(&s), before);
        clean(&s);
    }
}

#[test]
fn every_short_work_cut_retires_partial_seen_and_level_scratch() {
    let (mut baseline, conflict, _) = fixture(1, Reasons::Long);
    let original = test_owner(10_000_000, 10_000_000);
    attach(&mut baseline, &original);
    assert!(run(&mut baseline, conflict).unwrap().is_some());
    for work in 0..original.usage().unwrap().work_admitted {
        let (mut s, conflict, _) = fixture(1, Reasons::Long);
        let before = state(&s);
        let owner = test_owner(work, 10_000_000);
        attach(&mut s, &owner);
        assert_eq!(
            run(&mut s, conflict),
            Err(SatUnknownReason::ResourceBudget),
            "cut {work}"
        );
        assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
        assert_eq!(state(&s), before);
        clean(&s);
    }
}

#[test]
fn every_observer_cut_including_final_retirement_fence_is_terminal() {
    let (mut baseline, conflict, _) = fixture(2, Reasons::Long);
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut baseline, &observing_owner(usize::MAX, &calls));
    assert!(run(&mut baseline, conflict).unwrap().is_some());
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 10);
    for at in 0..total {
        let (mut s, conflict, _) = fixture(2, Reasons::Long);
        let before = state(&s);
        let calls = Arc::new(AtomicUsize::new(0));
        let owner = observing_owner(at, &calls);
        attach(&mut s, &owner);
        assert_eq!(
            run(&mut s, conflict),
            Err(SatUnknownReason::Interrupted),
            "observer {at}"
        );
        assert_eq!(run(&mut s, conflict), Err(SatUnknownReason::Interrupted));
        assert_eq!(calls.load(Ordering::SeqCst), at + 1);
        assert_eq!(state(&s), before);
        clean(&s);
    }
}

#[test]
fn final_fence_observes_original_cancellation_after_scratch_retirement() {
    let (mut s, conflict, _) = fixture(2, Reasons::Long);
    let before = state(&s);
    let cancel = Arc::new(AtomicBool::new(false));
    let observer = Arc::clone(&cancel);
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(10_000_000, 10_000_000),
        None,
        Arc::new(move || observer.load(Ordering::SeqCst)),
    )
    .unwrap();
    attach(&mut s, &owner);
    let scope = s.begin_counted_ic3_resolution(conflict).unwrap().unwrap();
    cancel.store(true, Ordering::SeqCst);
    assert_eq!(scope.finish(), Err(SatUnknownReason::Interrupted));
    cancel.store(false, Ordering::SeqCst);
    assert_eq!(run(&mut s, conflict), Err(SatUnknownReason::Interrupted));
    assert_eq!(state(&s), before);
    clean(&s);
}

#[test]
fn counted_entry_does_not_discard_preexisting_ordinary_analysis_scratch() {
    let (mut s, conflict, _) = fixture(2, Reasons::Long);
    assert!(ordinary(&mut s, conflict).is_some());
    let before = format!("{:?}", s.conflict);
    let data = s.var_data.clone();
    attach(&mut s, &test_owner(10_000_000, 10_000_000));
    assert_eq!(run(&mut s, conflict), Err(SatUnknownReason::ResourceBudget));
    assert_eq!(format!("{:?}", s.conflict), before);
    assert_eq!(s.var_data, data);
}

#[test]
fn proof_state_and_unsupported_ic3_config_are_refused_without_changing_defaults() {
    for mutate in [
        (|s: &mut Solver| s.cold.ic3_mode = false) as fn(&mut Solver),
        |s| s.chrono_enabled = true,
        |s| s.ghost_guard_needed = true,
        |s| s.cold.lrat_enabled = true,
        |s| s.cold.internal_lrat_enabled = true,
        |s| s.cold.proof_bookkeeping_budget = Some(100),
        |s| s.cold.lazy_materialization_failed = true,
    ] {
        let (mut s, conflict, _) = fixture(2, Reasons::Long);
        mutate(&mut s);
        let before = state(&s);
        attach(&mut s, &test_owner(10_000_000, 10_000_000));
        assert_eq!(run(&mut s, conflict), Err(SatUnknownReason::ResourceBudget));
        assert_eq!(state(&s), before);
    }
}

#[test]
fn stale_trail_and_nonfalse_reason_literals_are_refused_before_publication() {
    for mutate in [
        (|s: &mut Solver| {
            s.var_data[0].trail_pos = u32::MAX;
        }) as fn(&mut Solver),
        |s| {
            let last = s.trail.last().unwrap().variable().index();
            s.var_data[last].trail_pos = 0;
        },
        |s| {
            s.vals[neg(0).index()] = 1;
        },
        |s| {
            s.var_data[0].level = s.decision_level + 1;
        },
    ] {
        let (mut s, conflict, _) = fixture(2, Reasons::Long);
        mutate(&mut s);
        let before = state(&s);
        attach(&mut s, &test_owner(10_000_000, 10_000_000));
        assert_eq!(run(&mut s, conflict), Err(SatUnknownReason::ResourceBudget));
        assert_eq!(state(&s), before);
        clean(&s);
    }
}
