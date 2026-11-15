// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn refused_ic3_entry_does_not_run_an_unmetered_cleanup_backtrack() {
    let mut s = fixture(false, true);
    let before = state(&s);
    attach(&mut s, &test_owner(0, 0));
    assert!(matches!(
        s.solve_incremental_ic3(&[]).into_inner(),
        AssumeResult::Unknown
    ));
    assert_eq!(state(&s), before);
    assert_eq!(
        s.last_unknown_reason(),
        Some(SatUnknownReason::ResourceBudget)
    );
}

#[test]
fn exact_and_short_work_storage_leave_refused_transactions_unchanged() {
    for ic3 in [false, true] {
        let make = || {
            if ic3 {
                fixture(false, true)
            } else {
                lambda_fixture()
            }
        };
        let mut baseline = make();
        let original = test_owner(10_000_000, 10_000_000);
        attach(&mut baseline, &original);
        assert_eq!(run(&mut baseline, 1, ic3), Ok(()));
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
            let mut s = make();
            let before = state(&s);
            let owner = test_owner(work, storage);
            attach(&mut s, &owner);
            let result = run(&mut s, 1, ic3);
            if let Some(error) = error {
                assert_eq!(result, Err(SatUnknownReason::ResourceBudget));
                assert_eq!(state(&s), before);
                assert_eq!(owner.check(), Err(error));
                assert_eq!(run(&mut s, 1, ic3), result);
                assert_eq!(state(&s), before);
            } else {
                assert_eq!(result, Ok(()));
                assert_eq!(state(&s), state(&baseline));
                assert_eq!(owner.usage().unwrap().work_remaining, 0);
                assert_eq!(owner.usage().unwrap().storage_remaining, 0);
            }
        }
    }
}

fn observing_owner(stop_at: usize, calls: &Arc<AtomicUsize>) -> CountedAdmission {
    let observed = Arc::clone(calls);
    CountedAdmission::new(
        FiniteAdmissionGrant::new(10_000_000, 10_000_000),
        None,
        Arc::new(move || observed.fetch_add(1, Ordering::SeqCst) == stop_at),
    )
    .unwrap()
}

#[test]
fn every_observer_refusal_is_before_mutation_or_after_complete_commit() {
    for ic3 in [false, true] {
        let make = || {
            if ic3 {
                fixture(false, true)
            } else {
                lambda_fixture()
            }
        };
        let calls = Arc::new(AtomicUsize::new(0));
        let mut baseline = make();
        attach(&mut baseline, &observing_owner(usize::MAX, &calls));
        assert_eq!(run(&mut baseline, 1, ic3), Ok(()));
        let total = calls.load(Ordering::SeqCst);
        assert!(total > 2);
        for stop_at in 0..total {
            let mut s = make();
            let before = state(&s);
            let calls = Arc::new(AtomicUsize::new(0));
            let owner = observing_owner(stop_at, &calls);
            attach(&mut s, &owner);
            assert_eq!(run(&mut s, 1, ic3), Err(SatUnknownReason::Interrupted));
            let after = state(&s);
            if stop_at + 1 == total {
                // Final post-scratch-cleanup fence: compaction is complete.
                assert_eq!(after, state(&baseline));
            } else {
                assert_eq!(after, before);
            }
            assert_eq!(run(&mut s, 1, ic3), Err(SatUnknownReason::Interrupted));
            assert_eq!(state(&s), after);
        }
    }
}

#[test]
fn no_op_still_prepays_target_and_best_phase_copies() {
    let mut expected = fixture(false, false);
    expected.cold.target_kissat = false;
    expected.cold.best_stable_kissat = false;
    let mut actual = fixture(false, false);
    actual.cold.target_kissat = false;
    actual.cold.best_stable_kissat = false;
    expected.backtrack(expected.decision_level);
    let owner = test_owner(1 + 2 * actual.num_vars as u64, 0);
    attach(&mut actual, &owner);
    assert_eq!(actual.backtrack_counted(actual.decision_level), Ok(()));
    assert_eq!(state(&actual), state(&expected));
    assert_eq!(owner.usage().unwrap().work_remaining, 0);
}

#[test]
fn stale_frontier_epoch_is_invalidated_only_after_admission() {
    let make = || {
        let mut s = fixture(true, false);
        let offset = s.arena.indices().next().unwrap();
        s.arena.delete(offset);
        s
    };
    let mut expected = make();
    expected.backtrack(0);
    let mut actual = make();
    let before = state(&actual);
    attach(&mut actual, &test_owner(0, 0));
    assert_eq!(
        actual.backtrack_counted(0),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(state(&actual), before);
    let mut admitted = make();
    attach(&mut admitted, &test_owner(10_000_000, 10_000_000));
    assert_eq!(admitted.backtrack_counted(0), Ok(()));
    assert_eq!(state(&admitted), state(&expected));
}
