// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_and_short_work_storage_refuse_before_selection() {
    for make in [domain_fixture as fn() -> Solver, frontier_fixture] {
        let mut baseline = make();
        let generous = test_owner(10_000_000, 10_000_000);
        attach(&mut baseline, &generous);
        let expected = baseline.pick_next_decision_literal_counted();
        assert!(expected.is_ok());
        let used = generous.usage().unwrap();
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
            let result = s.pick_next_decision_literal_counted();
            if let Some(error) = error {
                assert_eq!(result, Err(SatUnknownReason::ResourceBudget));
                assert_eq!(state(&s), before);
                assert_eq!(owner.check(), Err(error));
                assert_eq!(s.pick_next_decision_literal_counted(), result);
                assert_eq!(state(&s), before);
            } else {
                assert_eq!(result, expected);
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
fn every_stop_cut_restores_domains_frontier_and_scratch_before_refusal() {
    for make in [domain_fixture as fn() -> Solver, frontier_fixture] {
        let mut baseline = make();
        let calls = Arc::new(AtomicUsize::new(0));
        attach(&mut baseline, &observing_owner(usize::MAX, &calls));
        assert!(baseline.pick_next_decision_literal_counted().is_ok());
        let total = calls.load(Ordering::SeqCst);
        assert!(total > 2);
        for stop_at in 0..total {
            let mut s = make();
            let before = state(&s);
            let calls = Arc::new(AtomicUsize::new(0));
            attach(&mut s, &observing_owner(stop_at, &calls));
            assert_eq!(
                s.pick_next_decision_literal_counted(),
                Err(SatUnknownReason::Interrupted)
            );
            let after = state(&s);
            if stop_at + 1 == total {
                // Only the post-scratch fence can observe a complete selection.
                assert_eq!(after, state(&baseline));
            } else {
                assert_eq!(after, before);
            }
            assert_eq!(
                s.pick_next_decision_literal_counted(),
                Err(SatUnknownReason::Interrupted)
            );
            assert_eq!(state(&s), after);
        }
    }
}

#[test]
fn exhausted_owner_is_never_the_empty_candidate_model_signal() {
    for domain in [false, true] {
        let make = || {
            let mut s = Solver::new(4);
            if domain {
                s.active_domain = Some(vec![false; 4]);
            } else {
                s.set_relevancy_branching(true);
                s.set_relevancy_hard(true);
            }
            s
        };
        let mut ordinary_solver = make();
        assert_eq!(ordinary(&mut ordinary_solver), None);
        let mut admitted = make();
        attach(&mut admitted, &test_owner(10_000_000, 10_000_000));
        assert_eq!(admitted.pick_next_decision_literal_counted(), Ok(None));
        assert_eq!(state(&admitted), state(&ordinary_solver));
        let mut refused = make();
        let before = state(&refused);
        attach(&mut refused, &test_owner(0, 0));
        assert_eq!(
            refused.pick_next_decision_literal_counted(),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(state(&refused), before);
    }
}
