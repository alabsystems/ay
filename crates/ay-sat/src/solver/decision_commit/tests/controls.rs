// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn observing_owner(stop_at: usize, calls: &Arc<AtomicUsize>) -> CountedAdmission {
    let observed = Arc::clone(calls);
    CountedAdmission::new(
        FiniteAdmissionGrant::new(10_000_000, 10_000_000),
        None,
        Arc::new(move || observed.fetch_add(1, Ordering::SeqCst) == stop_at),
    )
    .unwrap()
}

#[test]
fn every_observer_cut_is_before_mutation_or_after_complete_assignment() {
    let calls = Arc::new(AtomicUsize::new(0));
    let mut baseline = fixture();
    attach(&mut baseline, &observing_owner(usize::MAX, &calls));
    assert_eq!(baseline.decide_counted(lit(3)), Ok(()));
    let total = calls.load(Ordering::SeqCst);
    for stop_at in 0..total {
        let mut s = fixture();
        let before = state(&s);
        let calls = Arc::new(AtomicUsize::new(0));
        attach(&mut s, &observing_owner(stop_at, &calls));
        assert_eq!(s.decide_counted(lit(3)), Err(SatUnknownReason::Interrupted));
        let after = state(&s);
        assert_eq!(
            after,
            if stop_at + 1 == total {
                state(&baseline)
            } else {
                before
            }
        );
        assert_eq!(s.decide_counted(lit(3)), Err(SatUnknownReason::Interrupted));
        assert_eq!(state(&s), after);
    }
}

#[test]
fn exact_and_short_grants_cover_real_trail_and_limit_growth() {
    let mut baseline = fixture();
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut baseline, &owner);
    assert_eq!(baseline.decide_counted(lit(3)), Ok(()));
    let used = owner.usage().unwrap();
    assert!(used.storage_admitted > 0);
    for (work, storage, admitted) in [
        (used.work_admitted, used.storage_admitted, true),
        (used.work_admitted - 1, used.storage_admitted, false),
        (used.work_admitted, used.storage_admitted - 1, false),
        (0, 0, false),
    ] {
        let mut s = fixture();
        let before = state(&s);
        let owner = test_owner(work, storage);
        attach(&mut s, &owner);
        let result = s.decide_counted(lit(3));
        if admitted {
            assert_eq!(result, Ok(()));
            assert_eq!(state(&s), state(&baseline));
            assert_eq!(owner.usage().unwrap().work_remaining, 0);
            assert_eq!(owner.usage().unwrap().storage_remaining, 0);
        } else {
            assert_eq!(result, Err(SatUnknownReason::ResourceBudget));
            assert_eq!(state(&s), before);
            assert_eq!(s.decide_counted(lit(3)), result);
            assert_eq!(state(&s), before);
        }
    }
}

#[test]
fn invalid_assignment_or_overflow_never_partially_commits_decision_metadata() {
    for case in 0..6 {
        let mut s = fixture();
        let selected = match case {
            0 => lit(0),
            1 => lit(99),
            2 => {
                s.var_lifecycle.mark_eliminated(3);
                lit(3)
            }
            3 => {
                s.qhead = 0;
                lit(3)
            }
            4 => {
                s.decision_level = u32::MAX;
                lit(3)
            }
            _ => {
                s.stats.decision_level_sum = u64::MAX;
                lit(3)
            }
        };
        let before = state(&s);
        let owner = test_owner(10_000, 10_000);
        attach(&mut s, &owner);
        assert_eq!(
            s.decide_counted(selected),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(state(&s), before);
        assert!(matches!(
            owner.check(),
            Err(CountedAdmissionError::Original(_))
        ));
    }
}

#[cfg(debug_assertions)]
#[test]
fn every_1024th_enqueue_pays_the_actual_whole_variable_debug_scan() {
    let make = || {
        let mut s = Solver::new(1024);
        s.trail.reserve(1024);
        s.trail_lim.reserve(1);
        for index in 0..1023 {
            s.enqueue(lit(index), None);
        }
        assert!(s.search_propagate().is_none());
        s
    };
    let mut refused = make();
    let before = state(&refused);
    attach(&mut refused, &test_owner(1026, 0));
    assert_eq!(
        refused.decide_counted(lit(1023)),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(state(&refused), before);
    let mut admitted = make();
    let owner = test_owner(1027, 0);
    attach(&mut admitted, &owner);
    assert_eq!(admitted.decide_counted(lit(1023)), Ok(()));
    assert_eq!(owner.usage().unwrap().work_remaining, 0);
    assert_eq!(admitted.trail.len(), 1024);
}
