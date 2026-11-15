// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_and_short_original_work_and_storage_include_real_recursive_minimization() {
    let (mut baseline, conflict, _) = removable(4, Reasons::Long);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut baseline, &owner);
    let expected = minimize(&mut baseline, conflict).unwrap();
    let used = owner.usage().unwrap();
    for (work, storage, refused) in [
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
        let (mut s, conflict, _) = removable(4, Reasons::Long);
        let before = state(&s);
        let owner = test_owner(work, storage);
        attach(&mut s, &owner);
        let result = minimize(&mut s, conflict);
        if let Some(refused) = refused {
            assert_eq!(result, Err(SatUnknownReason::ResourceBudget));
            assert_eq!(owner.check(), Err(refused));
            let receipt = owner.usage().unwrap();
            assert_eq!(minimize(&mut s, conflict), result);
            assert_eq!(owner.usage().unwrap(), receipt);
        } else {
            assert_eq!(result, Ok(expected.clone()));
        }
        assert_eq!(state(&s), before);
        retired(&mut s);
    }
}

#[test]
fn every_minimization_work_cut_retires_recursion_flags_and_level_scratch() {
    let (mut baseline, conflict, _) = removable(3, Reasons::Long);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut baseline, &owner);
    let scope = baseline
        .begin_counted_ic3_resolution(conflict)
        .unwrap()
        .unwrap();
    let prefix = owner.usage().unwrap().work_admitted;
    scope.minimize_selected().unwrap().finish().unwrap();
    let total = owner.usage().unwrap().work_admitted;
    assert!(total > prefix);
    for work in prefix..total {
        let (mut s, conflict, _) = removable(3, Reasons::Long);
        let before = state(&s);
        let owner = test_owner(work, 10_000_000);
        attach(&mut s, &owner);
        assert_eq!(
            minimize(&mut s, conflict),
            Err(SatUnknownReason::ResourceBudget),
            "work {work}"
        );
        assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
        assert_eq!(state(&s), before);
        retired(&mut s);
    }
}

#[test]
fn every_minimization_observer_cut_including_result_and_retirement_fences_is_sticky() {
    let (mut baseline, conflict, _) = removable(3, Reasons::Long);
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut baseline, &observing_owner(usize::MAX, &calls));
    let scope = baseline
        .begin_counted_ic3_resolution(conflict)
        .unwrap()
        .unwrap();
    let prefix = calls.load(Ordering::SeqCst);
    scope.minimize_selected().unwrap().finish().unwrap();
    let total = calls.load(Ordering::SeqCst);
    for at in prefix..total {
        let (mut s, conflict, _) = removable(3, Reasons::Long);
        let before = state(&s);
        let calls = Arc::new(AtomicUsize::new(0));
        let owner = observing_owner(at, &calls);
        attach(&mut s, &owner);
        assert_eq!(
            minimize(&mut s, conflict),
            Err(SatUnknownReason::Interrupted),
            "observer {at}"
        );
        assert_eq!(
            minimize(&mut s, conflict),
            Err(SatUnknownReason::Interrupted)
        );
        assert_eq!(calls.load(Ordering::SeqCst), at + 1);
        assert_eq!(state(&s), before);
        retired(&mut s);
    }
}

#[test]
fn stale_unowned_minimization_scratch_is_not_silently_erased() {
    for mutate in [
        (|s: &mut Solver| s.min.minimize_flags[0] = MIN_KEEP) as fn(&mut Solver),
        |s| s.min.minimize_to_clear.push(0),
        |s| s.min.minimize_level_seen[0].count = 1,
        |s| s.min.minimize_levels_to_clear.push(0),
        |s| s.conflict.clause_buf_mut().push(neg(0)),
    ] {
        let (mut s, conflict, _) = removable(3, Reasons::Long);
        mutate(&mut s);
        let flags = s.min.minimize_flags.clone();
        let dirty = s.min.minimize_to_clear.clone();
        let levels = s.min.minimize_level_seen.clone();
        let level_dirty = s.min.minimize_levels_to_clear.clone();
        let buf = s.conflict.clause_buf_mut().clone();
        attach(&mut s, &test_owner(10_000_000, 10_000_000));
        assert_eq!(
            minimize(&mut s, conflict),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(s.min.minimize_flags, flags);
        assert_eq!(s.min.minimize_to_clear, dirty);
        assert_eq!(s.min.minimize_level_seen, levels);
        assert_eq!(s.min.minimize_levels_to_clear, level_dirty);
        assert_eq!(*s.conflict.clause_buf_mut(), buf);
        clean(&s);
    }
}

#[test]
fn invalid_minimization_only_reason_cannot_become_a_removed_literal() {
    for mode in 0..3 {
        let (mut s, conflict, _) = removable(3, Reasons::Long);
        let offset = s.var_reason(4).unwrap().0 as usize;
        let pivot = s
            .arena
            .literals(offset)
            .iter()
            .position(|lit| *lit == pos(4))
            .unwrap();
        let antecedent = s
            .arena
            .literals(offset)
            .iter()
            .position(|lit| *lit == neg(3))
            .unwrap();
        match mode {
            0 => s.arena.set_literal(offset, pivot, neg(4)),
            1 => s.arena.set_literal(offset, antecedent, neg(4)),
            _ => s.arena.set_literal(offset, antecedent, neg(5)),
        }
        let before = state(&s);
        let owner = test_owner(10_000_000, 10_000_000);
        attach(&mut s, &owner);
        // Resolution does not traverse this lower-level reason; refusal must
        // come from the actual subsequent minimization operation.
        let scope = s.begin_counted_ic3_resolution(conflict).unwrap().unwrap();
        assert!(matches!(
            scope.minimize_selected(),
            Err(SatUnknownReason::ResourceBudget)
        ));
        assert!(owner.usage().unwrap().refusal.is_some());
        assert_eq!(state(&s), before);
        retired(&mut s);
    }
}

#[test]
fn actual_tick_overflow_refuses_before_mutation_and_no_retry_renews_credit() {
    let (mut s, conflict, _) = removable(3, Reasons::Long);
    let mode = usize::from(s.stable_mode);
    s.search_ticks[mode] = u64::MAX;
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    assert_eq!(
        minimize(&mut s, conflict),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(s.search_ticks[mode], u64::MAX);
    let receipt = owner.usage().unwrap();
    assert_eq!(
        minimize(&mut s, conflict),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(owner.usage().unwrap(), receipt);
    retired(&mut s);
}
