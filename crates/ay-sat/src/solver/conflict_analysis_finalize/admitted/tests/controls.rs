// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn traced_removal_augmentation_refuses_before_snapshot_without_disabling_defaults() {
    let (mut s, reference, _) = fixture_tracking(true, BranchHeuristic::Evsids, Tracking::Traced);
    assert!(s.cold.lrat_enabled && s.shrink_enabled);
    let trace = format!("{:?}", s.clause_trace());
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    assert_eq!(
        run(&mut s, reference),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert!(format!("{:?}", owner.usage().unwrap().refusal).contains("LRAT removal augmentation"));
    assert_eq!(s.stats.lrat_original_learned_snapshot_copies, 0);
    assert_eq!(s.min.lrat_original_learned_buf.len(), 0);
    assert!(s.cold.lrat_enabled && s.shrink_enabled);
    assert_eq!(format!("{:?}", s.clause_trace()), trace);
    clean(&mut s);
}

#[test]
fn every_work_cut_in_default_block_finalization_retires_all_owned_scratch() {
    let (mut baseline, reference, _) = fixture(true, BranchHeuristic::Vmtf);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut baseline, &owner);
    assert!(run(&mut baseline, reference).is_ok());
    let total = owner.usage().unwrap().work_admitted;
    assert!(baseline.stats.shrink_block_successes > 0);
    for work in 0..total {
        let (mut s, reference, _) = fixture(true, BranchHeuristic::Vmtf);
        let owner = test_owner(work, 10_000_000);
        attach(&mut s, &owner);
        assert_eq!(
            run(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget),
            "cut {work}"
        );
        assert_eq!(
            owner.clone().check(),
            Err(CountedAdmissionError::WorkExhausted)
        );
        let used = owner.usage().unwrap();
        assert_eq!(
            run(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(owner.usage().unwrap(), used);
        clean(&mut s);
    }
}

#[test]
fn exact_and_one_short_storage_include_real_result_and_activity_allocation() {
    let (mut baseline, reference, _) = fixture(true, BranchHeuristic::Chb);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut baseline, &owner);
    let expected = run(&mut baseline, reference).unwrap();
    let used = owner.usage().unwrap();
    assert!(used.storage_admitted > 0);
    for bytes in [used.storage_admitted - 1, used.storage_admitted] {
        let (mut s, reference, _) = fixture(true, BranchHeuristic::Chb);
        let owner = test_owner(used.work_admitted, bytes);
        attach(&mut s, &owner);
        let result = run(&mut s, reference);
        if bytes == used.storage_admitted {
            assert_eq!(result.unwrap(), expected);
            assert_eq!(owner.usage().unwrap().storage_remaining, 0);
        } else {
            assert_eq!(result, Err(SatUnknownReason::ResourceBudget));
            assert_eq!(owner.check(), Err(CountedAdmissionError::StorageExhausted));
        }
        clean(&mut s);
    }
}

#[test]
fn every_observer_cut_during_block_minimize_activity_result_and_finish_is_terminal() {
    let calls = Arc::new(AtomicUsize::new(0));
    let observing = |stop, calls: &Arc<AtomicUsize>| {
        let calls = Arc::clone(calls);
        CountedAdmission::new(
            FiniteAdmissionGrant::new(10_000_000, 10_000_000),
            None,
            Arc::new(move || calls.fetch_add(1, Ordering::SeqCst) == stop),
        )
        .unwrap()
    };
    let (mut baseline, reference, _) = fixture(true, BranchHeuristic::Evsids);
    attach(&mut baseline, &observing(usize::MAX, &calls));
    run(&mut baseline, reference).unwrap();
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 30);
    for cut in 0..total {
        let (mut s, reference, _) = fixture(true, BranchHeuristic::Evsids);
        let calls = Arc::new(AtomicUsize::new(0));
        let owner = observing(cut, &calls);
        attach(&mut s, &owner);
        assert_eq!(
            run(&mut s, reference),
            Err(SatUnknownReason::Interrupted),
            "poll {cut}"
        );
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        clean(&mut s);
        assert!(owner.check().is_err());
    }
}

#[test]
fn dirty_preexisting_minimizer_state_is_not_claimed_or_cleared() {
    let (mut s, reference, _) = fixture(true, BranchHeuristic::Evsids);
    s.min.minimize_to_clear.push(0);
    s.min.minimize_flags[0] = MIN_VISITED;
    attach(&mut s, &test_owner(10_000_000, 10_000_000));
    assert_eq!(
        run(&mut s, reference),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(s.min.minimize_to_clear, vec![0]);
    assert_eq!(s.min.minimize_flags[0], MIN_VISITED);
}

#[test]
fn active_hint_work_is_refused_before_finalization_effects() {
    let (mut s, _, _) = fixture(true, BranchHeuristic::Evsids);
    s.mark_veripb_hints_active_for_test();
    let owner = test_owner(10_000_000, 10_000_000);
    let before = format!("{:?}", s.vsids);
    assert!(s
        .finalize_conflict_analysis_admitted(neg(4), Vec::new(), &Counted(&owner))
        .is_err());
    assert_eq!(format!("{:?}", s.vsids), before);
    assert_eq!(s.conflict.learned_count(), 0);
    assert!(owner.check().is_err());
}

#[test]
fn stable_level_sort_scales_to_wide_joins_with_exact_ties_and_logarithmic_passes() {
    let len = 8192usize;
    let data: Vec<_> = (0..len)
        .map(|i| VarData {
            level: ((i * 31) % 17) as u32,
            ..VarData::UNASSIGNED
        })
        .collect();
    let mut actual: Vec<_> = (0..len as u32).rev().map(pos).collect();
    let mut expected = actual.clone();
    expected.sort_by_key(|lit| std::cmp::Reverse(data[lit.variable().index()].level));
    let owner = test_owner(10_000_000, 10_000_000);
    sort::stable_by_level(&mut actual, &data, &owner).unwrap();
    assert_eq!(actual, expected);
    assert!(owner.usage().unwrap().work_admitted < (len * 64) as u64);
}
