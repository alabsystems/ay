// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn stale_unowned_block_workspaces_are_rejected_without_erasing_them() {
    for mutate in [
        (|s: &mut Solver| s.ws_shrink_entries.push((1, 1, 1))) as fn(&mut Solver),
        |s| s.ws_shrink_result.push(neg(1)),
        |s| s.ws_shrink_block_lits.push(neg(1)),
        |s| s.ws_shrink_chain.push(7),
        |s| s.min.shrink_walked.push(1),
        |s| s.reap.push(9),
    ] {
        let (mut s, conflict, _) = selected(3, Reasons::Long);
        mutate(&mut s);
        let entries = s.ws_shrink_entries.clone();
        let result = s.ws_shrink_result.clone();
        let block = s.ws_shrink_block_lits.clone();
        let chain = s.ws_shrink_chain.clone();
        let walked = s.min.shrink_walked.clone();
        let queue_empty = s.reap.is_empty();
        attach(&mut s, &test_owner(10_000_000, 10_000_000));
        assert_eq!(
            minimize(&mut s, conflict),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(s.ws_shrink_entries, entries);
        assert_eq!(s.ws_shrink_result, result);
        assert_eq!(s.ws_shrink_block_lits, block);
        assert_eq!(s.ws_shrink_chain, chain);
        assert_eq!(s.min.shrink_walked, walked);
        assert_eq!(s.reap.is_empty(), queue_empty);
        retired(&mut s);
    }
}

#[test]
fn block_shrink_exact_original_work_storage_and_one_short_controls() {
    let (mut baseline, conflict, _) = selected(3, Reasons::Long);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut baseline, &owner);
    let expected = minimize(&mut baseline, conflict).unwrap();
    let used = owner.usage().unwrap();
    assert!(baseline.stats.shrink_block_successes > 0);
    for (work, storage, refusal) in [
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
        let (mut s, conflict, _) = selected(3, Reasons::Long);
        let before = state(&s);
        let owner = test_owner(work, storage);
        attach(&mut s, &owner);
        let result = minimize(&mut s, conflict);
        if let Some(refusal) = refusal {
            assert_eq!(result, Err(SatUnknownReason::ResourceBudget));
            assert_eq!(owner.check(), Err(refusal));
            let receipt = owner.usage().unwrap();
            assert_eq!(minimize(&mut s, conflict), result);
            assert_eq!(owner.usage().unwrap(), receipt);
        } else {
            assert_eq!(result, Ok(expected.clone()));
        }
        assert_eq!(state(&s), before);
        fully_retired(&mut s);
    }
}

#[test]
fn every_repeated_block_work_cut_retires_taken_buffers_flags_and_radix_queue() {
    let (mut baseline, conflict, _) = selected(3, Reasons::Long);
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
        let (mut s, conflict, _) = selected(3, Reasons::Long);
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
        fully_retired(&mut s);
    }
}

#[test]
fn every_repeated_block_observer_cut_is_original_sticky_and_has_no_result() {
    let (mut baseline, conflict, _) = selected(3, Reasons::Long);
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
        let (mut s, conflict, _) = selected(3, Reasons::Long);
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
        fully_retired(&mut s);
    }
}

#[test]
fn malformed_block_only_reason_refuses_instead_of_using_ordinary_fallback() {
    for mode in 0..3 {
        let (mut s, conflict, _) = selected(3, Reasons::Long);
        let offset = s.var_reason(4).unwrap().0 as usize;
        let index = s
            .arena
            .literals(offset)
            .iter()
            .position(|lit| *lit == pos(4))
            .unwrap();
        let other = s
            .arena
            .literals(offset)
            .iter()
            .position(|lit| *lit == neg(3))
            .unwrap();
        match mode {
            0 => s.arena.set_literal(offset, index, neg(4)),
            1 => s.arena.set_literal(offset, other, neg(4)),
            _ => s.arena.set_literal(offset, other, neg(5)),
        }
        let before = state(&s);
        let owner = test_owner(10_000_000, 10_000_000);
        attach(&mut s, &owner);
        let scope = s.begin_counted_ic3_resolution(conflict).unwrap().unwrap();
        assert!(matches!(
            scope.minimize_selected(),
            Err(SatUnknownReason::ResourceBudget)
        ));
        assert!(owner.usage().unwrap().refusal.is_some());
        assert_eq!(state(&s), before);
        fully_retired(&mut s);
    }
}

#[test]
fn actual_block_tick_overflow_refuses_without_wrapping_or_renewing_owner() {
    let (mut s, conflict, _) = selected(3, Reasons::Long);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    let scope = s.begin_counted_ic3_resolution(conflict).unwrap().unwrap();
    let mode = usize::from(scope.retirement.solver.stable_mode);
    scope.retirement.solver.search_ticks[mode] = u64::MAX;
    assert!(matches!(
        scope.minimize_selected(),
        Err(SatUnknownReason::ResourceBudget)
    ));
    assert_eq!(s.search_ticks[mode], u64::MAX);
    let receipt = owner.usage().unwrap();
    assert_eq!(
        minimize(&mut s, conflict),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(owner.usage().unwrap(), receipt);
    fully_retired(&mut s);
}
