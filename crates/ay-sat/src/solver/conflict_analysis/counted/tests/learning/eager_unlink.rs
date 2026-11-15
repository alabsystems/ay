// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn watched(s: &Solver, reference: ClauseRef) -> usize {
    [neg(1), neg(0)]
        .into_iter()
        .map(|lit| {
            let list = s.watches.get_watches(lit);
            (0..list.len())
                .filter(|&i| list.clause_ref(i) == reference)
                .count()
        })
        .sum()
}

fn fixture() -> (Solver, ClauseRef, ClauseRef) {
    let (mut s, conflict, _) = fork(1, 0);
    // The real fork entails this binary. Add an older duplicate so the
    // normal learned binary selects actual eager removal from both lists.
    let older = s.add_learned_clause(vec![neg(1), neg(0)], 2, &[1, 2, 3]);
    assert_eq!(watched(&s, older), 2, "both old watches must really exist");
    assert!(!s.arena.is_garbage(older.index()));
    (s, conflict, older)
}

fn failed(s: &Solver, older: ClauseRef, before: &[(u64, Vec<Literal>, bool, Vec<u64>)]) {
    clean(s);
    for var in 0..s.num_vars {
        assert_eq!(s.lit_marks.get(Variable(var as u32)), 0);
    }
    let rows = trace_rows(s);
    assert!(
        rows.starts_with(before),
        "retained row/ID/hint prefix changed"
    );
    if rows.len() > before.len() {
        assert!(s.clause_trace().unwrap().proof_work_exhausted());
    }
    // No observer can interrupt between the two actual removals. A stopped
    // transition retains either the original pair or neither, never one side.
    let removed = s.arena.is_garbage(older.index());
    assert_eq!(watched(s, older), if removed { 0 } else { 2 });
    assert_eq!(
        s.cold.num_eager_subsumed_duplicate_binaries,
        u64::from(removed)
    );
    assert_eq!(s.cold.diagnostic_pass, DiagnosticPass::None);
}

#[test]
fn selected_duplicate_binary_unlink_matches_ordinary_and_false_keeps_both_watches() {
    for unlink in [false, true] {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            eager_subsume_unlink_binaries: Some(unlink),
            ..Default::default()
        });
        let (mut expected, reference, expected_older) = fixture();
        expected.analyze_and_backtrack(reference, "selected eager unlink", |_, _| {});
        let (mut s, reference, older) = fixture();
        let owner = test_owner(100_000_000, 100_000_000);
        attach(&mut s, &owner);
        let step = learn(&mut s, reference).unwrap();
        assert_eq!(s.arena.len_of(step.reference.index()), 2);
        assert_eq!(watched(&s, step.reference), 2, "new binary stays watched");
        assert!(s.arena.is_garbage(older.index()));
        assert!(expected.arena.is_garbage(expected_older.index()));
        assert_eq!(watched(&s, older), if unlink { 0 } else { 2 });
        assert_eq!(s.cold.num_eager_subsumed_duplicate_binaries, 1);
        parity(&s, &expected);
        assert!(owner.usage().unwrap().refusal.is_none());
        clean(&s);
    }
}

#[test]
fn every_selected_unlink_observer_cut_is_sticky_and_never_leaves_one_old_watch() {
    let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        eager_subsume_unlink_binaries: Some(true),
        ..Default::default()
    });
    let (mut baseline, reference, older) = fixture();
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut baseline, &observing_owner(usize::MAX, &calls));
    learn(&mut baseline, reference).unwrap();
    assert_eq!(watched(&baseline, older), 0);
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 30);
    let mut before_unlink = 0;
    let mut after_unlink = 0;
    for cut in 0..total {
        let (mut s, reference, older) = fixture();
        let before = trace_rows(&s);
        let calls = Arc::new(AtomicUsize::new(0));
        let owner = observing_owner(cut, &calls);
        attach(&mut s, &owner);
        assert_eq!(learn(&mut s, reference), Err(SatUnknownReason::Interrupted));
        let frozen = owner.usage().unwrap();
        assert_eq!(learn(&mut s, reference), Err(SatUnknownReason::Interrupted));
        assert_eq!(owner.usage().unwrap(), frozen);
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        failed(&s, older, &before);
        if s.arena.is_garbage(older.index()) {
            after_unlink += 1;
        } else {
            before_unlink += 1;
        }
    }
    assert!(
        before_unlink > 0 && after_unlink > 0,
        "both sides must be reached"
    );
}

#[test]
fn selected_unlink_exact_grants_succeed_and_each_one_short_grant_refuses() {
    let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        eager_subsume_unlink_binaries: Some(true),
        ..Default::default()
    });
    let (mut baseline, reference, older) = fixture();
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut baseline, &owner);
    learn(&mut baseline, reference).unwrap();
    assert_eq!(watched(&baseline, older), 0);
    let used = owner.usage().unwrap();
    assert!(used.work_admitted > 0 && used.storage_admitted > 0);
    let (mut exact, reference, older) = fixture();
    let owner = test_owner(used.work_admitted, used.storage_admitted);
    attach(&mut exact, &owner);
    learn(&mut exact, reference).unwrap();
    assert_eq!(watched(&exact, older), 0);
    assert_eq!(owner.usage().unwrap().work_remaining, 0);
    assert_eq!(owner.usage().unwrap().storage_remaining, 0);
    parity(&exact, &baseline);
    for (work, storage, reason) in [
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
        let (mut s, reference, older) = fixture();
        let before = trace_rows(&s);
        let owner = test_owner(work, storage);
        attach(&mut s, &owner);
        assert_eq!(
            learn(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(owner.check(), Err(reason));
        let frozen = owner.usage().unwrap();
        assert_eq!(
            learn(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(owner.usage().unwrap(), frozen);
        failed(&s, older, &before);
    }
}
