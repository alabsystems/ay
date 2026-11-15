// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn baseline() -> ay_core::original_query::AdmissionUsage {
    let (mut s, reference, _) = fork(0, 0);
    let owner = generous();
    attach(&mut s, &owner);
    assert!(matches!(
        s.dispatch_conflict_counted(reference),
        Ok(CountedDispatchStep::Learned { .. })
    ));
    let used = owner.usage().unwrap();
    assert!(used.work_admitted > 100 && used.storage_admitted > 0);
    used
}

fn failed(s: &Solver, before: &[(u64, Vec<Literal>, bool, Vec<u64>)]) {
    clean(s);
    assert!(rows(s).starts_with(before));
    assert!(s.clause_trace().unwrap().proof_work_exhausted());
    assert!(s.cold.decision_trace.is_none());
    assert!(
        !s.has_empty_clause(),
        "a refusal must not become UNSAT authority"
    );
}

#[test]
fn exact_dispatch_grants_reach_learning_without_renewal() {
    let used = baseline();
    let (mut s, reference, _) = fork(0, 0);
    let owner = test_owner(used.work_admitted, used.storage_admitted);
    attach(&mut s, &owner);
    assert!(matches!(
        s.dispatch_conflict_counted(reference),
        Ok(CountedDispatchStep::Learned { .. })
    ));
    let actual = owner.usage().unwrap();
    assert_eq!(actual.work_remaining, 0);
    assert_eq!(actual.storage_remaining, 0);
    assert_eq!(s.counted_admission_usage().unwrap().unwrap(), actual);
}

#[test]
fn every_short_dispatch_work_and_storage_cut_is_sticky_and_removes_authority() {
    let used = baseline();
    let work_cuts = (0..used.work_admitted).map(|cut| {
        (
            test_owner(cut, 100_000_000),
            CountedAdmissionError::WorkExhausted,
        )
    });
    let storage_cuts = (0..used.storage_admitted).map(|cut| {
        (
            test_owner(100_000_000, cut),
            CountedAdmissionError::StorageExhausted,
        )
    });
    for (owner, expected) in work_cuts.chain(storage_cuts) {
        let (mut s, reference, _) = fork(0, 0);
        let before = rows(&s);
        attach(&mut s, &owner);
        assert_eq!(
            s.dispatch_conflict_counted(reference),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(owner.check(), Err(expected));
        let frozen = owner.usage().unwrap();
        assert_eq!(
            s.dispatch_conflict_counted(reference),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(owner.usage().unwrap(), frozen);
        failed(&s, &before);
    }
}

#[test]
fn every_forced_observer_cut_preserves_first_stop_and_no_partial_proof_authority() {
    for fixture in [global_unit as fn() -> (Solver, ClauseRef), forced] {
        let (mut baseline, reference) = fixture();
        let calls = Arc::new(AtomicUsize::new(0));
        attach(&mut baseline, &observing(usize::MAX, &calls));
        assert_eq!(
            baseline.dispatch_conflict_counted(reference),
            Ok(CountedDispatchStep::Forced)
        );
        let total = calls.load(Ordering::SeqCst);
        assert!(total > 10);
        for cut in 0..total {
            let (mut s, reference) = fixture();
            let before = rows(&s);
            let calls = Arc::new(AtomicUsize::new(0));
            let owner = observing(cut, &calls);
            attach(&mut s, &owner);
            assert_eq!(
                s.dispatch_conflict_counted(reference),
                Err(SatUnknownReason::Interrupted)
            );
            let frozen = owner.usage().unwrap();
            assert_eq!(
                s.dispatch_conflict_counted(reference),
                Err(SatUnknownReason::Interrupted)
            );
            assert_eq!(owner.usage().unwrap(), frozen);
            assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
            failed(&s, &before);
        }
    }
}

#[test]
fn root_conflict_refuses_before_empty_clause_or_terminal_proof_publication() {
    let mut s = configured(2);
    assert!(s.add_clause(vec![neg(0)]));
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    assert!(s.search_propagate().is_none());
    assert_eq!(s.lit_val(neg(0)), 1);
    assert_eq!(s.var_data[0].level, 0);
    assert_ne!(s.unit_proof_id[0], 0);
    s.decide(pos(1));
    assert!(s.search_propagate().is_none());
    let reference = s.add_theory_lemma(vec![pos(0)]).unwrap();
    assert_eq!(s.take_live_pending_theory_conflict(), Some(reference));
    assert_eq!(s.lit_val(pos(0)), -1);
    assert!(!s.has_empty_clause());
    let before = rows(&s);
    let owner = generous();
    attach(&mut s, &owner);
    assert_eq!(
        s.dispatch_conflict_counted(reference),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(
        s.decision_level, 0,
        "real unit dispatch backtracked before discovering root conflict"
    );
    assert_eq!(rows(&s), before);
    assert!(owner.usage().unwrap().refusal.is_some());
    failed(&s, &before);
}

#[test]
fn invalid_reference_and_selected_output_refuse_without_new_authority() {
    for invalid_reference in [true, false] {
        let (mut s, mut reference) = forced();
        if invalid_reference {
            reference = ClauseRef(u32::MAX);
        } else {
            s.cold.trace_ext_conflict = true;
        }
        let before = rows(&s);
        let trail = s.trail.clone();
        let owner = generous();
        attach(&mut s, &owner);
        assert_eq!(
            s.dispatch_conflict_counted(reference),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(s.trail, trail);
        assert_eq!(rows(&s), before);
        assert!(owner.usage().unwrap().refusal.is_some());
        failed(&s, &before);
    }
}
