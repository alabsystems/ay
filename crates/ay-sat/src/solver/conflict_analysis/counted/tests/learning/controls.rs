// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn baseline() -> ay_core::original_query::AdmissionUsage {
    let (mut s, reference, _) = fork(0, 0);
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut s, &owner);
    learn(&mut s, reference).unwrap();
    let used = owner.usage().unwrap();
    assert!(used.work_admitted > 100 && used.storage_admitted > 0);
    used
}

fn failed(s: &Solver, before: &[(u64, Vec<Literal>, bool, Vec<u64>)]) {
    clean(s);
    let rows = trace_rows(s);
    assert!(
        rows.starts_with(before),
        "original row/ID/hint bytes cannot change"
    );
    if rows.len() > before.len() {
        assert!(
            s.clause_trace().unwrap().proof_work_exhausted(),
            "partial derived publication must not retain proof authority"
        );
    }
    assert!(s.cold.decision_trace.is_none());
    assert_eq!(s.cold.diagnostic_pass, DiagnosticPass::None);
}

#[test]
fn exact_learning_grants_cover_real_analysis_backtrack_insert_enqueue_and_retirement() {
    let used = baseline();
    let (mut s, reference, _) = fork(0, 0);
    let owner = test_owner(used.work_admitted, used.storage_admitted);
    attach(&mut s, &owner);
    learn(&mut s, reference).unwrap();
    let actual = owner.usage().unwrap();
    assert_eq!(actual.work_remaining, 0);
    assert_eq!(actual.storage_remaining, 0);
    clean(&s);
}

#[test]
fn every_short_work_grant_is_sticky_through_actual_learning_tail() {
    let used = baseline();
    for work in 0..used.work_admitted {
        let (mut s, reference, _) = fork(0, 0);
        let before = trace_rows(&s);
        let owner = test_owner(work, 100_000_000);
        attach(&mut s, &owner);
        assert_eq!(
            learn(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget),
            "work {work}"
        );
        assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
        let frozen = owner.usage().unwrap();
        assert_eq!(
            learn(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(owner.usage().unwrap(), frozen);
        failed(&s, &before);
    }
}

#[test]
fn every_short_storage_grant_is_sticky_with_no_partial_proof_authority() {
    let used = baseline();
    for storage in 0..used.storage_admitted {
        let (mut s, reference, _) = fork(0, 0);
        let before = trace_rows(&s);
        let owner = test_owner(100_000_000, storage);
        attach(&mut s, &owner);
        assert_eq!(
            learn(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget),
            "storage {storage}"
        );
        assert_eq!(owner.check(), Err(CountedAdmissionError::StorageExhausted));
        let frozen = owner.usage().unwrap();
        assert_eq!(
            learn(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(owner.usage().unwrap(), frozen);
        failed(&s, &before);
    }
}

#[test]
fn every_learning_observer_cut_including_publication_fence_terminalizes_exact_owner() {
    let (mut s, reference, _) = fork(0, 0);
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut s, &observing_owner(usize::MAX, &calls));
    learn(&mut s, reference).unwrap();
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 30);
    for cut in 0..total {
        let (mut s, reference, _) = fork(0, 0);
        let before = trace_rows(&s);
        let calls = Arc::new(AtomicUsize::new(0));
        let owner = observing_owner(cut, &calls);
        attach(&mut s, &owner);
        assert_eq!(
            learn(&mut s, reference),
            Err(SatUnknownReason::Interrupted),
            "observer {cut}"
        );
        let frozen = owner.usage().unwrap();
        assert_eq!(learn(&mut s, reference), Err(SatUnknownReason::Interrupted));
        assert_eq!(owner.usage().unwrap(), frozen);
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        failed(&s, &before);
    }
}
