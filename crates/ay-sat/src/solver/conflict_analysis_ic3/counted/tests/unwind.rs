// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::decision_trace::TraceEvent;
use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};

struct PanickingPayload(Arc<AtomicUsize>);

impl Drop for PanickingPayload {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
        panic!("test opaque observer payload destructor");
    }
}

fn pending(path: &std::path::Path) -> (Solver, ClauseRef) {
    let (mut s, conflict, _) = fixture(2, Reasons::Long);
    s.enable_decision_trace(path.to_str().unwrap()).unwrap();
    s.cold
        .decision_trace
        .as_mut()
        .unwrap()
        .write_event(&TraceEvent::Decide { lit_dimacs: 1 })
        .unwrap();
    assert_eq!(
        s.cold
            .decision_trace
            .as_ref()
            .unwrap()
            .decision_test_snapshot()
            .1
            .len(),
        5
    );
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    (s, conflict)
}

fn assert_no_late_flush(s: Solver, path: &std::path::Path) {
    assert!(s.cold.decision_trace.is_none());
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    drop(s);
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
}

#[test]
fn successful_resolution_retains_the_exact_pending_trace_without_emitting() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("healthy");
    let (mut s, conflict) = pending(&path);
    let before = s
        .cold
        .decision_trace
        .as_ref()
        .unwrap()
        .decision_test_snapshot();
    attach(&mut s, &test_owner(10_000_000, 10_000_000));
    assert!(run(&mut s, conflict).unwrap().is_some());
    assert_eq!(
        s.cold
            .decision_trace
            .as_ref()
            .unwrap()
            .decision_test_snapshot(),
        before
    );
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    clean(&s);
}

#[test]
fn refusal_through_an_owner_clone_after_begin_discards_trace_on_scope_drop() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("clone-refusal");
    let (mut s, conflict) = pending(&path);
    let before = state(&s);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    let scope = s.begin_counted_ic3_resolution(conflict).unwrap().unwrap();
    owner.clone().refuse(CountedAdmissionError::WorkExhausted);
    drop(scope);
    assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
    assert_eq!(state(&s), before);
    clean(&s);
    assert_no_late_flush(s, &path);
}

#[test]
fn opaque_observer_payload_unwind_at_entry_middle_and_finish_retires_scratch_and_trace() {
    let (mut baseline, conflict, _) = fixture(2, Reasons::Long);
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut baseline, &observing_owner(usize::MAX, &calls));
    assert!(run(&mut baseline, conflict).unwrap().is_some());
    let total = calls.load(Ordering::SeqCst);
    for stop_at in [0, total / 2, total - 1] {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("payload-unwind");
        let (mut s, conflict) = pending(&path);
        let before = state(&s);
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let payload_drops = Arc::new(AtomicUsize::new(0));
        let dropped = Arc::clone(&payload_drops);
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(10_000_000, 10_000_000),
            None,
            Arc::new(move || {
                if observed.fetch_add(1, Ordering::SeqCst) == stop_at {
                    panic_any(PanickingPayload(Arc::clone(&dropped)));
                }
                false
            }),
        )
        .unwrap();
        attach(&mut s, &owner);
        assert!(catch_unwind(AssertUnwindSafe(|| run(&mut s, conflict))).is_err());
        assert_eq!(payload_drops.load(Ordering::SeqCst), 1);
        let refusal = CountedAdmissionError::Original(OriginalAdmissionError::ObserverPanicked);
        assert_eq!(owner.check(), Err(refusal));
        assert_eq!(owner.clone().check(), Err(refusal));
        assert_eq!(run(&mut s, conflict), Err(SatUnknownReason::ResourceBudget));
        assert_eq!(calls.load(Ordering::SeqCst), stop_at + 1);
        assert_eq!(state(&s), before);
        clean(&s);
        assert_no_late_flush(s, &path);
    }
}

#[test]
fn corrupt_internal_clause_reference_unwind_is_terminal_not_a_partial_result() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("internal-unwind");
    let (mut s, _) = pending(&path);
    let before = state(&s);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    // Deliberately violate the internal arena-boundary precondition. The
    // indexed arena accessor must unwind; the armed owner must never revive.
    assert!(catch_unwind(AssertUnwindSafe(|| run(&mut s, ClauseRef(u32::MAX)))).is_err());
    let refusal = CountedAdmissionError::Original(OriginalAdmissionError::OperationPanicked);
    assert_eq!(owner.check(), Err(refusal));
    assert_eq!(owner.clone().check(), Err(refusal));
    assert_eq!(state(&s), before);
    clean(&s);
    assert_no_late_flush(s, &path);
}

#[test]
fn unwind_while_holding_the_result_retires_seen_lbd_levels_and_original_owner() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("scope-unwind");
    let (mut s, conflict) = pending(&path);
    let before = state(&s);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    assert!(catch_unwind(AssertUnwindSafe(|| {
        let _scope = s.begin_counted_ic3_resolution(conflict).unwrap().unwrap();
        panic!("test caller unwind before any publication");
    }))
    .is_err());
    assert_eq!(
        owner.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::OperationPanicked
        ))
    );
    assert_eq!(state(&s), before);
    clean(&s);
    assert_no_late_flush(s, &path);
}
