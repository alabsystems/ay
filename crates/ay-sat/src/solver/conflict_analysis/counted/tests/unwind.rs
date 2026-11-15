// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::decision_trace::TraceEvent;
use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};

struct HostilePayload(Arc<AtomicUsize>);
impl Drop for HostilePayload {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
        panic!("test observer payload destructor");
    }
}

fn pending(path: &std::path::Path) -> (Solver, ClauseRef) {
    let (mut s, reference, _) = fixture(1, Reasons::Long);
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
    (s, reference)
}

fn no_flush(s: Solver, path: &std::path::Path) {
    assert!(s.cold.decision_trace.is_none());
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    drop(s);
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
}

#[test]
fn successful_scope_preserves_the_exact_pending_decision_trace() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("healthy");
    let (mut s, reference) = pending(&path);
    let before = s
        .cold
        .decision_trace
        .as_ref()
        .unwrap()
        .decision_test_snapshot();
    attach(&mut s, &test_owner(100_000_000, 100_000_000));
    assert!(run(&mut s, reference).unwrap().is_some());
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
fn explicit_scope_abandonment_discards_pending_trace_without_late_flush() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("abandoned");
    let (mut s, reference) = pending(&path);
    attach(&mut s, &test_owner(100_000_000, 100_000_000));
    let scope = s
        .begin_counted_standard_analysis(reference)
        .unwrap()
        .unwrap();
    assert!(!scope.learned_clause().is_empty());
    drop(scope);
    clean(&s);
    no_flush(s, &path);
}

#[test]
fn hostile_observer_payload_at_entry_middle_and_finish_preserves_sticky_refusal() {
    let (mut baseline, reference, _) = fixture(1, Reasons::Long);
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut baseline, &observing_owner(usize::MAX, &calls));
    assert!(run(&mut baseline, reference).unwrap().is_some());
    let total = calls.load(Ordering::SeqCst);
    for cut in [0, total / 2, total - 1] {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("hostile");
        let (mut s, reference) = pending(&path);
        let calls = Arc::new(AtomicUsize::new(0));
        let called = Arc::clone(&calls);
        let drops = Arc::new(AtomicUsize::new(0));
        let dropped = Arc::clone(&drops);
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(100_000_000, 100_000_000),
            None,
            Arc::new(move || {
                if called.fetch_add(1, Ordering::SeqCst) == cut {
                    panic_any(HostilePayload(Arc::clone(&dropped)));
                }
                false
            }),
        )
        .unwrap();
        attach(&mut s, &owner);
        assert!(catch_unwind(AssertUnwindSafe(|| run(&mut s, reference))).is_err());
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(
            owner.check(),
            Err(CountedAdmissionError::Original(
                OriginalAdmissionError::ObserverPanicked
            ))
        );
        assert_eq!(
            run(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        clean(&s);
        no_flush(s, &path);
    }
}

#[test]
fn inactive_clause_reference_refuses_without_panicking_and_discards_trace() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("inactive-reference");
    let (mut s, _) = pending(&path);
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut s, &owner);
    let outcome = catch_unwind(AssertUnwindSafe(|| run(&mut s, ClauseRef(u32::MAX))));
    assert_eq!(outcome.unwrap(), Err(SatUnknownReason::ResourceBudget));
    assert_eq!(
        owner.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::Query(ay_core::original_query::QueryError::Invalid(
                "counted ordinary analysis cannot bump an inactive clause"
            ))
        ))
    );
    let frozen = owner.usage().unwrap();
    assert_eq!(
        run(&mut s, ClauseRef(u32::MAX)),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(owner.usage().unwrap(), frozen);
    clean(&s);
    no_flush(s, &path);
}

#[test]
fn post_analysis_owned_scope_operation_panic_retires_live_scratch_without_flush() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("owned-operation-unwind");
    let (mut s, reference) = pending(&path);
    let trace = s
        .cold
        .decision_trace
        .as_ref()
        .unwrap()
        .decision_test_snapshot();
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut s, &owner);
    let reached = AtomicUsize::new(0);
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        // Own the actual scope INSIDE the catch boundary: an outer borrowed
        // scope would survive unwinding and would not exercise its Drop guard.
        let scope = s
            .begin_counted_standard_analysis(reference)
            .unwrap()
            .unwrap();
        assert!(scope.retirement.active);
        assert!(!scope.retirement.solver.conflict.analyzed_vars().is_empty());
        assert!(scope
            .retirement
            .solver
            .var_data
            .iter()
            .any(|data| data.is_seen()));
        assert_eq!(
            scope
                .retirement
                .solver
                .cold
                .decision_trace
                .as_ref()
                .unwrap()
                .decision_test_snapshot(),
            trace
        );
        assert!(owner.usage().unwrap().refusal.is_none());
        let end = scope.learned_clause().len();
        assert!(end > 0);
        assert!(scope.resolution_chain().len() >= 3);
        reached.fetch_add(1, Ordering::SeqCst);
        // An actual safe bounds-check panic in a private continuation operation,
        // not an observer panic, invalid arena pointer or production test hook.
        std::hint::black_box(scope.learned_clause()[end]);
        reached.fetch_add(1, Ordering::SeqCst);
    }));
    let payload = outcome.expect_err("the owned private-result operation must panic");
    assert_eq!(reached.load(Ordering::SeqCst), 1);
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied());
    assert!(message.is_some_and(|message| message.contains("index out of bounds")));
    assert_eq!(
        owner.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::OperationPanicked
        ))
    );
    let frozen = owner.usage().unwrap();
    assert_eq!(
        run(&mut s, reference),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(owner.usage().unwrap(), frozen);
    clean(&s);
    no_flush(s, &path);
}

#[cfg(all(feature = "jit", target_arch = "aarch64"))]
#[test]
fn every_native_observer_cut_retires_unregistered_marks_and_preserves_trace_boundary() {
    let (mut baseline, reference, _) = fixture(1, Reasons::Long);
    baseline.compile_conflict_processor();
    assert!(baseline.standard_native_available());
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut baseline, &observing_owner(usize::MAX, &calls));
    assert!(run(&mut baseline, reference).unwrap().is_some());
    let total = calls.load(Ordering::SeqCst);
    let mut cuts_after_native = 0;
    for cut in 0..total {
        let (mut s, reference, _) = fixture(1, Reasons::Long);
        s.compile_conflict_processor();
        let calls = Arc::new(AtomicUsize::new(0));
        attach(&mut s, &observing_owner(cut, &calls));
        assert_eq!(run(&mut s, reference), Err(SatUnknownReason::Interrupted));
        if s.stats.sat_conflict_analysis_native_applications > 0 {
            cuts_after_native += 1;
        }
        clean(&s);
    }
    assert!(
        cuts_after_native > 10,
        "must interrupt actual post-native bookkeeping/finalization"
    );
}
