// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::decision_trace::TraceEvent;
use ay_core::original_query::OriginalAdmissionError;
use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};

fn pending(path: &std::path::Path) -> (Solver, ClauseRef) {
    let (mut s, reference) = forced();
    s.enable_decision_trace(path.to_str().unwrap()).unwrap();
    s.cold
        .decision_trace
        .as_mut()
        .unwrap()
        .write_event(&TraceEvent::Decide { lit_dimacs: 3 })
        .unwrap();
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    (s, reference)
}

#[test]
fn forced_success_preserves_exact_pending_trace_bytes_without_spurious_learn_event() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("forced");
    let (mut s, reference) = pending(&path);
    let before = s
        .cold
        .decision_trace
        .as_ref()
        .unwrap()
        .decision_test_snapshot();
    attach(&mut s, &generous());
    assert_eq!(
        s.dispatch_conflict_counted(reference),
        Ok(CountedDispatchStep::Forced)
    );
    assert_eq!(
        s.cold
            .decision_trace
            .as_ref()
            .unwrap()
            .decision_test_snapshot(),
        before
    );
    assert_eq!(before.0, 1);
    assert_eq!(before.1, vec![1, 3, 0, 0, 0]);
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
}

#[test]
fn every_forced_writer_observer_cut_discards_exact_descriptor_without_late_flush() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("baseline");
    let (mut baseline, reference) = pending(&path);
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut baseline, &observing(usize::MAX, &calls));
    baseline.dispatch_conflict_counted(reference).unwrap();
    let total = calls.load(Ordering::SeqCst);
    for cut in 0..total {
        let path = directory.path().join(format!("cut-{cut}"));
        let (mut s, reference) = pending(&path);
        let before = rows(&s);
        let calls = Arc::new(AtomicUsize::new(0));
        let owner = observing(cut, &calls);
        attach(&mut s, &owner);
        assert_eq!(
            s.dispatch_conflict_counted(reference),
            Err(SatUnknownReason::Interrupted)
        );
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        assert_eq!(rows(&s), before);
        assert!(s.clause_trace().unwrap().proof_work_exhausted());
        assert!(s.cold.decision_trace.is_none());
        clean(&s);
        drop(s);
        assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    }
}

struct Hostile(Arc<AtomicUsize>);
impl Drop for Hostile {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
        panic!("dispatch observer payload destructor");
    }
}

#[test]
fn preflight_midtransition_and_final_fence_unwind_keep_original_refusal_and_no_flush() {
    let directory = tempfile::tempdir().unwrap();
    let (mut baseline, reference) = pending(&directory.path().join("baseline"));
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut baseline, &observing(usize::MAX, &calls));
    baseline.dispatch_conflict_counted(reference).unwrap();
    let total = calls.load(Ordering::SeqCst);
    for cut in [0, total / 2, total - 1] {
        let path = directory.path().join(format!("unwind-{cut}"));
        let (mut s, reference) = pending(&path);
        let before = rows(&s);
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let drops = Arc::new(AtomicUsize::new(0));
        let dropped = Arc::clone(&drops);
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(100_000_000, 100_000_000),
            None,
            Arc::new(move || {
                if observed.fetch_add(1, Ordering::SeqCst) == cut {
                    panic_any(Hostile(Arc::clone(&dropped)));
                }
                false
            }),
        )
        .unwrap();
        attach(&mut s, &owner);
        assert!(catch_unwind(AssertUnwindSafe(|| s.dispatch_conflict_counted(reference))).is_err());
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        assert_eq!(
            owner.check(),
            Err(CountedAdmissionError::Original(
                OriginalAdmissionError::ObserverPanicked
            ))
        );
        let usage = owner.usage().unwrap();
        assert_eq!(
            s.dispatch_conflict_counted(reference),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(owner.usage().unwrap(), usage);
        assert_eq!(rows(&s), before);
        assert!(s.clause_trace().unwrap().proof_work_exhausted());
        assert!(s.cold.decision_trace.is_none());
        clean(&s);
        if cut == total - 1 {
            assert_eq!(
                s.lit_val(neg(2)),
                1,
                "real asserting propagation preceded final fence"
            );
        }
        drop(s);
        assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    }
}
