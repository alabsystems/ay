// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::decision_trace::TraceEvent;
use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};

fn pending(path: &std::path::Path) -> (Solver, ClauseRef) {
    let (mut s, reference, _) = fork(0, 0);
    s.enable_decision_trace(path.to_str().unwrap()).unwrap();
    s.cold
        .decision_trace
        .as_mut()
        .unwrap()
        .write_event(&TraceEvent::Decide { lit_dimacs: 1 })
        .unwrap();
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    (s, reference)
}

#[test]
fn learned_trace_and_replay_preserve_exact_inprocess_then_learn_bytes() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("learning");
    let (mut s, reference) = pending(&path);
    let id = s.cold.next_clause_id;
    s.cold.replay_trace = Some(crate::decision_trace::ReplayTrace::decision_test_new(vec![
        TraceEvent::Inprocess {
            pass_code: Solver::diagnostic_pass_code(DiagnosticPass::Learning),
        },
        TraceEvent::Learn { clause_id: id },
    ]));
    attach(&mut s, &test_owner(100_000_000, 100_000_000));
    let step = learn(&mut s, reference).unwrap();
    assert_eq!(s.clause_id(step.reference), id);
    assert_eq!(
        s.cold.replay_trace.as_ref().unwrap().decision_test_cursor(),
        2
    );
    let recorded = s
        .cold
        .decision_trace
        .as_ref()
        .unwrap()
        .decision_test_snapshot();
    assert_eq!(recorded.0, 3);
    assert_eq!(recorded.1.len(), 5 + 2 + 9);
    // Independent wire-format oracle: Decide=1 + little-endian i32(1),
    // Inprocess=7 + stable Learning pass=2, Learn=4 + little-endian u64 ID.
    // Do not call the production serializer to manufacture expected bytes.
    let mut expected_bytes = vec![1, 1, 0, 0, 0, 7, 2, 4];
    expected_bytes.extend_from_slice(&id.to_le_bytes());
    assert_eq!(recorded.1, expected_bytes);
    assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
    let ordinary_path = directory.path().join("ordinary");
    let (mut ordinary, reference) = pending(&ordinary_path);
    assert_eq!(ordinary.cold.next_clause_id, id);
    ordinary.analyze_and_backtrack(reference, "exact learning trace parity", |_, _| {});
    let ordinary_pending = ordinary
        .cold
        .decision_trace
        .as_ref()
        .unwrap()
        .decision_test_snapshot();
    assert_eq!(ordinary_pending, recorded);
    assert_eq!(std::fs::metadata(&ordinary_path).unwrap().len(), 9);
}

#[test]
fn every_writer_observer_cut_discards_exact_pending_descriptor_without_late_flush() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("baseline");
    let (mut s, reference) = pending(&path);
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut s, &observing_owner(usize::MAX, &calls));
    learn(&mut s, reference).unwrap();
    let total = calls.load(Ordering::SeqCst);
    for cut in 0..total {
        let path = directory.path().join(format!("cut-{cut}"));
        let (mut s, reference) = pending(&path);
        let calls = Arc::new(AtomicUsize::new(0));
        attach(&mut s, &observing_owner(cut, &calls));
        assert_eq!(learn(&mut s, reference), Err(SatUnknownReason::Interrupted));
        clean(&s);
        assert!(s.cold.decision_trace.is_none());
        assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
        drop(s);
        assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
    }
}

struct Hostile(Arc<AtomicUsize>);
impl Drop for Hostile {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
        panic!("learning observer payload destructor");
    }
}

#[test]
fn hostile_payload_after_insertion_and_at_final_fence_removes_proof_and_output_authority() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("baseline");
    let (mut s, reference) = pending(&path);
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut s, &observing_owner(usize::MAX, &calls));
    learn(&mut s, reference).unwrap();
    let total = calls.load(Ordering::SeqCst);
    for cut in [total - 2, total - 1] {
        let path = directory.path().join(format!("hostile-{cut}"));
        let (mut s, reference) = pending(&path);
        let before = trace_rows(&s);
        let called = Arc::new(AtomicUsize::new(0));
        let calls = Arc::clone(&called);
        let drops = Arc::new(AtomicUsize::new(0));
        let dropped = Arc::clone(&drops);
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(100_000_000, 100_000_000),
            None,
            Arc::new(move || {
                if called.fetch_add(1, Ordering::SeqCst) == cut {
                    panic_any(Hostile(Arc::clone(&dropped)));
                }
                false
            }),
        )
        .unwrap();
        attach(&mut s, &owner);
        assert!(catch_unwind(AssertUnwindSafe(|| learn(&mut s, reference))).is_err());
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        assert_eq!(
            owner.check(),
            Err(CountedAdmissionError::Original(
                OriginalAdmissionError::ObserverPanicked
            ))
        );
        assert!(
            trace_rows(&s).len() > before.len(),
            "actual insertion must have occurred"
        );
        assert!(s.clause_trace().unwrap().proof_work_exhausted());
        clean(&s);
        assert!(s.cold.decision_trace.is_none());
        drop(s);
        assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
    }
}
