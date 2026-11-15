// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;
use crate::decision_trace::TraceEvent;
use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};

struct Hostile(Arc<AtomicUsize>);
impl Drop for Hostile {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
        panic!("model observer payload destructor");
    }
}

fn pending(path: &std::path::Path) -> Solver {
    let mut s = reconstructed();
    s.enable_decision_trace(path.to_str().unwrap()).unwrap();
    s.cold
        .decision_trace
        .as_mut()
        .unwrap()
        .write_event(&TraceEvent::Decide { lit_dimacs: 2 })
        .unwrap();
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    s
}

#[test]
fn successful_model_publication_does_not_flush_pending_decision_output() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("pending");
    let mut s = pending(&path);
    let admission = owner();
    attach(&mut s, &admission);
    assert_eq!(
        s.declare_counted_complete_assignment_sat(&admission),
        Ok(SatResult::Sat(vec![true, false, true]))
    );
    assert!(
        s.cold
            .decision_trace
            .as_ref()
            .unwrap()
            .decision_test_snapshot()
            .1
            .len()
            > 0
    );
    assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
    s.cold
        .decision_trace
        .take()
        .unwrap()
        .discard_without_flush();
}

#[test]
fn hostile_payload_at_entry_reconstruction_and_publication_cannot_flush_later() {
    let directory = tempfile::tempdir().unwrap();
    let calls = Arc::new(AtomicUsize::new(0));
    let mut s = reconstructed();
    let admission = observed(usize::MAX, &calls);
    attach(&mut s, &admission);
    assert!(matches!(
        s.declare_counted_complete_assignment_sat(&admission),
        Ok(SatResult::Sat(_))
    ));
    let total = calls.load(Ordering::SeqCst);
    for cut in [0, total / 2, total - 1] {
        let path = directory.path().join(format!("cut-{cut}"));
        let mut s = pending(&path);
        let calls = Arc::new(AtomicUsize::new(0));
        let drops = Arc::new(AtomicUsize::new(0));
        let seen = Arc::clone(&calls);
        let dropped = Arc::clone(&drops);
        let admission = CountedAdmission::new(
            FiniteAdmissionGrant::new(1_000_000, 1_000_000),
            None,
            Arc::new(move || {
                if seen.fetch_add(1, Ordering::SeqCst) == cut {
                    panic_any(Hostile(Arc::clone(&dropped)));
                }
                false
            }),
        )
        .unwrap();
        attach(&mut s, &admission);
        assert!(catch_unwind(AssertUnwindSafe(
            || s.declare_counted_complete_assignment_sat(&admission)
        ))
        .is_err());
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        assert_eq!(
            admission.check(),
            Err(CountedAdmissionError::Original(
                OriginalAdmissionError::ObserverPanicked
            ))
        );
        refused(&s, &admission);
        drop(s);
        assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    }
}

#[test]
fn actual_internal_panic_while_model_guard_is_live_terminalizes_owner() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("panic");
    let mut s = pending(&path);
    let admission = owner();
    attach(&mut s, &admission);
    let reached = std::cell::Cell::new(false);
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        let guard = Guard {
            solver: &mut s,
            owner: &admission,
            completed: false,
        };
        prepare::entry(guard.solver, guard.owner).unwrap();
        let model = finalize(guard.solver, guard.owner).unwrap();
        assert_eq!(model, vec![true, false, true]);
        assert!(admission.usage().unwrap().refusal.is_none());
        reached.set(true);
        let invalid_index = std::hint::black_box(model.len());
        let _ = model[invalid_index];
    }));
    assert!(reached.get());
    let payload = outcome.unwrap_err();
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or("");
    assert!(message.contains("index out of bounds"), "{message}");
    assert_eq!(
        admission.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::OperationPanicked
        ))
    );
    refused(&s, &admission);
    drop(s);
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
}
