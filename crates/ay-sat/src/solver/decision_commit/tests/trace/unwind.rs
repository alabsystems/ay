// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};

struct PanickingPayload(Arc<AtomicUsize>);

impl Drop for PanickingPayload {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
        panic!("test panic payload destructor");
    }
}

fn pending_fixture(path: &std::path::Path) -> Solver {
    let mut s = traced_fixture(path);
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
    s
}

enum PanicAt {
    Preflight,
    PublicationFence,
}

fn check_observer_payload_unwind(at: PanicAt) {
    let directory = tempfile::tempdir().unwrap();
    let mut baseline = pending_fixture(&directory.path().join("baseline"));
    let calls = Arc::new(AtomicUsize::new(0));
    attach(
        &mut baseline,
        &controls::observing_owner(usize::MAX, &calls),
    );
    assert_eq!(baseline.decide_counted(lit(3)), Ok(()));
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 1);
    let stop_at = match at {
        PanicAt::Preflight => 0,
        PanicAt::PublicationFence => total - 1,
    };
    let path = directory.path().join("unwind");
    let mut s = pending_fixture(&path);
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
    let escaped = catch_unwind(AssertUnwindSafe(|| s.decide_counted(lit(3))));
    assert!(
        escaped.is_err(),
        "the opaque payload destructor must unwind"
    );
    assert_eq!(payload_drops.load(Ordering::SeqCst), 1);
    let committed = matches!(at, PanicAt::PublicationFence);
    assert_eq!(state(&s), if committed { state(&baseline) } else { before });
    assert_eq!(cursor(&s), usize::from(committed));
    assert!(s.cold.decision_trace.is_none());
    assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
    let refusal = CountedAdmissionError::Original(OriginalAdmissionError::ObserverPanicked);
    assert_eq!(owner.check(), Err(refusal));
    assert_eq!(owner.clone().check(), Err(refusal));
    let after = state(&s);
    assert_eq!(
        s.decide_counted(lit(3)),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(state(&s), after);
    assert_eq!(calls.load(Ordering::SeqCst), stop_at + 1);
    drop(s);
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
}

#[test]
fn preflight_observer_payload_unwind_retires_pending_trace_without_flush() {
    check_observer_payload_unwind(PanicAt::Preflight);
}

#[test]
fn final_fence_observer_payload_unwind_retires_pending_trace_without_flush() {
    check_observer_payload_unwind(PanicAt::PublicationFence);
}

#[test]
fn internal_assignment_unwind_latches_original_owner_and_retires_pending_trace() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("assignment-unwind");
    let mut s = pending_fixture(&path);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    // Force the real assignment kernel's bounds panic after metadata commit,
    // not an observer error. No possibly-partial state may be reused afterward.
    s.suppress_phase_saving = false;
    s.phase.clear();
    let escaped = catch_unwind(AssertUnwindSafe(|| s.decide_counted(lit(3))));
    assert!(escaped.is_err());
    assert!(s.cold.decision_trace.is_none());
    let refusal = CountedAdmissionError::Original(OriginalAdmissionError::OperationPanicked);
    assert_eq!(owner.check(), Err(refusal));
    assert_eq!(owner.clone().check(), Err(refusal));
    let after = state(&s);
    assert_eq!(
        s.decide_counted(lit(3)),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(state(&s), after);
    drop(s);
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
}
