// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::decision_trace::TraceEvent;
use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};

struct HostilePayload(Arc<AtomicUsize>);
impl Drop for HostilePayload {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
        panic!("test opaque minimization observer payload destructor");
    }
}

fn pending(path: &std::path::Path) -> (Solver, ClauseRef) {
    let (mut s, conflict, _) = removable(3, Reasons::Long);
    s.enable_decision_trace(path.to_str().unwrap()).unwrap();
    s.cold
        .decision_trace
        .as_mut()
        .unwrap()
        .write_event(&TraceEvent::Decide { lit_dimacs: 1 })
        .unwrap();
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    (s, conflict)
}

fn dropped_without_flush(s: Solver, path: &std::path::Path) {
    assert!(s.cold.decision_trace.is_none());
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    drop(s);
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
}

#[test]
fn successful_minimization_retains_pending_trace_exactly_without_emission() {
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
    assert_eq!(minimize(&mut s, conflict).unwrap().lower, vec![neg(1)]);
    assert_eq!(
        s.cold
            .decision_trace
            .as_ref()
            .unwrap()
            .decision_test_snapshot(),
        before
    );
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    retired(&mut s);
}

#[test]
fn cloned_owner_refusal_after_minimization_retires_scratch_and_prevents_late_flush() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("clone-refusal");
    let (mut s, conflict) = pending(&path);
    let before = state(&s);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    let minimized = s
        .begin_counted_ic3_resolution(conflict)
        .unwrap()
        .unwrap()
        .minimize_selected()
        .unwrap();
    owner
        .clone()
        .refuse(CountedAdmissionError::StorageExhausted);
    drop(minimized);
    assert_eq!(owner.check(), Err(CountedAdmissionError::StorageExhausted));
    assert_eq!(state(&s), before);
    retired(&mut s);
    dropped_without_flush(s, &path);
}

#[test]
fn hostile_observer_payload_at_minimize_entry_recursion_and_final_fence_is_terminal() {
    let (mut baseline, conflict, _) = removable(3, Reasons::Long);
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut baseline, &observing_owner(usize::MAX, &calls));
    let scope = baseline
        .begin_counted_ic3_resolution(conflict)
        .unwrap()
        .unwrap();
    let prefix = calls.load(Ordering::SeqCst);
    scope.minimize_selected().unwrap().finish().unwrap();
    let total = calls.load(Ordering::SeqCst);
    for at in [prefix, prefix + (total - prefix) / 2, total - 1] {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("opaque-unwind");
        let (mut s, conflict) = pending(&path);
        let before = state(&s);
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let drops = Arc::new(AtomicUsize::new(0));
        let dropped = Arc::clone(&drops);
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(10_000_000, 10_000_000),
            None,
            Arc::new(move || {
                if observed.fetch_add(1, Ordering::SeqCst) == at {
                    panic_any(HostilePayload(Arc::clone(&dropped)));
                }
                false
            }),
        )
        .unwrap();
        attach(&mut s, &owner);
        assert!(catch_unwind(AssertUnwindSafe(|| minimize(&mut s, conflict))).is_err());
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        let refusal = CountedAdmissionError::Original(OriginalAdmissionError::ObserverPanicked);
        assert_eq!(owner.check(), Err(refusal));
        assert_eq!(owner.clone().check(), Err(refusal));
        assert_eq!(
            minimize(&mut s, conflict),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(calls.load(Ordering::SeqCst), at + 1);
        assert_eq!(state(&s), before);
        retired(&mut s);
        dropped_without_flush(s, &path);
    }
}

#[test]
fn corrupt_internal_lower_reason_unwind_retires_partial_recursive_marks() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("internal-unwind");
    let (mut s, conflict) = pending(&path);
    // A nonbinary, non-NO_REASON offset outside the actual arena. First-UIP
    // does not resolve this lower literal; actual recursive minimization does.
    s.var_data[4].reason = 0x7fff_ffff;
    let before = state(&s);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    assert!(catch_unwind(AssertUnwindSafe(|| minimize(&mut s, conflict))).is_err());
    assert_eq!(
        owner.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::OperationPanicked
        ))
    );
    assert_eq!(state(&s), before);
    retired(&mut s);
    dropped_without_flush(s, &path);
}

#[test]
fn caller_unwind_after_real_minimization_still_owns_and_retires_all_analysis_scratch() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("caller-unwind");
    let (mut s, conflict) = pending(&path);
    let before = state(&s);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    assert!(catch_unwind(AssertUnwindSafe(|| {
        let minimized = s
            .begin_counted_ic3_resolution(conflict)
            .unwrap()
            .unwrap()
            .minimize_selected()
            .unwrap();
        assert_eq!(minimized.lower_literals(), &[neg(1)]);
        panic!("test downstream unwind before learning");
    }))
    .is_err());
    assert_eq!(
        owner.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::OperationPanicked
        ))
    );
    assert_eq!(state(&s), before);
    retired(&mut s);
    dropped_without_flush(s, &path);
}
