// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::decision_trace::TraceEvent;
use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};

struct HostilePayload(Arc<AtomicUsize>);
impl Drop for HostilePayload {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
        panic!("test block observer payload destructor");
    }
}

fn pending(path: &std::path::Path) -> (Solver, ClauseRef) {
    let (mut s, conflict, _) = selected(3, Reasons::Long);
    s.cold.shrink_removable_kissat = true;
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

fn no_flush(s: Solver, path: &std::path::Path) {
    assert!(s.cold.decision_trace.is_none());
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    drop(s);
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
}

#[test]
fn hostile_observer_at_every_block_observation_retires_without_trace_publication() {
    let directory = tempfile::tempdir().unwrap();
    let baseline_path = directory.path().join("baseline");
    let (mut baseline, conflict) = pending(&baseline_path);
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut baseline, &observing_owner(usize::MAX, &calls));
    let scope = baseline
        .begin_counted_ic3_resolution(conflict)
        .unwrap()
        .unwrap();
    let prefix = calls.load(Ordering::SeqCst);
    scope.minimize_selected().unwrap().finish().unwrap();
    let total = calls.load(Ordering::SeqCst);
    for at in prefix..total {
        let path = directory.path().join(format!("cut-{at}"));
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
        assert_eq!(
            owner.check(),
            Err(CountedAdmissionError::Original(
                OriginalAdmissionError::ObserverPanicked
            ))
        );
        assert_eq!(state(&s), before);
        fully_retired(&mut s);
        no_flush(s, &path);
    }
}

#[test]
fn corrupt_block_reason_unwind_retires_partial_radix_walk() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("internal");
    let (mut s, conflict) = pending(&path);
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
    fully_retired(&mut s);
    no_flush(s, &path);
}

#[test]
fn successful_block_keeps_trace_pending_but_later_shared_refusal_discards_it() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("late-refusal");
    let (mut s, conflict) = pending(&path);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    let minimized = s
        .begin_counted_ic3_resolution(conflict)
        .unwrap()
        .unwrap()
        .minimize_selected()
        .unwrap();
    assert_eq!(minimized.lower_literals(), &[neg(1)]);
    assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
    owner
        .clone()
        .refuse(CountedAdmissionError::StorageExhausted);
    drop(minimized);
    fully_retired(&mut s);
    no_flush(s, &path);
}

#[test]
fn successful_block_finish_preserves_exact_pending_trace_state() {
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
    assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
    fully_retired(&mut s);
}
