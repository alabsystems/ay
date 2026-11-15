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
        panic!("driver observer payload destructor");
    }
}
fn pending(path: &std::path::Path) -> Solver {
    let mut s = unsat();
    s.enable_decision_trace(path.to_str().unwrap()).unwrap();
    s.cold
        .decision_trace
        .as_mut()
        .unwrap()
        .write_event(&TraceEvent::Decide { lit_dimacs: 1 })
        .unwrap();
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    s
}

#[test]
fn entry_midsearch_and_final_owner_unwind_cannot_flush_or_publish() {
    let directory = tempfile::tempdir().unwrap();
    let mut baseline = pending(&directory.path().join("baseline"));
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut baseline, &observing(usize::MAX, &calls));
    assert!(matches!(drive(&mut baseline), SatResult::Unsat(_)));
    assert_eq!(
        std::fs::metadata(directory.path().join("baseline"))
            .unwrap()
            .len(),
        9
    );
    assert!(
        baseline
            .cold
            .decision_trace
            .as_ref()
            .unwrap()
            .decision_test_snapshot()
            .1
            .len()
            > 5
    );
    let total = calls.load(Ordering::SeqCst);
    for cut in [0, total / 2, total - 1] {
        let path = directory.path().join(format!("cut-{cut}"));
        let mut s = pending(&path);
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let drops = Arc::new(AtomicUsize::new(0));
        let dropped = Arc::clone(&drops);
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(10_000_000, 10_000_000),
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
        assert!(catch_unwind(AssertUnwindSafe(|| drive(&mut s))).is_err());
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        assert_eq!(
            owner.check(),
            Err(CountedAdmissionError::Original(
                OriginalAdmissionError::ObserverPanicked
            ))
        );
        refused(&s, &owner);
        drop(s);
        assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
    }
}
