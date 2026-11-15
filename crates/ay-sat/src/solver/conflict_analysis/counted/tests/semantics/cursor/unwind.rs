// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::decision_trace::TraceEvent;
use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};

struct Payload(Arc<AtomicUsize>);
impl Drop for Payload {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
        panic!("stale-cursor observer payload destructor");
    }
}

fn pending(path: &std::path::Path, stale: bool) -> (Solver, ClauseRef) {
    let (mut s, reference, _) = fixture(1, Reasons::Long);
    if stale {
        s.var_data[2].trail_pos = u32::MAX;
    }
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

fn polls(stale: bool) -> (usize, usize) {
    let directory = tempfile::tempdir().unwrap();
    let (mut s, reference) = pending(&directory.path().join("baseline"), stale);
    let trail_len = s.trail.len();
    let calls = Arc::new(AtomicUsize::new(0));
    attach(&mut s, &observing_owner(usize::MAX, &calls));
    let actual = run(&mut s, reference).unwrap().unwrap();
    assert_eq!(actual.clause, [neg(2), neg(1), neg(0)]);
    assert!(actual.chain.len() >= 3);
    (calls.load(Ordering::SeqCst), trail_len)
}

#[test]
fn every_stale_fallback_observer_unwind_discards_pending_trace_without_flush() {
    let (normal, trail_len) = polls(false);
    let (total, stale_len) = polls(true);
    assert_eq!(trail_len, stale_len);
    // The fallback's actual one-unit reads are the only additional polls.
    // Enumerating all of them exercises panic inside that scan, not only
    // constructor/entry/finish boundaries or an observer before ownership.
    assert_eq!(total, normal + trail_len);
    for cut in 0..total {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("hostile");
        let (mut s, reference) = pending(&path, true);
        let trace = format!("{:?}", s.clause_trace());
        let calls = Arc::new(AtomicUsize::new(0));
        let called = Arc::clone(&calls);
        let drops = Arc::new(AtomicUsize::new(0));
        let dropped = Arc::clone(&drops);
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(100_000_000, 100_000_000),
            None,
            Arc::new(move || {
                if called.fetch_add(1, Ordering::SeqCst) == cut {
                    panic_any(Payload(Arc::clone(&dropped)));
                }
                false
            }),
        )
        .unwrap();
        attach(&mut s, &owner);
        assert!(
            catch_unwind(AssertUnwindSafe(|| run(&mut s, reference))).is_err(),
            "poll {cut}"
        );
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(
            owner.check(),
            Err(CountedAdmissionError::Original(
                OriginalAdmissionError::ObserverPanicked
            ))
        );
        let frozen = owner.usage().unwrap();
        assert_eq!(
            run(&mut s, reference),
            Err(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(owner.usage().unwrap(), frozen);
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        assert_eq!(format!("{:?}", s.clause_trace()), trace);
        clean(&s);
        assert!(s.cold.decision_trace.is_none());
        assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
        drop(s);
        assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
    }
}
