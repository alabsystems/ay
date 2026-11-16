// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]
use super::*;
use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};

struct HostilePayload(Arc<AtomicUsize>);
impl Drop for HostilePayload {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
        panic!("root observer payload destructor");
    }
}

#[test]
fn hostile_payload_inside_actual_materialization_retires_owned_buffers_and_no_late_flush() {
    let baseline_calls = Arc::new(AtomicUsize::new(0));
    let count = Arc::clone(&baseline_calls);
    let observer = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        None,
        Arc::new(move || {
            count.fetch_add(1, Ordering::SeqCst);
            false
        }),
    )
    .unwrap();
    let mut before = materializer();
    Counted(&observer).enter(&mut before).unwrap();
    let entry_polls = baseline_calls.load(Ordering::SeqCst);
    baseline_calls.store(0, Ordering::SeqCst);
    before
        .materialize_level0_unit_proofs_impl(false, &Counted(&observer))
        .unwrap();
    let total = baseline_calls.load(Ordering::SeqCst);
    let cut = entry_polls + (total - entry_polls) / 2;
    assert!(cut > entry_polls + 3 && cut + 3 < total);

    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("hostile");
    let mut s = materializer();
    let original_rows = rows(&s);
    s.enable_decision_trace(path.to_str().unwrap()).unwrap();
    s.cold
        .decision_trace
        .as_mut()
        .unwrap()
        .write_event(&TraceEvent::Decide { lit_dimacs: 1 })
        .unwrap();
    let calls = Arc::new(AtomicUsize::new(0));
    let called = Arc::clone(&calls);
    let drops = Arc::new(AtomicUsize::new(0));
    let dropped = Arc::clone(&drops);
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        None,
        Arc::new(move || {
            if called.fetch_add(1, Ordering::SeqCst) == cut {
                panic_any(HostilePayload(Arc::clone(&dropped)));
            }
            false
        }),
    )
    .unwrap();
    assert!(catch_unwind(AssertUnwindSafe(|| {
        s.materialize_level0_unit_proofs_impl(false, &Counted(&owner))
    }))
    .is_err());
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
    assert_eq!(
        owner.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::ObserverPanicked
        ))
    );
    assert_eq!(rows(&s), original_rows);
    assert!(s.cold.clause_trace.as_ref().unwrap().proof_work_exhausted());
    assert_eq!(s.cold.lrat_materialize_hints_buf.len(), 0);
    assert_eq!(s.cold.lrat_level0_unit_materialize_pinned.len(), 0);
    assert_eq!(s.cold.lrat_level0_unit_materialize_cursor, 0);
    assert!(s.cold.decision_trace.is_none());
    let receipt = owner.usage().unwrap();
    assert!(s
        .materialize_level0_unit_proofs_impl(false, &Counted(&owner))
        .is_err());
    assert_eq!(owner.usage().unwrap(), receipt);
    assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
    drop(s);
    assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
}
