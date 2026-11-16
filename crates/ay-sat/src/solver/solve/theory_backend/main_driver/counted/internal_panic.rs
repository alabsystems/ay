// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;
use crate::counted_storage::test_owner;
use crate::decision_trace::TraceEvent;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering};

#[test]
fn safe_internal_panic_under_driver_custody_terminalizes_owner_and_trace() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("internal");
    let mut s = Solver::new(2);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    assert!(s.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1))
    ]));
    s.initialize_watches();
    s.enable_decision_trace(path.to_str().unwrap()).unwrap();
    s.cold
        .decision_trace
        .as_mut()
        .unwrap()
        .write_event(&TraceEvent::Decide { lit_dimacs: 1 })
        .unwrap();
    let owner = test_owner(10_000_000, 10_000_000);
    assert!(s.attach_counted_admission(owner.clone()).is_ok());
    let reached = AtomicUsize::new(0);
    let panic = catch_unwind(AssertUnwindSafe(|| {
        let guard = Guard {
            solver: &mut s,
            owner: owner.clone(),
            completed: false,
        };
        prepare::entry(guard.solver, &guard.owner).unwrap();
        assert!(guard.owner.usage().unwrap().refusal.is_none());
        assert!(guard.solver.cold.decision_trace.is_some());
        reached.fetch_add(1, Ordering::SeqCst);
        let empty: &[Literal] = &[];
        assert!(std::hint::black_box(empty).len() > std::hint::black_box(0));
    }));
    let _ = panic.expect_err("the injected internal panic must be reached");
    assert_eq!(reached.load(Ordering::SeqCst), 1);
    assert_eq!(
        owner.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::OperationPanicked
        ))
    );
    assert!(s.clause_trace().unwrap().proof_work_exhausted());
    assert!(s.cold.decision_trace.is_none());
    drop(s);
    assert_eq!(std::fs::metadata(path).unwrap().len(), 9);
}
