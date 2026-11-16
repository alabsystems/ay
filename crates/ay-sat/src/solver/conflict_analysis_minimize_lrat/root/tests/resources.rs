// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]
use super::*;

#[test]
fn exact_work_storage_and_every_work_cut_cover_real_root_finalization() {
    for kind in [Roots::Input, Roots::Implied] {
        let (mut baseline, conflict, _) = analysis_fixture(kind);
        let owner = test_owner(1_000_000, 1_000_000);
        assert!(baseline.attach_counted_admission(owner.clone()).is_ok());
        let expected = run(&mut baseline, conflict).unwrap();
        let used = owner.usage().unwrap();
        assert!(used.work_admitted > 100 && used.storage_admitted > 0);
        for work in 0..=used.work_admitted {
            let (mut s, conflict, _) = analysis_fixture(kind);
            let owner = test_owner(work, used.storage_admitted);
            assert!(s.attach_counted_admission(owner.clone()).is_ok());
            let result = run(&mut s, conflict);
            if work == used.work_admitted {
                assert_eq!(result.unwrap(), expected);
                assert_eq!(owner.usage().unwrap().work_remaining, 0);
                assert_eq!(owner.usage().unwrap().storage_remaining, 0);
            } else {
                assert_eq!(result, Err(SatUnknownReason::ResourceBudget));
                assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
                let receipt = owner.usage().unwrap();
                assert!(run(&mut s, conflict).is_err());
                assert_eq!(owner.usage().unwrap(), receipt);
            }
            clean(&s);
        }
        let (mut s, conflict, _) = analysis_fixture(kind);
        let owner = test_owner(used.work_admitted, used.storage_admitted - 1);
        assert!(s.attach_counted_admission(owner.clone()).is_ok());
        assert!(run(&mut s, conflict).is_err());
        assert_eq!(owner.check(), Err(CountedAdmissionError::StorageExhausted));
        clean(&s);
    }
}

fn observing(cut: usize, calls: &Arc<AtomicUsize>) -> CountedAdmission {
    let calls = Arc::clone(calls);
    CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        None,
        Arc::new(move || calls.fetch_add(1, Ordering::SeqCst) == cut),
    )
    .unwrap()
}

#[test]
fn every_original_observer_poll_is_terminal_and_quiet_across_root_bfs_and_finish() {
    let calls = Arc::new(AtomicUsize::new(0));
    let (mut s, conflict, _) = analysis_fixture(Roots::Implied);
    assert!(s
        .attach_counted_admission(observing(usize::MAX, &calls))
        .is_ok());
    run(&mut s, conflict).unwrap();
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 50);
    for cut in 0..total {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("root-stop");
        let (mut s, conflict, _) = analysis_fixture(Roots::Implied);
        let before = rows(&s);
        s.enable_decision_trace(path.to_str().unwrap()).unwrap();
        s.cold
            .decision_trace
            .as_mut()
            .unwrap()
            .write_event(&TraceEvent::Decide { lit_dimacs: 1 })
            .unwrap();
        let calls = Arc::new(AtomicUsize::new(0));
        let owner = observing(cut, &calls);
        assert!(s.attach_counted_admission(owner.clone()).is_ok());
        assert_eq!(
            run(&mut s, conflict),
            Err(SatUnknownReason::Interrupted),
            "poll {cut}"
        );
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        assert_eq!(rows(&s), before);
        assert!(s.cold.decision_trace.is_none());
        clean(&s);
        assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
        drop(s);
        assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
    }
}

#[test]
fn selected_external_proof_and_pending_hint_routes_refuse_before_materialization() {
    for mutate in [
        (|s: &mut Solver| s.cold.proof_vars_compacted = true) as fn(&mut Solver),
        |s| s.cold.veripb_hints.derived.ready.push(9),
        |s| s.set_proof_bookkeeping_budget(Some(100)),
    ] {
        let mut s = materializer();
        mutate(&mut s);
        let before = rows(&s);
        let owner = test_owner(1_000_000, 1_000_000);
        assert!(s
            .materialize_level0_unit_proofs_impl(false, &Counted(&owner))
            .is_err());
        assert_eq!(s.stats.lrat_materialize_calls, 0);
        assert_eq!(rows(&s), before);
        assert!(owner.check().is_err());
    }
}

#[test]
fn owned_materializer_scratch_unwind_returns_buffers_and_never_flushes_pending_trace() {
    use std::panic::{catch_unwind, AssertUnwindSafe};
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("owned");
    let mut s = materializer();
    s.cold.lrat_level0_unit_materialize_pinned = vec![1];
    s.cold.lrat_materialize_hints_buf = Vec::with_capacity(16);
    s.enable_decision_trace(path.to_str().unwrap()).unwrap();
    s.cold
        .decision_trace
        .as_mut()
        .unwrap()
        .write_event(&TraceEvent::Decide { lit_dimacs: 1 })
        .unwrap();
    let owner = test_owner(1_000_000, 1_000_000);
    Counted(&owner).enter(&mut s).unwrap();
    let reached = AtomicUsize::new(0);
    assert!(catch_unwind(AssertUnwindSafe(|| {
        let scratch = Scratch::new(&mut s, Some(&owner));
        assert_eq!(scratch.pinned, [1]);
        assert!(owner.check().is_ok());
        reached.fetch_add(1, Ordering::SeqCst);
        let _ = scratch.pinned[scratch.pinned.len()];
    }))
    .is_err());
    assert_eq!(reached.load(Ordering::SeqCst), 1);
    assert_eq!(
        owner.check(),
        Err(CountedAdmissionError::Original(
            OriginalAdmissionError::OperationPanicked
        ))
    );
    assert_eq!(s.cold.lrat_level0_unit_materialize_cursor, 0);
    assert_eq!(s.cold.lrat_materialize_hints_buf.len(), 0);
    assert_eq!(s.cold.lrat_materialize_hints_buf.capacity(), 16);
    assert!(s.cold.clause_trace.as_ref().unwrap().proof_work_exhausted());
    assert!(s.cold.decision_trace.is_none());
    assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
    drop(s);
    assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
}
