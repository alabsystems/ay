// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;

#[test]
fn exact_original_work_storage_and_every_short_work_cut_gate_terminal_publication() {
    let (mut baseline, conflict, _) = fixture();
    let owner = test_owner(1_000_000, 1_000_000);
    baseline.attach_counted_admission(owner.clone()).unwrap();
    let expected = core(run(&mut baseline, conflict, &owner).unwrap());
    let used = owner.usage().unwrap();
    assert!(used.work_admitted > 200 && used.storage_admitted > 0);
    for work in 0..=used.work_admitted {
        let (mut s, conflict, _) = fixture();
        let owner = test_owner(work, used.storage_admitted);
        s.attach_counted_admission(owner.clone()).unwrap();
        let result = run(&mut s, conflict, &owner);
        if work == used.work_admitted {
            assert_eq!(core(result.unwrap()), expected);
            assert_eq!(owner.usage().unwrap().work_remaining, 0);
            assert_eq!(owner.usage().unwrap().storage_remaining, 0);
        } else {
            assert!(
                matches!(result, Err(SatUnknownReason::ResourceBudget)),
                "work {work}"
            );
            assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
            let receipt = owner.usage().unwrap();
            assert!(run(&mut s, conflict, &owner).is_err());
            assert_eq!(owner.usage().unwrap(), receipt);
        }
        clean(&s);
    }
    let (mut s, conflict, _) = fixture();
    let owner = test_owner(used.work_admitted, used.storage_admitted - 1);
    s.attach_counted_admission(owner.clone()).unwrap();
    assert!(run(&mut s, conflict, &owner).is_err());
    assert_eq!(owner.check(), Err(CountedAdmissionError::StorageExhausted));
    clean(&s);
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
fn every_original_observer_poll_stops_terminal_publication_without_late_writer_flush() {
    let calls = Arc::new(AtomicUsize::new(0));
    let (mut baseline, conflict, _) = fixture();
    let owner = observing(usize::MAX, &calls);
    baseline.attach_counted_admission(owner.clone()).unwrap();
    assert!(matches!(
        run(&mut baseline, conflict, &owner).unwrap(),
        SatResult::Unsat(_)
    ));
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 50);
    for cut in 0..total {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("pending");
        let (mut s, conflict, _) = fixture();
        pending_writer(&mut s, &path);
        let before = rows(&s);
        let calls = Arc::new(AtomicUsize::new(0));
        let owner = observing(cut, &calls);
        s.attach_counted_admission(owner.clone()).unwrap();
        assert!(
            matches!(
                run(&mut s, conflict, &owner),
                Err(SatUnknownReason::Interrupted)
            ),
            "poll {cut}"
        );
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        let after = rows(&s);
        assert_eq!(&after[..before.len()], before.as_slice());
        if after.len() > before.len() {
            assert!(s.cold.clause_trace.as_ref().unwrap().proof_work_exhausted());
        }
        let receipt = owner.usage().unwrap();
        assert!(run(&mut s, conflict, &owner).is_err());
        assert_eq!(owner.usage().unwrap(), receipt);
        quiet(&s, &path);
        drop(s);
        assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
    }
}

#[test]
fn pending_decision_writer_is_not_flushed_by_successful_ordinary_or_counted_declaration() {
    let directory = tempfile::tempdir().unwrap();
    for counted in [false, true] {
        let path = directory
            .path()
            .join(if counted { "counted" } else { "ordinary" });
        let (mut s, conflict, _) = fixture();
        pending_writer(&mut s, &path);
        if counted {
            let owner = test_owner(1_000_000, 1_000_000);
            s.attach_counted_admission(owner.clone()).unwrap();
            assert!(matches!(
                run(&mut s, conflict, &owner).unwrap(),
                SatResult::Unsat(_)
            ));
        } else {
            s.record_level0_conflict_chain(conflict);
            assert!(matches!(s.declare_unsat(), SatResult::Unsat(_)));
        }
        assert!(s.cold.decision_trace.is_some());
        assert_eq!(std::fs::metadata(&path).unwrap().len(), 9);
        s.cold
            .decision_trace
            .take()
            .unwrap()
            .discard_without_flush();
    }
}
