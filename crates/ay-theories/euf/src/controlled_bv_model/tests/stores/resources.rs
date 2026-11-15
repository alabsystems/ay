// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn four_name_store_trace_exact_work_copy_and_each_one_short_refusal() {
    let fixture = store_fixture(Sort::bitvec(64), Sort::bitvec(8));
    let source = prepare(&fixture.terms, &fixture.assignments);
    let (complete, units, bytes, _) = measured(&source, &fixture.roots, u64::MAX, usize::MAX);
    assert!(complete.is_ok());
    assert!(measured(&source, &fixture.roots, units, bytes).0.is_ok());
    assert!(matches!(
        measured(&source, &fixture.roots, units - 1, bytes).0,
        Err(QueryError::Exhausted)
    ));
    assert!(matches!(
        measured(&source, &fixture.roots, units, bytes - 1).0,
        Err(QueryError::Exhausted)
    ));
    assert!(!source.dirty);
    assert!(source.model_term_scope.is_none());
}

#[test]
fn shared_store_owner_exhaustion_cannot_be_renewed_by_clone_or_stop_reset() {
    let fixture = store_fixture(Sort::bitvec(64), Sort::bitvec(8));
    let source = prepare(&fixture.terms, &fixture.assignments);
    let (_, units, bytes, _) = measured(&source, &fixture.roots, u64::MAX, usize::MAX);
    let flag = Arc::new(AtomicBool::new(false));
    let original = owner(
        units,
        bytes,
        Instant::now() + Duration::from_secs(20),
        &flag,
    );
    let clone = original.clone();
    assert!(original
        .with_work(|work| {
            source.try_extract_prepared_bv_model_from_roots_with_budget(&fixture.roots, work)
        })
        .is_ok());
    assert!(matches!(
        clone.with_work(|work| {
            source.try_extract_prepared_bv_model_from_roots_with_budget(&fixture.roots, work)
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
    flag.store(false, Ordering::SeqCst);
    assert!(matches!(
        original.check(),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
}

#[test]
fn final_store_scratch_poll_refuses_complete_data_without_mutating_source() {
    let fixture = store_fixture(Sort::bitvec(64), Sort::bitvec(8));
    let source = prepare(&fixture.terms, &fixture.assignments);
    let parents = source.uf.parent.clone();
    let (_, _, _, final_poll) = measured(&source, &fixture.roots, u64::MAX, usize::MAX);
    let polls = Cell::new(0usize);
    let mut sink = |units: usize, _: usize| {
        if units == 0 {
            polls.set(polls.get() + 1);
            if polls.get() == final_poll {
                return Err(QueryError::Interrupted(StopReason::Deadline));
            }
        }
        Ok(())
    };
    let mut work = WorkBudget::with_admission(u64::MAX, &mut sink);
    assert!(matches!(
        source.try_extract_prepared_bv_model_from_roots_with_budget(&fixture.roots, &mut work),
        Err(QueryError::Interrupted(StopReason::Deadline))
    ));
    assert!(matches!(
        work.charge(0),
        Err(QueryError::Interrupted(StopReason::Deadline))
    ));
    assert_eq!(source.uf.parent, parents);
    assert!(!source.dirty);
}
