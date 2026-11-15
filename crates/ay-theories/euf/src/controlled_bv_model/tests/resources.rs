// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_work_accepts_and_one_short_refuses_with_same_prepared_source() {
    let (terms, roots, assignments) = fixture(8, false);
    let source = prepare(&terms, &assignments);
    let (_, units, bytes, _) = measured(&source, &roots, u64::MAX, usize::MAX);
    assert!(measured(&source, &roots, units, bytes).0.is_ok());
    assert!(matches!(
        measured(&source, &roots, units - 1, bytes).0,
        Err(QueryError::Exhausted)
    ));
    assert!(!source.dirty);
    assert!(source.model_term_scope.is_none());
}

#[test]
fn exact_copy_accepts_and_one_short_refuses_before_public_data_return() {
    let (terms, roots, assignments) = fixture(8, false);
    let source = prepare(&terms, &assignments);
    let (_, units, bytes, _) = measured(&source, &roots, u64::MAX, usize::MAX);
    assert!(measured(&source, &roots, units, bytes).0.is_ok());
    assert!(matches!(
        measured(&source, &roots, units, bytes - 1).0,
        Err(QueryError::Exhausted)
    ));
    assert!(!source.dirty);
}

#[test]
fn cloned_original_owner_accumulates_calls_and_cannot_renew_exhaustion() {
    let (terms, roots, assignments) = fixture(8, false);
    let source = prepare(&terms, &assignments);
    let (_, units, bytes, _) = measured(&source, &roots, u64::MAX, usize::MAX);
    let flag = Arc::new(AtomicBool::new(false));
    let original = owner(
        2 * units,
        2 * bytes,
        Instant::now() + Duration::from_secs(20),
        &flag,
    );
    let clone = original.clone();
    for account in [&original, &clone] {
        assert!(account
            .with_work(
                |work| source.try_extract_prepared_bv_model_from_roots_with_budget(&roots, work)
            )
            .is_ok());
    }
    assert!(matches!(
        clone.with_work(
            |work| source.try_extract_prepared_bv_model_from_roots_with_budget(&roots, work)
        ),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
    assert!(matches!(
        original.check(),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
}

#[test]
fn observer_refusal_remains_sticky_after_external_reset() {
    let (terms, roots, assignments) = fixture(8, false);
    let source = prepare(&terms, &assignments);
    let flag = Cell::new(false);
    let calls = Cell::new(0usize);
    let mut stop = || {
        calls.set(calls.get() + 1);
        if calls.get() == 12 {
            flag.set(true);
        }
        if flag.get() {
            ControlFlow::Break(StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut work = WorkBudget::new(100_000_000, &mut stop);
    assert!(matches!(
        source.try_extract_prepared_bv_model_from_roots_with_budget(&roots, &mut work),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    ));
    flag.set(false);
    let before = calls.get();
    assert!(matches!(
        source.try_extract_prepared_bv_model_from_roots_with_budget(&roots, &mut work),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    ));
    assert_eq!(calls.get(), before);
}

#[test]
fn final_success_scratch_poll_vetoes_complete_model_and_preserves_source() {
    let (terms, roots, assignments) = fixture(8, false);
    let source = prepare(&terms, &assignments);
    let (_, _, _, final_poll) = measured(&source, &roots, u64::MAX, usize::MAX);
    let polls = Cell::new(0usize);
    let positive = Cell::new(0usize);
    let mut sink = |units: usize, _: usize| {
        if units == 0 {
            polls.set(polls.get() + 1);
            if polls.get() == final_poll {
                return Err(QueryError::Interrupted(StopReason::Deadline));
            }
        } else {
            positive.set(positive.get() + units);
        }
        Ok(())
    };
    let mut work = WorkBudget::with_admission(u64::MAX, &mut sink);
    assert!(matches!(
        source.try_extract_prepared_bv_model_from_roots_with_budget(&roots, &mut work),
        Err(QueryError::Interrupted(StopReason::Deadline))
    ));
    assert!(positive.get() > 0);
    assert!(!source.dirty);
}

#[test]
fn caught_callback_panic_latches_original_owner_without_rebuilding() {
    let (terms, roots, assignments) = fixture(8, false);
    let source = prepare(&terms, &assignments);
    let calls = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let original = OriginalAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 256_000_000),
        Instant::now() + Duration::from_secs(20),
        Arc::new(move || {
            if observed.fetch_add(1, Ordering::SeqCst) == 12 {
                panic!("fixture observer panic");
            }
            false
        }),
    );
    assert!(matches!(
        original.with_work(
            |work| source.try_extract_prepared_bv_model_from_roots_with_budget(&roots, work)
        ),
        Err(OriginalAdmissionError::ObserverPanicked)
    ));
    assert!(matches!(
        original.check(),
        Err(OriginalAdmissionError::ObserverPanicked)
    ));
    assert!(!source.dirty);
    assert!(source.model_term_scope.is_none());
}

#[test]
fn original_absolute_end_refuses_empty_roots_without_new_allowance() {
    let (terms, _, assignments) = fixture(8, false);
    let source = prepare(&terms, &assignments);
    let flag = Arc::new(AtomicBool::new(false));
    let end = Instant::now();
    let original = owner(100_000_000, 256_000_000, end, &flag);
    assert!(matches!(
        original.with_work(
            |work| source.try_extract_prepared_bv_model_from_roots_with_budget(&[], work)
        ),
        Err(OriginalAdmissionError::Query(QueryError::Interrupted(
            StopReason::Deadline
        )))
    ));
    assert_eq!(original.deadline(), end);
    assert!(source.model_term_scope.is_none());
}
