// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn same_original_work_is_cumulative_across_walks() {
    let deadline = end();
    let (executor, proof, scope) = fixture();
    let (units, bytes) = totals(&native_offers(&executor, &proof, &scope, deadline));
    let original = owner(2 * units, 10 * bytes, deadline);
    let calls = Cell::new(0);
    for _ in 0..2 {
        assert!(matches!(
            owned_walk(&original, &executor, &proof, &scope, &calls),
            Ok(Ok(_))
        ));
    }
    assert_eq!(
        owned_walk(&original, &executor, &proof, &scope, &calls),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    let before = calls.get();
    assert_eq!(
        owned_walk(&original.clone(), &executor, &proof, &scope, &calls),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(calls.get(), before);
}

#[test]
fn same_original_copy_allowance_is_cumulative_across_walks() {
    let deadline = end();
    let (executor, proof, scope) = fixture();
    let (units, bytes) = totals(&native_offers(&executor, &proof, &scope, deadline));
    let original = owner(10 * units, 2 * bytes, deadline);
    let calls = Cell::new(0);
    for _ in 0..2 {
        assert!(matches!(
            owned_walk(&original, &executor, &proof, &scope, &calls),
            Ok(Ok(_))
        ));
    }
    assert_eq!(
        owned_walk(&original, &executor, &proof, &scope, &calls),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(
        original.check(),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn one_short_original_work_refuses_and_clone_cannot_renew() {
    let deadline = end();
    let (executor, proof, scope) = fixture();
    let (units, bytes) = totals(&native_offers(&executor, &proof, &scope, deadline));
    assert!(units > 0);
    let original = owner(units - 1, bytes, deadline);
    let calls = Cell::new(0);
    assert_eq!(
        owned_walk(&original, &executor, &proof, &scope, &calls),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert!(calls.get() > 1);
    assert_eq!(
        original.clone().check(),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn one_short_original_copy_refuses_and_clone_cannot_renew() {
    let deadline = end();
    let (executor, proof, scope) = fixture();
    let (units, bytes) = totals(&native_offers(&executor, &proof, &scope, deadline));
    assert!(bytes > 0);
    let original = owner(units, bytes - 1, deadline);
    let calls = Cell::new(0);
    assert_eq!(
        owned_walk(&original, &executor, &proof, &scope, &calls),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert!(calls.get() > 1);
    assert_eq!(
        original.clone().check(),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn original_callback_reset_cannot_restart_an_observed_walk() {
    let deadline = end();
    let (executor, proof, scope) = fixture();
    let (units, bytes) = totals(&native_offers(&executor, &proof, &scope, deadline));
    let stopped = Arc::new(AtomicBool::new(false));
    let observed = stopped.clone();
    let original = OriginalAdmission::new(
        FiniteAdmissionGrant::new(10 * units, 10 * bytes),
        deadline,
        Arc::new(move || observed.load(Ordering::Acquire)),
    );
    let outcome = original.with_work(|work| {
        let calls = Cell::new(0);
        let outcome = check_with_caller_progress(
            &executor,
            walk(&proof, &scope),
            &|| false,
            &mut |units, bytes| {
                calls.set(calls.get() + 1);
                if calls.get() == 3 {
                    stopped.store(true, Ordering::Release);
                }
                work.admit(units, bytes).is_ok()
            },
        )
        .0;
        assert_eq!(outcome, Err(ProofCheckError::ResourceLimit));
        Err::<(), _>(work.refuse_exhaustion())
    });
    assert_eq!(outcome, Err(OriginalAdmissionError::ObserverStopped));
    stopped.store(false, Ordering::Release);
    let calls = Cell::new(0);
    assert_eq!(
        owned_walk(&original, &executor, &proof, &scope, &calls),
        Err(OriginalAdmissionError::ObserverStopped)
    );
    assert_eq!(calls.get(), 0);
}

#[test]
fn original_deadline_refuses_even_with_unlimited_executor_controls() {
    let (mut executor, proof, scope) = fixture();
    executor.set_solve_controls(None, None);
    let original = owner(1_000_000, 1_000_000, Instant::now());
    let calls = Cell::new(0);
    assert_eq!(
        owned_walk(&original, &executor, &proof, &scope, &calls),
        Err(OriginalAdmissionError::Query(QueryError::Interrupted(
            ay_core::original_query::StopReason::Deadline
        )))
    );
    assert_eq!(calls.get(), 0);
}

#[test]
fn local_meter_refusal_is_latched_in_the_same_original_before_retry() {
    let deadline = end();
    let (executor, proof, scope) = fixture();
    let original = owner(1_000_000, 1_000_000, deadline);
    let calls = Cell::new(0);
    let outcome = original.with_work(|work| {
        let outcome = run_with_meter(
            &executor,
            walk(&proof, &scope),
            &|| false,
            &mut |units, bytes| {
                calls.set(calls.get() + 1);
                work.admit(units, bytes).is_ok()
            },
            StrictCheckMeter::with_limits(0, usize::MAX),
        )
        .0;
        assert_eq!(outcome, Err(ProofCheckError::ResourceLimit));
        Err::<(), _>(work.refuse_exhaustion())
    });
    assert_eq!(
        outcome,
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert_eq!(
        calls.get(),
        1,
        "the rejected local offer never reaches the owner"
    );
    assert_eq!(
        original.clone().check(),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}
