// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn completed_borrowed_fact_has_no_trailing_original_poll() {
    let deadline = end();
    let (executor, proof, scope) = fixture();
    let total = native_offers(&executor, &proof, &scope, deadline).len();
    let calls = Cell::new(0);
    let stop = Cell::new(false);
    let outcome = check_with_caller_progress(
        &executor,
        walk(&proof, &scope),
        &|| Instant::now() >= deadline,
        &mut |_, _| {
            if stop.get() {
                return false;
            }
            calls.set(calls.get() + 1);
            if calls.get() == total {
                stop.set(true);
            }
            true
        },
    );
    assert!(outcome.0.is_ok());
    assert_eq!(calls.get(), total);
    assert!(
        stop.get(),
        "the new stop is pending, not retroactive invalidity"
    );
}

#[test]
fn original_scope_final_fence_refuses_without_reclassifying_completed_fact() {
    let deadline = end();
    let (executor, proof, scope) = fixture();
    let expected = native_offers(&executor, &proof, &scope, deadline);
    let total = expected.len();
    let (units, bytes) = totals(&expected);
    let stopped = Arc::new(AtomicBool::new(false));
    let observed = stopped.clone();
    let original = OriginalAdmission::new(
        FiniteAdmissionGrant::new(units, bytes),
        deadline,
        Arc::new(move || observed.load(Ordering::Acquire)),
    );
    let completed = Cell::new(false);
    let outcome = original.with_work(|work| {
        let calls = Cell::new(0);
        let outcome = check_with_caller_progress(
            &executor,
            walk(&proof, &scope),
            &|| false,
            &mut |units, bytes| {
                let admitted = work.admit(units, bytes).is_ok();
                calls.set(calls.get() + 1);
                if calls.get() == total {
                    stopped.store(true, Ordering::Release);
                }
                admitted
            },
        )
        .0;
        assert!(outcome.is_ok());
        completed.set(true);
        // Checker scratch is already disposed. This UNIT cannot be a proof
        // capability, model, or export; only the later owning fence refuses.
        drop(outcome);
        Ok(())
    });
    assert!(
        completed.get(),
        "the immutable document fact really completed"
    );
    assert_eq!(outcome, Err(OriginalAdmissionError::ObserverStopped));
    assert_eq!(
        original.check(),
        Err(OriginalAdmissionError::ObserverStopped)
    );
}
