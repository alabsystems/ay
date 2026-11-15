// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::atomic::AtomicUsize;

#[test]
fn explicit_original_observer_is_never_polled_after_the_final_checker_offer() {
    let deadline = end();
    let (executor, proof, scope) = fixture();
    let total = native_offers(&executor, &proof, &scope, deadline).len();
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = calls.clone();
    let stopped = Arc::new(AtomicBool::new(false));
    let flag = stopped.clone();
    let callback: ay_core::resource::CheckStop = Arc::new(move || {
        observed.fetch_add(1, Ordering::SeqCst);
        flag.load(Ordering::SeqCst)
    });
    let _scope = ay_core::resource::enter_check_stop(callback.clone());
    let offers = Cell::new(0);
    let outcome =
        check_with_caller_progress(&executor, walk(&proof, &scope), &|| false, &mut |_, _| {
            offers.set(offers.get() + 1);
            if offers.get() == total {
                stopped.store(true, Ordering::SeqCst);
            }
            true
        });
    assert!(outcome.0.is_ok());
    assert_eq!(offers.get(), total);
    assert_eq!(calls.load(Ordering::SeqCst), total);
    assert!(stopped.load(Ordering::SeqCst));
    assert!(executor.certification_stop.get().is_none());
    assert!(Arc::ptr_eq(
        &ay_core::resource::current_check_stop().unwrap().unwrap(),
        &callback
    ));
}

#[test]
fn explicit_original_refusal_at_every_offer_is_sticky_and_precedes_work() {
    let (executor, proof, scope) = fixture();
    let total = native_offers(&executor, &proof, &scope, end()).len();
    for stop in 1..=total {
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = calls.clone();
        let _original = ay_core::resource::enter_check_stop(Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst) + 1 == stop
        }));
        let offers = Cell::new(0);
        let outcome =
            check_with_caller_progress(&executor, walk(&proof, &scope), &|| false, &mut |_, _| {
                offers.set(offers.get() + 1);
                true
            });
        assert_eq!(outcome.0, Err(ProofCheckError::Cancelled), "stop={stop}");
        assert_eq!(calls.load(Ordering::SeqCst), stop);
        assert_eq!(offers.get(), stop - 1);
    }
}
