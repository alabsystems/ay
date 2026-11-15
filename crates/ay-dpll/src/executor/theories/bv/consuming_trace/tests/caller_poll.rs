// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The trace caller is polled at every strict-checker offer of the walks it
//! encloses. Without an original of its own it is entered with a witness,
//! the three flags that are its whole answer, so those walks read the flags
//! instead of calling it; with an original it is opaque and called.

use super::*;
use ay_core::resource::current_check_stop_and_witness;

/// Behaviour-preservation pin (it passes on the code before the `Ok(None)`
/// shortcut too): without an original, every stop the caller read before is
/// still read at once, and stays read.
#[test]
fn a_caller_without_an_original_still_reads_every_stop_at_once() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let mut executor = Executor::new();
    executor.set_solve_controls(Some(Arc::clone(&interrupt)), None);
    let caller = TraceCaller::capture(&executor);
    assert!(matches!(caller.state.original, Ok(None)));
    for poll in 0..3 {
        assert!(!caller.stopped(), "healthy poll {poll}");
    }
    interrupt.store(true, Ordering::SeqCst);
    assert!(caller.stopped());
    assert_eq!(
        caller.state.attempt.stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
    interrupt.store(false, Ordering::SeqCst);
    assert!(caller.stopped(), "the recorded stop is sticky");

    let quiet = Executor::new();
    let caller = TraceCaller::capture(&quiet);
    assert!(!caller.stopped());
    quiet.record_evaluation_stop(UnknownOrigin::MemoryBudget);
    assert!(caller.stopped(), "a stop another owner recorded");
}

/// Without an original the caller is entered with its witness, and the
/// witness is quiet exactly when the callback answers "no stop": healthy,
/// the interrupt raised, the stop it recorded kept after the interrupt is
/// lowered, and a stop another owner recorded on the attempt.
#[test]
fn a_caller_without_an_original_is_entered_with_a_witness_that_answers_as_it_does() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let mut executor = Executor::new();
    executor.set_solve_controls(Some(Arc::clone(&interrupt)), None);
    let caller = TraceCaller::capture(&executor);
    {
        let _scope = caller.enter();
        let (stop, witness) = current_check_stop_and_witness();
        let stop = stop.expect("captured").expect("entered");
        assert!(Arc::ptr_eq(&stop, &caller.callback));
        let witness = witness.expect("no original: entered with its witness");
        assert!(witness.quiet());
        assert!(!stop());
        interrupt.store(true, Ordering::SeqCst);
        assert!(!witness.quiet());
        assert!(stop());
        interrupt.store(false, Ordering::SeqCst);
        assert!(
            !witness.quiet(),
            "the recorded stop raised the attempt's flag"
        );
        assert!(stop());
    }

    // Captured outside that scope: a caller captured inside it would hold
    // the first as its original, and be opaque.
    let quiet = Executor::new();
    let caller = TraceCaller::capture(&quiet);
    let _scope = caller.enter();
    let witness = current_check_stop_and_witness().1.expect("witnessed");
    assert!(witness.quiet());
    assert!(!(caller.callback)());
    quiet.record_evaluation_stop(UnknownOrigin::MemoryBudget);
    assert!(!witness.quiet());
    assert!((caller.callback)());
}

/// The negative twin: with an original callback the caller is entered
/// opaque, and its poll still marks its invocation around the original, so
/// a poll reentered from inside it refuses.
#[test]
fn a_caller_with_an_original_is_opaque_and_refuses_a_reentered_poll() {
    let executor = Executor::new();
    let slot: Arc<std::sync::Mutex<Option<CheckStop>>> = Arc::default();
    let nested = Arc::clone(&slot);
    let _original = ay_core::resource::enter_check_stop(Arc::new(move || {
        let stop = nested.lock().ok().and_then(|stop| stop.clone());
        stop.is_some_and(|stop| {
            assert!(stop(), "the reentered poll refuses");
            false
        })
    }));
    let caller = TraceCaller::capture(&executor);
    {
        let _scope = caller.enter();
        let (stop, witness) = current_check_stop_and_witness();
        assert!(Arc::ptr_eq(&stop.unwrap().unwrap(), &caller.callback));
        assert!(witness.is_none(), "an original makes the caller opaque");
    }
    assert!(!caller.stopped(), "no reentry yet");
    *slot.lock().expect("slot") = Some(Arc::clone(&caller.callback));
    assert!(caller.stopped(), "the outer poll reports the refusal");
    assert_eq!(
        caller.state.attempt.stop_origin(),
        Some(UnknownOrigin::IncompleteSolverLane)
    );
    *slot.lock().expect("slot") = None;
}
