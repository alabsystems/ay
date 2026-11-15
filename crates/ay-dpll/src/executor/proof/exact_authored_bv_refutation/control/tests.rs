// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The continuation reads its outer stops whole at every poll of its exact
//! phase, then when something it watches changes and once per stride: a
//! stop raised after the exact phase is still read at the next poll, with
//! the reason a whole read gives it, and "no stop" is answered only where a
//! whole read answers it too.

use super::*;
use ay_core::resource::{
    enter_witnessed_check_stop, CheckStopScope, ChildSpec, DeadlineSource, LiveDeadline, NodeLabel,
};
use ay_core::time::Instant;
use std::sync::atomic::AtomicUsize;
use std::time::Duration;

/// Poll a healthy continuation through its exact phase and the first
/// strided whole read after it: the next poll reads whole only if its watch
/// is disturbed.
fn warm(continuation: &Continuation) {
    for at in 0..=HotStride::EXACT {
        assert!(!continuation.stopped(), "healthy poll {at}");
    }
    assert!(!continuation.state.hot.stride.exact());
}

/// An executor with an interrupt, inside a `CancelOnly` Certify node under a
/// Check node (the strict walk's shape), and a second Certify node as the
/// proof assembly's.
struct Fixture {
    interrupt: Arc<AtomicBool>,
    executor: Executor,
    check: Guard,
    assembly: Guard,
    _inside: ay_core::resource::EnterScope,
}

fn fixture() -> Fixture {
    fixture_with(ChildSpec::new(NodeLabel::Check))
}

fn fixture_with(check: ChildSpec) -> Fixture {
    let interrupt = Arc::new(AtomicBool::new(false));
    let mut executor = Executor::new();
    executor.set_solve_controls(Some(Arc::clone(&interrupt)), None);
    let check = Guard::root_child(check);
    let certify = check.child(
        ChildSpec::new(NodeLabel::Certify)
            .cancel_only()
            .with_external(Arc::clone(&interrupt)),
    );
    let assembly = check.child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    executor.assembly_certify = assembly.downgrade();
    let inside = certify.enter();
    Fixture {
        interrupt,
        executor,
        check,
        assembly,
        _inside: inside,
    }
}

#[test]
fn a_stop_raised_after_the_exact_phase_refuses_at_the_next_poll_with_its_reason() {
    let raises: [(&str, fn(&Fixture), EnvelopeStop); 4] = [
        (
            "interrupt",
            |at| at.interrupt.store(true, Ordering::Relaxed),
            EnvelopeStop::Interrupt,
        ),
        (
            "guard chain",
            |at| at.check.cancel(),
            EnvelopeStop::Interrupt,
        ),
        ("assembly", |at| at.assembly.cancel(), EnvelopeStop::Caller),
        (
            "moved certification deadline",
            |at| {
                at.executor.certification_deadline.set(Some(Instant::now()));
            },
            EnvelopeStop::Backstop,
        ),
    ];
    for (what, raise, reason) in raises {
        let at = fixture();
        let continuation = Continuation::capture(&at.executor);
        warm(&continuation);
        raise(&at);
        assert!(continuation.stopped(), "{what}: refused at the next poll");
        assert_eq!(continuation.reason(), Some(reason), "{what}");
        assert!(at.executor.evaluation_stop_origin().is_some(), "{what}");
        assert!(continuation.stopped(), "{what}: a refusal is final");
    }
}

/// The negative twin of the quiet answer: past the exact phase a healthy
/// continuation keeps answering "no stop", and a change that a whole read
/// finds to be no stop of this continuation (the search wall's deadline
/// latched on the Check node, which its `CancelOnly` nodes do not obey) is
/// read whole and refuses nothing.
#[test]
fn a_quiet_continuation_answers_no_stop_only_where_a_whole_read_does() {
    let passed = DeadlineSource::Fixed(Instant::now());
    let at = fixture_with(ChildSpec::new(NodeLabel::Check).with_deadline(passed));
    let continuation = Continuation::capture(&at.executor);
    warm(&continuation);
    for poll in 0..HotStride::STRIDE * 4 {
        assert!(!continuation.stopped(), "quiet poll {poll}");
    }
    assert_eq!(at.check.exhausted(), Some(Exhausted::Deadline), "latches");
    assert!(continuation.state.hot.watch.disturbed());
    assert_eq!(continuation.state.read_outer_stop(), None);
    for poll in 0..HotStride::STRIDE * 2 {
        assert!(!continuation.stopped(), "still healthy {poll}");
    }
    assert_eq!(continuation.reason(), None);
    assert_eq!(at.executor.evaluation_stop_origin(), None);
}

/// What only the clock reveals: a deadline of the walk's node that passes
/// once the exact phase is over refuses within one stride, never later.
#[test]
fn a_deadline_the_clock_passes_refuses_within_a_stride() {
    let deadline = Instant::now() + Duration::from_millis(500);
    let executor = Executor::new();
    let check = Guard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Fixed(deadline)),
    );
    let _inside = check.enter();
    let continuation = Continuation::capture(&executor);
    for _ in 0..HotStride::EXACT {
        if continuation.stopped() {
            // A host too slow to warm in 500 ms: the exact phase read it.
            assert!(Instant::now() >= deadline);
            assert_eq!(continuation.reason(), Some(EnvelopeStop::Backstop));
            return;
        }
    }
    while Instant::now() < deadline {
        std::thread::sleep(Duration::from_millis(1));
    }
    let seen = (1..=HotStride::STRIDE).find(|_| continuation.stopped());
    assert!(seen.is_some(), "read within one stride");
    assert_eq!(continuation.reason(), Some(EnvelopeStop::Backstop));
}

/// What `HotWatch` of the guard alone does not see: the executor's interrupt
/// with no current guard (and an assembly node that does not share it), a
/// flag of the assembly node's own chain, and a deadline share opened on the
/// certification cell (which moves its generation without a
/// `LiveDeadline::set`). Each, raised after the exact phase, refuses at the
/// next poll with the reason a whole read gives it.
#[test]
fn what_the_guard_does_not_carry_still_refuses_at_the_next_poll() {
    type Raise = fn(
        &Executor,
        &Arc<AtomicBool>,
        &Arc<AtomicBool>,
    ) -> Option<crate::executor::solve_deadline::OpenShare>;
    let raises: [(&str, Raise, EnvelopeStop); 3] = [
        (
            "interrupt without a guard",
            |_, interrupt, _| {
                interrupt.store(true, Ordering::Relaxed);
                None
            },
            EnvelopeStop::Interrupt,
        ),
        (
            "assembly chain flag",
            |_, _, assembly_flag| {
                assembly_flag.store(true, Ordering::Relaxed);
                None
            },
            EnvelopeStop::Caller,
        ),
        (
            "share opened on the certification cell",
            |executor, _, _| {
                Some(
                    executor
                        .certification_deadline
                        .open_share(LiveDeadline::new(Some(Instant::now()))),
                )
            },
            EnvelopeStop::Backstop,
        ),
    ];
    let mut seen = Vec::new();
    for (what, raise, reason) in raises {
        let interrupt = Arc::new(AtomicBool::new(false));
        let assembly_flag = Arc::new(AtomicBool::new(false));
        let mut executor = Executor::new();
        executor.set_solve_controls(Some(Arc::clone(&interrupt)), None);
        let assembly = Guard::root_child(
            ChildSpec::new(NodeLabel::Certify)
                .cancel_only()
                .with_external(Arc::clone(&assembly_flag)),
        );
        executor.assembly_certify = assembly.downgrade();
        let continuation = Continuation::capture(&executor);
        assert!(continuation.state.guard.is_none(), "{what}: no guard");
        warm(&continuation);
        let _share = raise(&executor, &interrupt, &assembly_flag);
        let refused = continuation.stopped();
        seen.push((what, refused, continuation.reason(), Some(reason)));
    }
    for (what, refused, got, want) in seen.iter().copied() {
        assert!(
            refused && got == want,
            "{what}: refused at the next poll as {want:?}: {seen:?}"
        );
    }
}

/// An opaque original's invocation is marked: a poll reentered from inside
/// it on the polling thread refuses as `Caller`, and the outer poll reports
/// that refusal.
#[test]
fn a_poll_reentered_from_the_original_refuses_as_caller() {
    let executor = Executor::new();
    let slot: Arc<Mutex<Option<CheckStop>>> = Arc::default();
    let nested = Arc::clone(&slot);
    let _original = enter_check_stop(Arc::new(move || {
        let stop = nested.lock().ok().and_then(|stop| stop.clone());
        stop.is_some_and(|stop| {
            assert!(stop(), "the reentered poll refuses");
            false
        })
    }));
    let continuation = Continuation::capture(&executor);
    assert!(!continuation.stopped(), "no reentry yet");
    *slot.lock().expect("slot") = Some(Arc::clone(&continuation.stop));
    assert!(continuation.stopped(), "the outer poll reports the refusal");
    assert_eq!(continuation.reason(), Some(EnvelopeStop::Caller));
    *slot.lock().expect("slot") = None;
}

/// A counting original over a fresh flag, entered with that flag as its
/// witness or opaque, and the continuation captured inside it.
fn counted(
    witnessed: bool,
) -> (
    CheckStopScope,
    Arc<AtomicBool>,
    Arc<AtomicUsize>,
    Continuation,
) {
    let flag = Arc::new(AtomicBool::new(false));
    let calls = Arc::new(AtomicUsize::new(0));
    let (read, count) = (Arc::clone(&flag), Arc::clone(&calls));
    let original: CheckStop = Arc::new(move || {
        count.fetch_add(1, Ordering::SeqCst);
        read.load(Ordering::SeqCst)
    });
    let scope = if witnessed {
        enter_witnessed_check_stop(original, CheckStopWitness::new([Arc::clone(&flag)]))
    } else {
        enter_check_stop(original)
    };
    let continuation = Continuation::capture(&Executor::new());
    assert_eq!(continuation.state.witness.is_some(), witnessed);
    (scope, flag, calls, continuation)
}

/// A witnessed original is called at every poll of the exact phase, then
/// answered by its witness; a flag of the witness raised after the exact
/// phase is read at the next poll, which calls it and refuses as `Caller`.
#[test]
fn a_witnessed_original_refuses_at_the_poll_after_its_flag_is_raised() {
    let (_scope, flag, calls, continuation) = counted(true);
    warm(&continuation);
    let warmed = calls.load(Ordering::SeqCst);
    assert_eq!(
        warmed,
        HotStride::EXACT as usize + 1,
        "every due poll calls it"
    );
    flag.store(true, Ordering::SeqCst);
    assert!(continuation.stopped(), "refused at the next poll");
    assert_eq!(continuation.reason(), Some(EnvelopeStop::Caller));
    assert_eq!(calls.load(Ordering::SeqCst), warmed + 1, "called there");
    flag.store(false, Ordering::SeqCst);
    assert!(continuation.stopped(), "a refusal is final");
}

/// The negative twin: an opaque original is called at every poll, quiet
/// or not, and its refusal is read at the poll that makes it.
#[test]
fn an_opaque_original_is_called_at_every_poll() {
    let (_scope, flag, calls, continuation) = counted(false);
    warm(&continuation);
    let polls = HotStride::STRIDE as usize * 4;
    for poll in 0..polls {
        assert!(!continuation.stopped(), "quiet poll {poll}");
    }
    let warmed = HotStride::EXACT as usize + 1;
    assert_eq!(calls.load(Ordering::SeqCst), warmed + polls);
    flag.store(true, Ordering::SeqCst);
    assert!(continuation.stopped());
    assert_eq!(continuation.reason(), Some(EnvelopeStop::Caller));
    assert_eq!(calls.load(Ordering::SeqCst), warmed + polls + 1);
}
