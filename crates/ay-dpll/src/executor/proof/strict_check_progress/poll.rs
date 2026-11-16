// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bound OS memory polling cost without delaying interrupt/deadline callbacks.

use std::cell::Cell;
use std::sync::atomic::Ordering;

use crate::api::proofs::EnvelopeStop;
use ay_core::resource::{
    current_check_stop_and_witness, current_guard, CheckStop, CheckStopCaptureError,
    CheckStopWitness, Exhausted, Guard, GuardPoll,
};

use super::STOP_POLL_INTERVAL;
use crate::executor::solve_deadline::DeadlinePoll;
use crate::executor::Executor;

impl Executor {
    /// `make_should_stop`'s three signals (interrupt, solve deadline, the
    /// portfolio lane's memory share), for a strict walk that polls them at
    /// every callback: the deadline is read through a [`DeadlinePoll`], so a
    /// long walk reads a flag a timer raises instead of a lock and the clock
    /// (DR-34).
    pub(in crate::executor) fn make_strict_check_stop(&self) -> impl Fn() -> bool {
        let interrupt = self.solve_interrupt.clone();
        let deadline = DeadlinePoll::new(self.solve_deadline.clone());
        move || {
            interrupt
                .as_ref()
                .is_some_and(|flag| flag.load(Ordering::Relaxed))
                || deadline.expired()
                || ay_sys::current_memory_group_soft_tripped()
        }
    }
}

/// Capture the explicit caller and the actual walk's node, not a search node
/// when a stop closure was lifted out before entering Certify. No scope or
/// allowance is replaced. The captured callback remains the exact original Arc.
pub(super) fn strided_memory_poll(
    should_stop: &impl Fn() -> bool,
    memory_limit: Option<usize>,
) -> StopPoll<&impl Fn() -> bool, impl Fn() -> bool> {
    sampled_poll(should_stop, move || {
        crate::memory::memory_exceeded(memory_limit) || ay_sys::process_memory_exceeded()
    })
}

#[derive(Clone, Copy)]
enum Cause {
    Envelope(EnvelopeStop),
    /// The supplied executor/test control stopped; classify its live executor
    /// signal once, or conservatively keep Caller if that signal already reset.
    LocalControl,
}

/// One walk's irreversible observation, independent of the lifetime of a live
/// flag. All fields are call-local; no captured source is written or replenished.
/// The actual walk's node is read through a [`GuardPoll`]: every flag, latch,
/// count and moved deadline at every callback, what only the clock reveals
/// at every callback of a short walk and once per stride of a long one. An
/// original entered with a witness is read through it at every callback.
pub(super) struct StopPoll<S, M> {
    should_stop: S,
    memory_stopped: M,
    guard: Option<GuardPoll>,
    original: Result<Option<CheckStop>, CheckStopCaptureError>,
    witness: Option<CheckStopWitness>,
    callbacks: Cell<u64>,
    refused: Cell<Option<Cause>>,
    reentered: Cell<bool>,
}

impl<S: Fn() -> bool, M: Fn() -> bool> StopPoll<S, M> {
    pub(super) fn reason(&self) -> Option<EnvelopeStop> {
        match self.refused.get() {
            Some(Cause::Envelope(reason)) => Some(reason),
            Some(Cause::LocalControl) | None => None,
        }
    }

    pub(super) fn poll(&self) -> bool {
        if self.refused.get().is_some() {
            // A nested observation has returned refusal to its caller. Even
            // if the outer callback returns false, that fact is irreversible.
            self.reentered.set(true);
            return true;
        }
        let callbacks = self.callbacks.get().wrapping_add(1);
        self.callbacks.set(callbacks);
        if let Some(reason) = self.guard.as_ref().and_then(GuardPoll::poll) {
            self.refused.set(Some(Cause::Envelope(tree_reason(reason))));
            return true;
        }
        // A guard's poll reads the process cancel itself, first, and answers
        // it as `Cancelled`: the same `Interrupt`.
        if self.guard.is_none() && ay_core::resource::process_cancelled() {
            self.refused
                .set(Some(Cause::Envelope(EnvelopeStop::Interrupt)));
            return true;
        }
        // An original whose witness is quiet answers "no stop" and changes
        // nothing: it is answered by the witness, and no caller code runs.
        // Every other original is called at every callback.
        if !self.witness.as_ref().is_some_and(CheckStopWitness::quiet) {
            // Arm before arbitrary caller code: unwind/reentry cannot revive
            // this attempt. Capture failure is also an opaque caller refusal,
            // not absence.
            self.refused
                .set(Some(Cause::Envelope(EnvelopeStop::Caller)));
            match &self.original {
                Err(_) => return true,
                Ok(Some(stop)) if stop() => return true,
                _ => {}
            }
            if self.reentered.get() {
                return true;
            }
        }
        self.refused.set(Some(Cause::LocalControl));
        if (self.should_stop)() || self.reentered.get() {
            return true;
        }
        // Preserve sampled OS memory work. The cause is captured by THIS read,
        // never inferred by re-reading a flag or callback after it has reset.
        if (callbacks == 1 || callbacks.is_multiple_of(STOP_POLL_INTERVAL))
            && (self.memory_stopped)()
        {
            self.refused
                .set(Some(Cause::Envelope(EnvelopeStop::ProcessMemory)));
            return true;
        }
        if self.reentered.get() {
            return true;
        }
        self.refused.set(None);
        false
    }
}

fn tree_reason(reason: Exhausted) -> EnvelopeStop {
    match reason {
        Exhausted::Cancelled => EnvelopeStop::Interrupt,
        Exhausted::Deadline | Exhausted::Cpu => EnvelopeStop::Backstop,
        Exhausted::Rlimit => EnvelopeStop::WorkLimit,
        Exhausted::Memory => EnvelopeStop::LaneShare,
    }
}

// Memory is observed at admission and every STOP_POLL_INTERVAL callbacks.
// No observer runs after the checker's final callback: a completed document
// fact remains accepted; later publication/cleanup belongs to its outer owner.
fn sampled_poll<S: Fn() -> bool, M: Fn() -> bool>(
    should_stop: S,
    memory_stopped: M,
) -> StopPoll<S, M> {
    let (original, witness) = current_check_stop_and_witness();
    StopPoll {
        should_stop,
        memory_stopped,
        guard: current_guard().as_ref().map(Guard::hot_poll),
        original,
        witness,
        callbacks: Cell::new(0),
        refused: Cell::new(None),
        reentered: Cell::new(false),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn memory_is_observed_at_entry_and_within_one_bounded_interval() {
        let observations = Cell::new(0);
        let breach = Cell::new(false);
        let poll = sampled_poll(
            || false,
            || {
                observations.set(observations.get() + 1);
                breach.get()
            },
        );
        assert!(!poll.poll());
        assert_eq!(observations.get(), 1);
        breach.set(true);
        for _ in 2..STOP_POLL_INTERVAL {
            assert!(!poll.poll());
        }
        assert!(poll.poll());
        assert_eq!(observations.get(), 2);
        breach.set(false);
        assert!(poll.poll(), "observed refusal remains sticky");
    }

    #[test]
    fn cheap_stop_does_not_wait_for_the_memory_interval() {
        let stop = Cell::new(false);
        let poll = sampled_poll(|| stop.get(), || false);
        assert!(!poll.poll());
        stop.set(true);
        assert!(poll.poll());
        stop.set(false);
        assert!(poll.poll());
    }

    #[test]
    fn original_callback_and_guard_survive_scope_drop_and_healthy_replacements() {
        use ay_core::resource::{enter_check_stop, ChildSpec, NodeLabel};
        use std::sync::{atomic::AtomicBool, Arc};
        let flag = Arc::new(AtomicBool::new(false));
        let observed = flag.clone();
        let callback: CheckStop = Arc::new(move || observed.load(Ordering::SeqCst));
        let owner = enter_check_stop(callback.clone());
        let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        let inside = guard.enter();
        let poll = sampled_poll(|| false, || false);
        assert!(Arc::ptr_eq(
            poll.original.as_ref().unwrap().as_ref().unwrap(),
            &callback
        ));
        drop(inside);
        drop(owner);
        let _replacement = enter_check_stop(Arc::new(|| false));
        let healthy = Guard::new();
        let _healthy = healthy.enter();
        flag.store(true, Ordering::SeqCst);
        assert!(poll.poll());
        assert_eq!(poll.reason(), Some(EnvelopeStop::Caller));
        flag.store(false, Ordering::SeqCst);
        assert!(poll.poll(), "the already observed refusal is permanent");
        let original = guard.enter();
        let stopped_guard = sampled_poll(|| false, || false);
        drop(original);
        guard.cancel();
        assert!(stopped_guard.poll());
        assert_eq!(stopped_guard.reason(), Some(EnvelopeStop::Interrupt));
    }

    #[test]
    fn caught_original_callback_unwind_does_not_revive_the_same_poll() {
        use ay_core::resource::enter_check_stop;
        use std::sync::{atomic::AtomicUsize, Arc};
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = calls.clone();
        let _scope = enter_check_stop(Arc::new(move || {
            assert!(
                observed.fetch_add(1, Ordering::SeqCst) != 0,
                "observer fixture"
            );
            false
        }));
        let poll = sampled_poll(|| false, || false);
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| poll.poll())).is_err());
        assert!(poll.poll());
        assert_eq!(poll.reason(), Some(EnvelopeStop::Caller));
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    /// A counting original over `flag`, entered with `flag` as its witness
    /// or opaque, and the walk's poll of it.
    fn counted_original(
        witnessed: bool,
    ) -> (
        ay_core::resource::CheckStopScope,
        std::sync::Arc<std::sync::atomic::AtomicBool>,
        std::sync::Arc<std::sync::atomic::AtomicUsize>,
    ) {
        use ay_core::resource::{enter_check_stop, enter_witnessed_check_stop, CheckStopWitness};
        use std::sync::{atomic::AtomicBool, atomic::AtomicUsize, Arc};
        let flag = Arc::new(AtomicBool::new(false));
        let calls = Arc::new(AtomicUsize::new(0));
        let (read, counted) = (Arc::clone(&flag), Arc::clone(&calls));
        let original: CheckStop = Arc::new(move || {
            counted.fetch_add(1, Ordering::SeqCst);
            read.load(Ordering::SeqCst)
        });
        let scope = if witnessed {
            enter_witnessed_check_stop(original, CheckStopWitness::new([Arc::clone(&flag)]))
        } else {
            enter_check_stop(original)
        };
        (scope, flag, calls)
    }

    /// An original entered with a witness is answered by it while it is
    /// quiet, at every callback, and called at the first callback after one
    /// of its flags is raised: that refusal is the original's, and sticky.
    #[test]
    fn a_witnessed_original_is_read_through_its_witness_and_called_once_raised() {
        let (_scope, flag, calls) = counted_original(true);
        let poll = sampled_poll(|| false, || false);
        for _ in 0..STOP_POLL_INTERVAL * 2 {
            assert!(!poll.poll());
        }
        assert_eq!(calls.load(Ordering::SeqCst), 0, "the quiet witness answers");
        flag.store(true, Ordering::SeqCst);
        assert!(poll.poll(), "read at the next callback");
        assert_eq!(poll.reason(), Some(EnvelopeStop::Caller));
        assert_eq!(calls.load(Ordering::SeqCst), 1, "and called there");
        flag.store(false, Ordering::SeqCst);
        assert!(poll.poll(), "the observed refusal is permanent");
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    /// The negative twin: the same original entered opaque is called at
    /// every callback.
    #[test]
    fn an_opaque_original_is_called_at_every_callback() {
        let (_scope, flag, calls) = counted_original(false);
        let poll = sampled_poll(|| false, || false);
        for _ in 0..STOP_POLL_INTERVAL * 2 {
            assert!(!poll.poll());
        }
        let offers = usize::try_from(STOP_POLL_INTERVAL * 2).expect("small");
        assert_eq!(calls.load(Ordering::SeqCst), offers);
        flag.store(true, Ordering::SeqCst);
        assert!(poll.poll());
        assert_eq!(poll.reason(), Some(EnvelopeStop::Caller));
        assert_eq!(calls.load(Ordering::SeqCst), offers + 1);
    }

    #[test]
    fn reentered_refusal_survives_an_outer_callback_returning_false() {
        use std::cell::RefCell;
        use std::rc::Rc;
        type Reenter = Rc<RefCell<Option<Box<dyn Fn() -> bool>>>>;
        let reenter: Reenter = Rc::new(RefCell::new(None));
        let observed = reenter.clone();
        let calls = Rc::new(Cell::new(0));
        let counted = calls.clone();
        let poll = Rc::new(sampled_poll(
            move || {
                counted.set(counted.get() + 1);
                assert!(observed.borrow().as_ref().unwrap()());
                false
            },
            || false,
        ));
        let weak = Rc::downgrade(&poll);
        *reenter.borrow_mut() = Some(Box::new(move || weak.upgrade().unwrap().poll()));
        assert!(poll.poll());
        assert!(poll.poll(), "the outer false cannot undo nested refusal");
        assert_eq!(calls.get(), 1);
    }
}
