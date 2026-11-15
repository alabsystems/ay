// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One original stop across presentation advice and alternate lemma attempts.
//! Refusal is retained in the enclosing evaluation attempt, not just this
//! helper. No deadline, work allowance or semantic decision is created here.

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use ay_core::resource::{
    current_check_stop_and_witness, current_guard, enter_check_stop, CheckStop,
    CheckStopCaptureError, CheckStopWitness, Exhausted, Guard, HotStride, HotWatch,
};

use crate::api::proofs::EnvelopeStop;
use crate::executor::model::EvaluationAttempt;
use crate::executor::solve_deadline::{DeadlinePoll, SolveDeadlineCell};
use crate::executor::Executor;

pub(in crate::executor::proof) struct Continuation {
    state: Arc<State>,
    stop: CheckStop,
}

struct State {
    original: Result<Option<CheckStop>, CheckStopCaptureError>,
    /// The original's whole answer, when it was entered with one.
    witness: Option<CheckStopWitness>,
    guard: Option<Guard>,
    assembly: Guard,
    interrupt: Option<Arc<AtomicBool>>,
    deadline: Mutex<DeadlinePoll>,
    attempt: EvaluationAttempt,
    refused: OnceLock<EnvelopeStop>,
    polling: AtomicBool,
    hot: Hot,
}

/// The walks a continuation encloses poll it at every strict-checker offer
/// (911 M offers on qb44). What its outer stops read without the clock is
/// watched here with relaxed loads (the guard's and the assembly node's
/// chains, the interrupt and the process cancel, the certification
/// deadline's generation, the polling thread's work ceiling): `outer_stop`
/// reads whole only when that changed, at every poll of its first
/// `HotStride::EXACT`, and once per stride after. A poll that reads nothing
/// whole and whose original is absent or quiet by its witness is the quiet
/// poll: a few loads, nothing marked, nothing called (`State::poll`).
struct Hot {
    watch: HotWatch,
    stride: HotStride,
    /// The cell `deadline` polls, and its generation at the last whole read.
    certification: SolveDeadlineCell,
    seen: AtomicU64,
    /// Raised once `refused` is set.
    refused: AtomicBool,
}

impl Continuation {
    pub(in crate::executor::proof) fn capture(executor: &Executor) -> Self {
        let (original, witness) = current_check_stop_and_witness();
        let guard = current_guard();
        let assembly = executor
            .assembly_certify
            .upgrade()
            .unwrap_or_else(|| executor.proof_assembly_certify_node());
        let interrupt = executor.solve_interrupt.clone();
        let mut watch = HotWatch::new().cancelled_of(&assembly);
        if let Some(guard) = &guard {
            watch = watch.poll_of(guard);
        }
        if let Some(flag) = &interrupt {
            watch = watch.flag(flag);
        }
        let certification = executor.certification_deadline.clone();
        let state = Arc::new(State {
            original,
            witness,
            guard,
            assembly,
            interrupt,
            deadline: Mutex::new(DeadlinePoll::new(certification.clone())),
            attempt: executor.evaluation_attempt(),
            refused: OnceLock::new(),
            polling: AtomicBool::new(false),
            hot: Hot {
                watch,
                stride: HotStride::new(),
                seen: AtomicU64::new(certification.generation()),
                certification,
                refused: AtomicBool::new(false),
            },
        });
        if let Some(reason) = executor.certification_stop() {
            if Self::imports(executor, reason) {
                state.refuse(reason);
            }
        }
        let captured = Arc::clone(&state);
        let stop = Arc::new(move || captured.poll());
        Self { state, stop }
    }

    /// Whether a stop an earlier walk noted (`certification_stop`) refuses
    /// this continuation before it polls anything (#check-sat-assuming-empty-core).
    ///
    /// A noted stop may be one this continuation can no longer observe (a
    /// one-shot caller stop a strict walk consumed), so it is imported. Not a
    /// `Backstop` while the certification envelope is live: that came from a
    /// narrower deadline, a search lane's slice of `solve_deadline` a strict
    /// walk polled or a nested guard, and the continuation re-polls the
    /// deadlines it does obey, the envelope and the guard current at capture.
    /// Proof assembly obeys the envelope, never the search wall
    /// (`build_unsat_assembly/stop.rs`). Imported, the core minimizer's 2 s
    /// slice expiring under a strict walk refused the subset attempt's repair
    /// and, through it, the attempt: its UNSAT lost its core.
    fn imports(executor: &Executor, reason: EnvelopeStop) -> bool {
        reason != EnvelopeStop::Backstop || executor.certification_deadline.expired()
    }

    pub(in crate::executor::proof) fn stopped(&self) -> bool {
        (self.stop)()
    }

    pub(in crate::executor::proof) fn reason(&self) -> Option<EnvelopeStop> {
        self.state.refused.get().copied()
    }

    pub(in crate::executor::proof) fn enter(&self) -> ay_core::resource::CheckStopScope {
        enter_check_stop(Arc::clone(&self.stop))
    }

    pub(in crate::executor::proof) fn refuse(&self, reason: EnvelopeStop) {
        self.state.refuse(reason);
    }
}

impl State {
    fn refuse(&self, reason: EnvelopeStop) -> bool {
        let first = *self.refused.get_or_init(|| reason);
        self.hot.refused.store(true, Ordering::Relaxed);
        self.attempt.record_stop(first.unknown().0);
        true
    }

    /// `refused` is set, or the enclosing attempt recorded a stop.
    #[inline]
    fn stopped(&self) -> bool {
        self.hot.refused.load(Ordering::Relaxed) || self.attempt.is_stopped()
    }

    /// Whether anything [`Self::read_outer_stop`] reads without the clock may
    /// have changed since its last whole read (`Hot`).
    #[inline]
    fn outer_disturbed(&self) -> bool {
        let hot = &self.hot;
        hot.watch.disturbed()
            || hot
                .certification
                .moved_since(hot.seen.load(Ordering::Relaxed))
            || ay_core::resource::work_ceiling_reached()
    }

    /// [`Self::read_outer_stop`]'s answer: read whole when `due` or
    /// disturbed (`Hot`); else "no stop".
    #[inline]
    fn outer_stop(&self, due: bool) -> Option<EnvelopeStop> {
        if due || self.outer_disturbed() {
            return self.outer_stop_whole();
        }
        None
    }

    /// Whether the original answers "no stop" without being called: there is
    /// none, or its witness is quiet. An opaque original is never quiet.
    #[inline]
    fn original_quiet(&self) -> bool {
        match (&self.original, &self.witness) {
            (Ok(None), _) => true,
            (Ok(Some(_)), Some(witness)) => witness.quiet(),
            _ => false,
        }
    }

    #[cold]
    #[inline(never)]
    fn outer_stop_whole(&self) -> Option<EnvelopeStop> {
        let hot = &self.hot;
        hot.seen
            .store(hot.certification.generation(), Ordering::Relaxed);
        hot.watch.note();
        let reason = self.read_outer_stop();
        if reason.is_some() {
            hot.stride.again();
        }
        reason
    }

    fn read_outer_stop(&self) -> Option<EnvelopeStop> {
        if let Some(reason) = self.guard.as_ref().and_then(Guard::poll) {
            return Some(match reason {
                Exhausted::Cancelled => EnvelopeStop::Interrupt,
                Exhausted::Deadline | Exhausted::Cpu => EnvelopeStop::Backstop,
                Exhausted::Rlimit => EnvelopeStop::WorkLimit,
                Exhausted::Memory => EnvelopeStop::LaneShare,
            });
        }
        if ay_core::resource::process_cancelled()
            || self
                .interrupt
                .as_ref()
                .is_some_and(|flag| flag.load(Ordering::Relaxed))
        {
            return Some(EnvelopeStop::Interrupt);
        }
        // DeadlinePoll has thread-local interior counters. Serialize only that
        // internal poll, releasing its lock before any opaque caller callback.
        let expired = match self.deadline.lock() {
            Ok(deadline) => deadline.expired(),
            Err(_) => return Some(EnvelopeStop::Caller),
        };
        if expired {
            return Some(EnvelopeStop::Backstop);
        }
        self.assembly.cancelled().map(|_| EnvelopeStop::Caller)
    }

    fn poll(&self) -> bool {
        if self.stopped() {
            return true;
        }
        let whole = self.hot.stride.due() || self.outer_disturbed();
        // The quiet poll: a whole read would answer "no stop" (bar what only
        // the clock reveals, read once per stride) and so would the original.
        // No code that could reenter this poll or unwind out of it runs, so
        // there is no invocation to mark. An opaque original is called, and
        // its invocation marked, at every poll.
        if !whole && self.original_quiet() {
            return false;
        }
        self.poll_marked(whole)
    }

    fn poll_marked(&self, whole: bool) -> bool {
        if self.polling.swap(true, Ordering::AcqRel) {
            return self.refuse(EnvelopeStop::Caller);
        }
        let _invocation = Invocation(self);
        if whole {
            if let Some(reason) = self.outer_stop_whole() {
                return self.refuse(reason);
            }
        }
        match &self.original {
            Err(_) => return self.refuse(EnvelopeStop::Caller),
            Ok(Some(stop)) if stop() => return self.refuse(EnvelopeStop::Caller),
            _ => {}
        }
        // What the original changed is watched; the exact phase reads whole.
        if let Some(reason) = self.outer_stop(self.hot.stride.exact()) {
            return self.refuse(reason);
        }
        if self.stopped() {
            return true;
        }
        self.polling.store(false, Ordering::Release);
        false
    }
}

/// Arm before arbitrary code. Unwind/reentry is recorded outside any lock or
/// TLS borrow; another repair cannot revive the same enclosing attempt.
struct Invocation<'a>(&'a State);

impl Drop for Invocation<'_> {
    fn drop(&mut self) {
        if self.0.polling.load(Ordering::Acquire) {
            self.0.refuse(EnvelopeStop::Caller);
        }
    }
}

#[cfg(test)]
mod tests;
