// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Original caller boundaries, independent of a race's participant flags.

use ay_core::time::Instant;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use super::{
    definitive, CancellationToken, LadderMember, LadderOutcome, PortfolioResult, RaceState,
    ValidationEvidence,
};

pub(super) fn refused_outcome() -> LadderOutcome {
    (
        PortfolioResult::Unknown,
        ValidationEvidence::FullVerification,
    )
}

/// Spawned members inherit none of these thread-local boundaries.
#[derive(Clone, Copy)]
pub(super) struct InheritedBoundaries {
    pub(super) solve_deadline: Option<Instant>,
    pub(super) smt_deadline: Option<Instant>,
    pub(super) term_memory_budget: Option<usize>,
}

impl InheritedBoundaries {
    fn capture(enclosing_deadline: Option<Instant>) -> Self {
        Self {
            solve_deadline: [
                enclosing_deadline,
                crate::smt::current_thread_solve_deadline(),
            ]
            .into_iter()
            .flatten()
            .min(),
            smt_deadline: crate::smt::deadline::current_smt_deadline(),
            term_memory_budget: crate::smt::SmtContext::current_thread_term_memory_budget(),
        }
    }

    pub(super) fn open(&self, token: &CancellationToken) -> bool {
        let now = Instant::now();
        !token.is_cancelled()
            && !self.solve_deadline.is_some_and(|deadline| now >= deadline)
            && !self.smt_deadline.is_some_and(|deadline| now >= deadline)
    }
}

pub(super) struct CallerAdmission {
    pub(super) boundaries: InheritedBoundaries,
    cancellation: CancellationToken,
    memory: Option<ay_sys::MemoryGroupObservation>,
    interrupt: Option<Arc<AtomicBool>>,
    interrupt_seen: AtomicBool,
}

impl CallerAdmission {
    pub(super) fn capture(solve: &CancellationToken, enclosing_deadline: Option<Instant>) -> Self {
        let mut cancellation = solve.child();
        if let Some(lane) = crate::smt::deadline::current_lane_token() {
            cancellation.link_upstream(&lane);
        }
        // Link every owner before sharing one attempt-local refusal latch.
        let cancellation = cancellation.sticky_child();
        let interrupt = crate::smt::deadline::lane_interrupt_flag();
        let interrupt_seen = interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed));
        Self {
            boundaries: InheritedBoundaries::capture(enclosing_deadline),
            cancellation,
            memory: ay_sys::current_memory_group_observation(),
            interrupt,
            interrupt_seen: AtomicBool::new(interrupt_seen),
        }
    }

    pub(super) fn participant_token(&self) -> CancellationToken {
        self.cancellation.child()
    }

    fn interrupt_open(&self) -> bool {
        if self.interrupt_seen.load(Ordering::Relaxed)
            || self
                .interrupt
                .as_ref()
                .is_some_and(|flag| flag.load(Ordering::Relaxed))
        {
            // Only this attempt-local observation is written. The original
            // caller flag is read-only and a child winner cannot clear it.
            self.interrupt_seen.store(true, Ordering::Relaxed);
            false
        } else {
            true
        }
    }

    pub(super) fn open(&self) -> bool {
        self.interrupt_open()
            && self.boundaries.open(&self.cancellation)
            && !self
                .memory
                .as_ref()
                .is_some_and(|memory| memory.is_tripped())
            && !ay_sys::current_memory_group_soft_tripped()
    }

    pub(super) fn participant_open(&self, token: &CancellationToken) -> bool {
        self.boundaries.open(token) && self.open()
    }

    pub(super) fn limit(&self, outcome: LadderOutcome) -> LadderOutcome {
        if definitive(&outcome.0) && !self.open() {
            refused_outcome()
        } else {
            outcome
        }
    }
}

/// Preserve healthy serial order, but never enter another callback once its
/// original owner boundaries or participant token are known to be closed.
pub(super) fn run_serial(
    state: &RaceState,
    members: Vec<LadderMember<'_>>,
    foreground: impl FnOnce() -> LadderOutcome,
) -> LadderOutcome {
    for (index, member) in members.into_iter().enumerate() {
        let token = &state.tokens[index];
        if !state.caller.participant_open(token) {
            return refused_outcome();
        }
        let outcome = (member.run)();
        if !state.caller.participant_open(token) {
            return refused_outcome();
        }
        if let Some(outcome) = outcome {
            if definitive(&outcome.0) {
                return state.caller.limit(outcome);
            }
        }
    }
    let token = state.foreground_token();
    if !state.caller.participant_open(token) {
        return refused_outcome();
    }
    let outcome = foreground();
    if !state.caller.participant_open(token) {
        return refused_outcome();
    }
    state.caller.limit(outcome)
}
