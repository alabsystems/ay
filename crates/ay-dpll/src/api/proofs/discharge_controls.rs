// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The deferred-trust discharge's resource envelope (P4a.1).
//!
//! No clock decides inside it. Every nested solve the discharge runs is
//! bounded by a grant from the [`CertificationEffort`], a count, so what it
//! decides is a function of the query. What remains are STOPS: the caller's
//! interrupt, the backstop (the certification deadline on the executor path;
//! none on the proof-export path, where no solve is active), the memory
//! ceilings, and the cancels that reach the certification's node from above
//! (DR-39). Each poll latches the first stop it sees and every later poll
//! reports it, so a stop only ever ends lanes and the funnel reports it as the
//! stop it was ([`TrustClauseDischargeControls::decline_stop`]), never as a
//! rejection, even after the signal has cleared (RSS falls; a nested lane's
//! own stop is not visible from outside).
//!
//! A completed check is a fact (#completed-check-accepted): once a lane has
//! accepted, nothing re-polls the clock or RSS. Only the exact term-store
//! count is re-checked, because it is a count of what the lane built.
//!
//! A nested solve of the guard or of a pool lane also runs under its share's
//! grant of split-loop round trips ([`TrustClauseDischargeControls::in_round_trip_grant`]),
//! because a conflict grant bounds each round's SAT solve but not how many
//! rounds a split loop runs; step (4a)'s question and a closed-sentence
//! refutation run under counts of their own
//! ([`TrustClauseDischargeControls::in_round_trips`]).

use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use ay_core::resource::{DeadlineSource, Exhausted, Guard};

use super::certification_effort::{
    certify_node, CertificationEffort, EffortShare, EnvelopeStop, NestedStop,
};

#[cfg(test)]
thread_local! {
    static ONE_POLL_MEMORY_STOP: Cell<bool> = const { Cell::new(false) };
}

/// Test-only: the next envelope poll on this thread sees a process-memory
/// stop (the real `ay_sys` force, raised for that one poll and lowered
/// again): a stop that lapses before any later poll, as RSS that falls back
/// under its ceiling would.
#[cfg(test)]
pub(crate) fn arm_one_poll_memory_stop_for_testing() {
    ONE_POLL_MEMORY_STOP.with(|armed| armed.set(true));
}

/// Caller-owned resource envelope for the fresh solvers used while
/// discharging deferred-trust clauses, and for the forged-UNSAT guard and the
/// whole-problem re-solve beside them. One per certification.
#[derive(Debug, Default)]
pub(crate) struct TrustClauseDischargeControls {
    pub(crate) interrupt: Option<Arc<AtomicBool>>,
    pub(crate) backstop: Option<ay_core::time::Instant>,
    pub(crate) memory_limit: Option<usize>,
    pub(crate) term_memory_limit: Option<usize>,
    pub(crate) effort: CertificationEffort,
    /// The certification's node (DR-39): every nested solve this envelope
    /// arms runs its checks under it. `None` (a default envelope) leaves a
    /// nested check where it runs.
    certify: Option<Guard>,
    stop: Cell<Option<EnvelopeStop>>,
    lane_clock_spent: Cell<bool>,
}

impl TrustClauseDischargeControls {
    pub(crate) fn new(
        interrupt: Option<Arc<AtomicBool>>,
        backstop: Option<ay_core::time::Instant>,
        memory_limit: Option<usize>,
        term_memory_limit: Option<usize>,
        effort: CertificationEffort,
    ) -> Self {
        let certify = Some(certify_node(
            interrupt.clone(),
            backstop.map_or(DeadlineSource::None, DeadlineSource::Fixed),
        ));
        Self {
            interrupt,
            backstop,
            memory_limit,
            term_memory_limit,
            effort,
            certify,
            ..Self::default()
        }
    }

    /// The certification's node, for a nested executor this envelope does
    /// not arm itself (`Executor::set_certification_parent`).
    pub(crate) fn certify(&self) -> Option<Guard> {
        self.certify.clone()
    }

    /// Whether the envelope has stopped: the latched stop if one was seen,
    /// else a live poll, whose first stop is latched.
    pub(crate) fn stop_requested(&self, terms: &ay_core::TermStore) -> bool {
        if self.stop.get().is_some() {
            return true;
        }
        let observed = self.poll_stop(terms);
        if let Some(stop) = observed {
            self.latch(stop);
        }
        observed.is_some()
    }

    fn poll_stop(&self, terms: &ay_core::TermStore) -> Option<EnvelopeStop> {
        #[cfg(test)]
        if ONE_POLL_MEMORY_STOP.with(|armed| armed.replace(false)) {
            ay_sys::force_process_memory_exceeded_for_testing(true);
            let observed = self.poll_live(terms);
            ay_sys::force_process_memory_exceeded_for_testing(false);
            return observed;
        }
        self.poll_live(terms)
    }

    fn poll_live(&self, terms: &ay_core::TermStore) -> Option<EnvelopeStop> {
        if self
            .interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
        {
            Some(EnvelopeStop::Interrupt)
        } else if self.backstop_passed() {
            Some(EnvelopeStop::Backstop)
        } else if crate::memory::memory_exceeded(self.memory_limit)
            || ay_sys::process_memory_exceeded()
        {
            Some(EnvelopeStop::ProcessMemory)
        } else if ay_sys::current_memory_group_soft_tripped() {
            Some(EnvelopeStop::LaneShare)
        } else if ay_core::TermStore::global_memory_exceeded()
            || self
                .term_memory_limit
                .is_some_and(|limit| terms.instance_memory_exceeded(limit))
        {
            Some(EnvelopeStop::TermMemory)
        } else {
            self.certify_cancelled()
        }
    }

    /// The cancels of the certification's node that the reads above do not
    /// make (DR-39): the flags of the nodes above it (the interrupt of a check
    /// around this one, a node's cancel, the process cancel) and a memory
    /// share's trip. A nested check is a `Full` child of the node, so its
    /// theory loops stop for these too (`check_stop_requested`), and its
    /// `Unknown` names no envelope origin; read here, the stop is latched as
    /// the stop it was, never left to read as a decline. A work cap reached
    /// above the node is a count, not a cancel, and is not read here: the
    /// envelope did not read the thread's caps before S2 either, and the
    /// nested executor's own polls classify it.
    fn certify_cancelled(&self) -> Option<EnvelopeStop> {
        self.certify
            .as_ref()
            .and_then(Guard::cancelled)
            .map(|why| match why {
                Exhausted::Memory => EnvelopeStop::LaneShare,
                _ => EnvelopeStop::Interrupt,
            })
    }

    fn backstop_passed(&self) -> bool {
        self.backstop
            .is_some_and(|backstop| ay_core::time::Instant::now() >= backstop)
    }

    /// Keep `stop` unless an earlier one was already latched.
    pub(crate) fn latch(&self, stop: EnvelopeStop) {
        if self.stop.get().is_none() {
            self.stop.set(Some(stop));
        }
    }

    /// The first stop any poll or nested solve of this envelope saw.
    pub(crate) fn observed_stop(&self) -> Option<EnvelopeStop> {
        self.stop.get()
    }

    /// The stop a DECLINE of this funnel is reported as: the latched stop, or
    /// `Backstop` when a lane-local wall clock ended a lane (that lane might
    /// have accepted on a faster host, so the decline is not a fact about the
    /// proof). `None`: every lane declined on its own evidence or count.
    pub(crate) fn decline_stop(&self) -> Option<EnvelopeStop> {
        self.observed_stop().or_else(|| {
            self.lane_clock_spent
                .get()
                .then_some(EnvelopeStop::Backstop)
        })
    }

    /// A lane-local wall clock (not the backstop) ended a lane.
    pub(crate) fn note_lane_clock(&self) {
        self.lane_clock_spent.set(true);
    }

    /// Classify a nested solve's `Unknown`: an envelope origin latches its
    /// stop; a deadline latches `Backstop` when the backstop has passed and is
    /// a lane-local clock otherwise; anything else (a spent count, an
    /// incomplete lane, a refused certification) is a plain decline, unless
    /// a cancel of the certification's node is up: then the nested solve may
    /// have ended on it ([`Self::certify_cancelled`]), and it is that stop.
    pub(crate) fn latch_nested(&self, origin: Option<crate::UnknownOrigin>, term_tripped: bool) {
        match EnvelopeStop::of_nested_origin(origin, term_tripped) {
            Some(NestedStop::Envelope(stop)) => self.latch(stop),
            Some(NestedStop::Deadline) if self.backstop_passed() => {
                self.latch(EnvelopeStop::Backstop);
            }
            Some(NestedStop::Deadline) => self.note_lane_clock(),
            None => {
                if let Some(stop) = self.certify_cancelled() {
                    self.latch(stop);
                }
            }
        }
    }

    /// Charge what a nested executor spent on `share` and classify its stop.
    pub(crate) fn settle_nested(&self, exec: &crate::Executor, share: EffortShare) {
        self.effort.settle(share, exec.statistics().conflicts);
        self.latch_nested(exec.unknown_origin(), exec.term_memory_exceeded());
    }

    /// The one check a lane's acceptance still answers to: the exact
    /// term-store count of what it built (a count, so a fact). A breach
    /// latches `TermMemory`.
    pub(crate) fn accept_fits(&self, terms: &ay_core::TermStore) -> bool {
        let exceeded = self
            .term_memory_limit
            .is_some_and(|limit| terms.true_memory_bytes() > limit);
        if exceeded {
            self.latch(EnvelopeStop::TermMemory);
        }
        !exceeded
    }

    /// Whether `terms` may be cloned for a nested lane: no stop, the exact
    /// term count, and the clone's predicted footprint.
    pub(crate) fn clone_fits(&self, terms: &ay_core::TermStore) -> bool {
        !self.stop_requested(terms)
            && self.accept_fits(terms)
            && crate::memory::probe_clone_fits(terms.true_memory_bytes(), self.memory_limit)
    }

    /// Arm a fresh nested executor with this envelope and a grant on `share`.
    /// The grant, or `None` (nothing to run) when the share is spent or a
    /// stop fired.
    pub(crate) fn install_on(
        &self,
        executor: &mut crate::Executor,
        share: EffortShare,
    ) -> Option<u64> {
        let grant = self.effort.grant(share)?;
        executor.set_memory_limit(self.memory_limit);
        executor.set_term_memory_limit(self.term_memory_limit);
        self.effort.arm(
            executor,
            grant,
            self.backstop,
            self.interrupt.clone(),
            self.certify(),
        );
        (!self.stop_requested(&executor.ctx.terms) && self.accept_fits(&executor.ctx.terms))
            .then_some(grant)
    }

    /// Run `solve`, a nested solve this envelope armed on `share`, under the
    /// share's grant of split-loop round trips ([`EffortShare::round_trips`];
    /// none for step (4)'s re-solve, which runs as it did).
    pub(crate) fn in_round_trip_grant<T>(
        &self,
        share: EffortShare,
        solve: impl FnOnce() -> T,
    ) -> T {
        let Some(round_trips) = share.round_trips() else {
            return solve();
        };
        self.in_round_trips(round_trips, solve)
    }

    /// Run `solve`, a nested solve of this envelope, under a grant of
    /// `round_trips` split-loop round trips.
    ///
    /// The grant is a `Full` child of the node where the nested check would
    /// run (`Executor::open_check_node`): the certification's node while
    /// this thread runs above it (or outside every node), entered on this
    /// thread for the solve, so the nested check hangs below it and keeps the
    /// envelope it had; otherwise the current caller node. A grant/share
    /// entered after this envelope was built must not be escaped by
    /// re-entering Certify. The solve charges every round trip it runs to the
    /// grant. Its stop polls find the grant spent at the round trip after the
    /// last granted one, and the check ends `Unknown` from
    /// `DeterministicResourceBudget`, which [`Self::latch_nested`] reads as a
    /// plain decline: a count, never a stop. A grant around the certification
    /// (a metered probe's) still bounds the solve; the tighter one stops it.
    pub(crate) fn in_round_trips<T>(&self, round_trips: u64, solve: impl FnOnce() -> T) -> T {
        let current = ay_core::resource::current_guard();
        let _in_certify = self
            .certify
            .as_ref()
            .filter(|certify| current.as_ref().is_none_or(|node| certify.is_within(node)))
            .map(Guard::enter);
        let _grant = ay_core::resource::enter_work_grant(round_trips);
        solve()
    }

    /// Install this envelope's memory ceilings on a fresh native
    /// proof-checking solver before translation allocates into its private
    /// term store.
    pub(crate) fn start_native_solver(&self, solver: &mut super::super::Solver) -> bool {
        solver.set_memory_limit(self.memory_limit);
        solver.set_term_memory_limit(self.term_memory_limit);
        !self.stop_requested(solver.terms()) && self.accept_fits(solver.terms())
    }

    /// Poll both the caller controls and the fresh solver's own term store.
    pub(crate) fn native_solver_live(&self, solver: &super::super::Solver) -> bool {
        !self.stop_requested(solver.terms())
    }

    /// Run a fresh native internal query on a grant of `share`. `None` means
    /// there was nothing to run on (a spent share, a stop before the solve)
    /// or the solve built past the exact term ceiling; a completed result is
    /// otherwise returned as the fact it is.
    pub(crate) fn check_native_solver(
        &self,
        solver: &mut super::super::Solver,
        share: EffortShare,
    ) -> Option<super::super::VerifiedSolveResult> {
        if self.stop_requested(solver.terms()) || !self.accept_fits(solver.terms()) {
            return None;
        }
        let grant = self.effort.grant(share)?;
        self.effort
            .arm_native(solver, grant, self.backstop, self.certify());
        let result = self.in_round_trip_grant(share, || {
            if let Some(interrupt) = self.interrupt.clone() {
                solver.check_sat_interruptible_internal_query(move || {
                    interrupt.load(Ordering::Relaxed)
                })
            } else {
                solver.check_sat_internal_query()
            }
        });
        self.effort.settle(share, solver.statistics().conflicts);
        self.latch_nested(
            solver.certification_unknown_origin(),
            solver.certification_term_store_tripped(),
        );
        self.accept_fits(solver.terms()).then_some(result)
    }
}
