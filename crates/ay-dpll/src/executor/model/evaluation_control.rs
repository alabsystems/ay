// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Resource ownership for evaluation within a decision or an external model read.

use ay_core::time::Instant;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};

use crate::api::proofs::EnvelopeStop;
use crate::executor::theories::MemoryPollGate;
use crate::executor::Executor;
use crate::executor_types::UnknownOrigin;

mod field_work;
mod native_bv_refutation_scope;
pub(in crate::executor) use native_bv_refutation_scope::NativeBvRefutationScope;

#[derive(Default)]
pub(in crate::executor) struct EvaluationControl {
    frames: Arc<Mutex<Frames>>,
}

#[derive(Default)]
struct Frames {
    current: EvaluationAttempt,
    saved_decision: Option<EvaluationAttempt>,
    readers: usize,
    proof_data: Option<EvaluationArena>,
    proof_charge_pending: bool,
}

struct PendingProofReadCharge {
    frames: Arc<Mutex<Frames>>,
    attempt: EvaluationAttempt,
}

impl Drop for PendingProofReadCharge {
    fn drop(&mut self) {
        let mut frames = lock(&self.frames);
        if frames.proof_charge_pending && self.attempt.is_same_attempt(&frames.current) {
            self.attempt
                .record_stop(UnknownOrigin::IncompleteSolverLane);
            frames.proof_charge_pending = false;
        }
    }
}

/// Clones share the same first refusal, conflict debit and live arena ledger.
#[derive(Clone, Default)]
pub(in crate::executor) struct EvaluationAttempt {
    data: Arc<Mutex<AttemptData>>,
    /// Raised once the first refusal is recorded, never lowered: the stop
    /// chain of a strict walk asks at every checker offer (911 M on qb44)
    /// whether one is, so "none yet" is one relaxed load, not the lock.
    stopped: Arc<AtomicBool>,
}

#[derive(Default)]
struct AttemptData {
    origin: Option<UnknownOrigin>,
    conflicts: u64,
    /// The exact native BV source is offered once across early/late repairs.
    /// Alternate repairs cannot renew its proof-producing allowance.
    native_bv_refutations: Vec<NativeBvRefutationScope>,
    // Construction, failed retries, confirmation and rendering retain this
    // original attempt ledger; cloned models cannot replenish it.
    functional_work_used: Arc<AtomicUsize>,
    field_work: field_work::FieldWorkState,
    decisions: u64,
    arenas: Vec<Option<usize>>,
    read_controls: Option<EvaluationReadControls>,
    /// Operating-system memory observation schedule of every stop poll this
    /// attempt makes (one gate per evaluation, not per evaluated term).
    memory_gate: MemoryPollGate,
}

/// A decision parked around nested subset work: its evaluation attempt and
/// the stop its metered strict walks noted (`certification_stop`). The
/// proof-repair controls re-import that noted stop onto the live attempt
/// (`exact_authored_bv_refutation::control`), so it is the same evidence and
/// is parked, refreshed and restored with the attempt.
pub(in crate::executor) struct ParkedEvaluationDecision {
    attempt: EvaluationAttempt,
    certification_stop: Option<EnvelopeStop>,
}

/// Native getters borrow immutable Solver state after solve controls have
/// been restored. Retain their own control envelope for the complete read.
#[derive(Clone)]
pub(in crate::executor) struct EvaluationReadControls {
    pub(in crate::executor) interrupt: Arc<AtomicBool>,
    pub(in crate::executor) deadline: Option<Instant>,
    pub(in crate::executor) memory_limit: Option<usize>,
    pub(in crate::executor) term_memory_limit: Option<usize>,
}

/// Owned rather than executor-borrowing: text read elaboration needs `&mut self`.
pub(crate) struct EvaluationReadScope {
    frames: Arc<Mutex<Frames>>,
    outer_read: bool,
}

pub(in crate::executor) struct EvaluationArena {
    attempt: EvaluationAttempt,
    slot: usize,
}

fn lock<T>(value: &Mutex<T>) -> MutexGuard<'_, T> {
    // A guard only protects bookkeeping; an unwound evaluation must still be
    // able to release its arena/read ownership and retain its first refusal.
    value.lock().unwrap_or_else(|poison| poison.into_inner())
}

impl EvaluationControl {
    /// Whether a fresh attempt was installed (never inside a model read).
    pub(in crate::executor) fn begin_decision(&self) -> bool {
        let mut frames = lock(&self.frames);
        // An internal decision inside a model read is part of that read, not
        // permission to replenish it. Normal external decisions have no reader.
        if frames.readers != 0 {
            return false;
        }
        frames.current = EvaluationAttempt::default();
        true
    }

    fn attempt(&self) -> EvaluationAttempt {
        lock(&self.frames).current.clone()
    }

    /// Park the current decision's attempt and install a fresh one for nested
    /// work that decides a DIFFERENT (reduced) problem on the same executor —
    /// the unsat-core minimizer's subset solves. A stop those solves record is
    /// evidence about their own problem only; it must never be read back as
    /// the parked decision's refusal. The fresh attempt inherits the read
    /// controls so a caller-installed envelope keeps governing nested work.
    ///
    /// Mirrors `begin_decision`'s rule: inside a model read nothing changes
    /// and `None` is returned, because a decision inside a read is part of
    /// that read and shares its attempt.
    pub(in crate::executor) fn park_decision(&self) -> Option<EvaluationAttempt> {
        let mut frames = lock(&self.frames);
        if frames.readers != 0 {
            return None;
        }
        let fresh = EvaluationAttempt::default();
        lock(&fresh.data).read_controls = lock(&frames.current.data).read_controls.clone();
        Some(std::mem::replace(&mut frames.current, fresh))
    }

    /// Reinstate an attempt parked by [`Self::park_decision`], discarding
    /// whatever nested work recorded meanwhile. Exactly the stop state the
    /// decision itself earned comes back: a stop it had already recorded is
    /// still in the parked object and still publishes. While a model read is
    /// live the parked decision lands in the read's saved slot, which is what
    /// the read's last guard restores on drop.
    pub(in crate::executor) fn restore_decision(&self, parked: Option<EvaluationAttempt>) {
        let Some(parked) = parked else { return };
        let mut frames = lock(&self.frames);
        if frames.readers == 0 {
            frames.current = parked;
        } else {
            frames.saved_decision = Some(parked);
        }
    }

    fn read(&self, controls: Option<EvaluationReadControls>) -> EvaluationReadScope {
        let mut frames = lock(&self.frames);
        if frames.readers == 0 {
            let decision = std::mem::take(&mut frames.current);
            lock(&frames.current.data).read_controls = controls;
            frames.saved_decision = Some(decision);
        } else if frames.proof_charge_pending {
            frames
                .current
                .record_stop(UnknownOrigin::IncompleteSolverLane);
        }
        // A reader requires a live owned guard, so this count is bounded by
        // addressable guard storage; it cannot wrap in a realizable process.
        frames.readers += 1;
        EvaluationReadScope {
            frames: self.frames.clone(),
            outer_read: frames.readers == 1,
        }
    }
}

impl EvaluationReadScope {
    fn charge_proof_data(&self, exec: &Executor) {
        if !self.outer_read {
            return;
        }
        let attempt = {
            let mut frames = lock(&self.frames);
            frames.proof_charge_pending = true;
            frames.current.clone()
        };
        let _pending = PendingProofReadCharge {
            frames: Arc::clone(&self.frames),
            attempt: attempt.clone(),
        };
        let data = exec.admit_retained_proof_read();
        let mut frames = lock(&self.frames);
        if attempt.is_same_attempt(&frames.current) {
            frames.proof_data = data;
            frames.proof_charge_pending = false;
        } else {
            attempt.record_stop(UnknownOrigin::IncompleteSolverLane);
            frames
                .current
                .record_stop(UnknownOrigin::IncompleteSolverLane);
        }
    }

    /// Retain this exact read frame during a consuming adapter handoff. This
    /// neither captures controls nor installs an attempt or an arena.
    pub(crate) fn retain(&self) -> Self {
        let mut frames = lock(&self.frames);
        // As for read(), every count owns addressable guard storage.
        frames.readers += 1;
        Self {
            frames: Arc::clone(&self.frames),
            outer_read: false,
        }
    }
}

impl Drop for EvaluationReadScope {
    fn drop(&mut self) {
        let mut frames = lock(&self.frames);
        frames.readers -= 1;
        if frames.readers == 0 {
            frames.proof_data = None;
            frames.proof_charge_pending = false;
            if let Some(decision) = frames.saved_decision.take() {
                frames.current = decision;
            }
        }
    }
}

impl EvaluationAttempt {
    pub(in crate::executor) fn native_bv_refutation_attempted(
        &self,
        scope: &NativeBvRefutationScope,
    ) -> bool {
        lock(&self.data)
            .native_bv_refutations
            .iter()
            .any(|old| old.matches(scope))
    }

    #[cfg(test)]
    pub(in crate::executor) fn native_bv_refutation_count(&self) -> usize {
        lock(&self.data).native_bv_refutations.len()
    }

    pub(in crate::executor) fn begin_native_bv_refutation(
        &self,
        scope: NativeBvRefutationScope,
    ) -> bool {
        let mut data = lock(&self.data);
        if data.native_bv_refutations.len() >= 64
            || data
                .native_bv_refutations
                .iter()
                .any(|old| old.matches(&scope))
        {
            return false;
        }
        data.native_bv_refutations.push(scope);
        true
    }

    /// Whether both handles share one ledger (clones do; a fresh attempt
    /// installed by `begin_decision` / `park_decision` does not).
    pub(in crate::executor) fn is_same_attempt(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.data, &other.data)
    }

    pub(in crate::executor) fn stop_origin(&self) -> Option<UnknownOrigin> {
        if !self.is_stopped() {
            return None;
        }
        lock(&self.data).origin
    }

    /// Whether a refusal is recorded, as [`Self::stop_origin`] answers it,
    /// read without the lock. A refusal another thread records at once may
    /// be read at the next call; one this thread recorded always is.
    #[inline]
    pub(in crate::executor) fn is_stopped(&self) -> bool {
        self.stopped.load(Ordering::Relaxed)
    }

    /// The flag [`Self::is_stopped`] reads, for a check stop's witness.
    pub(in crate::executor) fn stop_flag(&self) -> Arc<AtomicBool> {
        Arc::clone(&self.stopped)
    }

    pub(in crate::executor) fn record_stop(&self, origin: UnknownOrigin) -> UnknownOrigin {
        let first = {
            let mut data = lock(&self.data);
            let first = *data.origin.get_or_insert(origin);
            // Under the lock, after the origin: a reader that sees the flag
            // and takes the lock reads the origin.
            self.stopped.store(true, Ordering::Relaxed);
            first
        };
        super::eval_guard::note_stop();
        first
    }

    pub(in crate::executor) fn functional_work_counter(&self) -> Arc<AtomicUsize> {
        Arc::clone(&lock(&self.data).functional_work_used)
    }

    /// Whether this attempt's next stop poll must observe process memory.
    fn memory_observation_due(&self) -> bool {
        lock(&self.data).memory_gate.due_lazily(Instant::now)
    }

    #[cfg(test)]
    pub(in crate::executor) fn consumed_conflicts(&self) -> u64 {
        lock(&self.data).conflicts
    }

    #[cfg(test)]
    pub(in crate::executor) fn add_conflicts(&self, conflicts: u64) {
        let mut data = lock(&self.data);
        data.conflicts = data.conflicts.saturating_add(conflicts);
    }

    /// What this attempt's SAT solves already spent of the `:rlimit`
    /// allowances (one solve chain: P4a).
    pub(in crate::executor) fn consumed_spend(&self) -> crate::executor::theories::ChainSpend {
        let data = lock(&self.data);
        crate::executor::theories::ChainSpend {
            conflicts: data.conflicts,
            decisions: data.decisions,
        }
    }

    /// Debit one SAT solve of this attempt.
    pub(in crate::executor) fn debit_solve(&self, solver: &ay_sat::Solver) {
        let mut data = lock(&self.data);
        data.conflicts = data.conflicts.saturating_add(solver.num_conflicts());
        data.decisions = data.decisions.saturating_add(solver.num_decisions());
    }

    pub(in crate::executor) fn temporary_arena(&self) -> Result<EvaluationArena, UnknownOrigin> {
        let mut data = lock(&self.data);
        if let Some(origin) = data.origin {
            return Err(origin);
        }
        let slot = match data.arenas.iter().position(Option::is_none) {
            Some(slot) => slot,
            None => {
                if data.arenas.try_reserve(1).is_err() {
                    drop(data);
                    return Err(self.record_stop(UnknownOrigin::MemoryBudget));
                }
                data.arenas.push(None);
                data.arenas.len() - 1
            }
        };
        data.arenas[slot] = Some(0);
        Ok(EvaluationArena {
            attempt: self.clone(),
            slot,
        })
    }
}

impl EvaluationArena {
    /// Charge source capacity once plus EVERY live temporary arena. This is a
    /// polled term ledger, not an allocator reservation or an RSS bound.
    pub(in crate::executor) fn check_usage(
        &self,
        source_bytes: usize,
        temporary_bytes: usize,
        limit: Option<usize>,
    ) -> Result<(), UnknownOrigin> {
        let mut data = lock(&self.attempt.data);
        if let Some(origin) = data.origin {
            return Err(origin);
        }
        data.arenas[self.slot] = Some(temporary_bytes);
        let Some(limit) = limit else { return Ok(()) };
        let total = data
            .arenas
            .iter()
            .flatten()
            .try_fold(source_bytes, |sum, bytes| sum.checked_add(*bytes));
        if total.is_none_or(|bytes| bytes > limit) {
            drop(data);
            return Err(self.attempt.record_stop(UnknownOrigin::MemoryBudget));
        }
        Ok(())
    }
}

impl Drop for EvaluationArena {
    fn drop(&mut self) {
        lock(&self.attempt.data).arenas[self.slot] = None;
    }
}

impl Executor {
    /// Admit live transient output/copy bytes on this SAME evaluation attempt.
    /// The returned arena releases its charge on drop. This is the existing
    /// polled term ledger, not an allocator reservation or a fresh allowance.
    pub(in crate::executor) fn admit_evaluation_scratch(
        &self,
        bytes: usize,
    ) -> Result<EvaluationArena, UnknownOrigin> {
        self.poll_evaluation_stop()?;
        let arena = self.evaluation_attempt().temporary_arena()?;
        arena.check_usage(
            self.ctx.terms.true_memory_bytes(),
            bytes,
            self.evaluation_term_memory_limit(),
        )?;
        Ok(arena)
    }

    pub(in crate::executor) fn evaluation_attempt(&self) -> EvaluationAttempt {
        self.evaluation_control.attempt()
    }

    pub(in crate::executor) fn evaluation_stop_origin(&self) -> Option<UnknownOrigin> {
        self.evaluation_attempt().stop_origin()
    }

    pub(in crate::executor) fn record_evaluation_stop(
        &self,
        origin: UnknownOrigin,
    ) -> UnknownOrigin {
        self.evaluation_attempt().record_stop(origin)
    }

    /// Park the live decision's attempt around nested subset work; see
    /// [`EvaluationControl::park_decision`]. The stop the decision's strict
    /// walks noted is parked with it (#check-sat-assuming-empty-core): the
    /// proof-repair controls re-import `certification_stop` onto the live
    /// attempt, so left in place one subset attempt's noted stop refused
    /// every later attempt's repairs, and the restored decision's.
    pub(in crate::executor) fn park_evaluation_decision(&self) -> Option<ParkedEvaluationDecision> {
        let attempt = self.evaluation_control.park_decision()?;
        Some(ParkedEvaluationDecision {
            attempt,
            certification_stop: self.certification_stop.take(),
        })
    }

    /// Reinstate the decision parked by [`Self::park_evaluation_decision`]:
    /// its attempt and exactly the certification stop it had noted.
    pub(in crate::executor) fn restore_evaluation_decision(
        &self,
        parked: Option<ParkedEvaluationDecision>,
    ) {
        let Some(parked) = parked else { return };
        self.evaluation_control
            .restore_decision(Some(parked.attempt));
        self.certification_stop.set(parked.certification_stop);
    }

    /// Give the NEXT nested subset solve a clean attempt: the previous
    /// subset's stop, recorded on its attempt or noted by its strict walks, is
    /// discarded rather than read as this one's refusal.
    /// Only meaningful while the live decision is parked.
    pub(in crate::executor) fn begin_subset_evaluation_attempt(&self) {
        drop(self.park_evaluation_decision());
    }

    /// Begin a caller-visible decision: a fresh evaluation attempt, and no
    /// certification stop an earlier decision's strict walks noted, which the
    /// proof-repair controls would otherwise import as this decision's refusal
    /// (#check-sat-assuming-empty-core). Inside a model read both stay the
    /// read's.
    pub(in crate::executor) fn begin_evaluation_decision(&self) {
        if self.evaluation_control.begin_decision() {
            self.certification_stop.set(None);
        }
    }

    pub(in crate::executor) fn publish_evaluation_stop(&mut self) -> bool {
        if let Some(origin) = self.evaluation_stop_origin() {
            self.publish_unknown_from_origin(origin);
            true
        } else {
            false
        }
    }

    pub(crate) fn begin_external_evaluation_read(&self) -> EvaluationReadScope {
        let scope = self.evaluation_control.read(None);
        scope.charge_proof_data(self);
        scope
    }

    pub(crate) fn begin_native_evaluation_read(
        &self,
        interrupt: Arc<AtomicBool>,
        deadline: Option<Instant>,
        memory_limit: Option<usize>,
        term_memory_limit: Option<usize>,
    ) -> EvaluationReadScope {
        let scope = self.evaluation_control.read(Some(EvaluationReadControls {
            interrupt,
            deadline,
            memory_limit,
            term_memory_limit,
        }));
        scope.charge_proof_data(self);
        scope
    }

    fn admit_retained_proof_read(&self) -> Option<EvaluationArena> {
        if self.proof_construction_memory.is_empty() {
            return None;
        }
        let attempt = self.evaluation_attempt();
        let mut bytes = 0usize;
        let mut limit = self.evaluation_term_memory_limit();
        let current = || {
            if attempt.is_same_attempt(&self.evaluation_attempt()) {
                true
            } else {
                attempt.record_stop(UnknownOrigin::IncompleteSolverLane);
                self.record_evaluation_stop(UnknownOrigin::IncompleteSolverLane);
                false
            }
        };
        for memory in &self.proof_construction_memory {
            if self.poll_evaluation_stop().is_err() || !current() {
                return None;
            }
            let (charge, ceiling) = memory.charge_for_attempt(&attempt);
            let Some(total) = bytes.checked_add(charge) else {
                self.record_evaluation_stop(UnknownOrigin::MemoryBudget);
                return None;
            };
            bytes = total;
            limit = match (limit, ceiling) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            };
        }
        let arena = attempt.temporary_arena().ok()?;
        arena
            .check_usage(self.ctx.terms.true_memory_bytes(), bytes, limit)
            .ok()?;
        self.poll_evaluation_stop().ok()?;
        current().then_some(arena)
    }

    pub(in crate::executor) fn evaluation_read_controls(&self) -> Option<EvaluationReadControls> {
        lock(&self.evaluation_attempt().data).read_controls.clone()
    }

    pub(in crate::executor) fn evaluation_term_memory_limit(&self) -> Option<usize> {
        self.term_memory_limit()
            .into_iter()
            .chain(
                self.evaluation_read_controls()
                    .and_then(|controls| controls.term_memory_limit),
            )
            .min()
    }

    pub(in crate::executor) fn poll_evaluation_stop(&self) -> Result<(), UnknownOrigin> {
        let attempt = self.evaluation_attempt();
        if let Some(origin) = attempt.stop_origin() {
            return Err(origin);
        }
        // Interrupt, deadline and term admission are read on every poll; the
        // process-memory syscall follows the attempt's shared gate. A stop
        // built with a fresh gate per poll observed on every evaluated term
        // (12 % of the solver thread on strcspn_2, PERF_vs_winners_2026-09-25).
        super::super::theories::FpStop::from_executor_gated(self, move || {
            attempt.memory_observation_due()
        })
        .check()
        .map_err(|origin| self.record_evaluation_stop(origin))
    }

    /// Check while the read guard is still active, including after formatting
    /// or decoding. The previous decision owner is restored only on guard drop.
    pub(crate) fn check_evaluation_read(&self) -> Result<(), String> {
        self.poll_evaluation_stop()
            .map_err(|origin| format!("model evaluation stopped: {}", origin.reason().code()))
    }

    pub(crate) fn checked_evaluation_output(&self, render: impl FnOnce() -> String) -> String {
        if let Err(error) = self.check_evaluation_read() {
            return format!("(error \"{error}\")");
        }
        let output = render();
        match self.check_evaluation_read() {
            Ok(()) => output,
            Err(error) => format!("(error \"{error}\")"),
        }
    }
}

#[cfg(test)]
mod tests;
