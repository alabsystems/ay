// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unsafe results restated over the problem the solver was handed, and
//! admitted under their original owner.
//!
//! `PdrSolver::new` rewrites its input before searching: it expands nullary
//! fail predicates (`ChcProblem::expand_nullary_fail_queries`), may scalarize
//! array arguments, and splits clauses on disjunctions and `ite`s
//! (`try_split_ors_in_clauses`, `try_split_ites_in_clauses`). A
//! counterexample found by the search names
//! clauses of that REWRITTEN problem: its ground derivation, its derivation
//! witness (each fact's `incoming_clause`, the `query_clause`) and its steps'
//! `clause_index`. Every caller reads those indices in terms of the problem it
//! passed in (portfolio back-translation, adaptive validators with
//! `preserve_original_clauses`), where a rewritten index names another clause
//! or none: a split problem's index past the input's length, or an in-range
//! index naming the wrong clause.
//!
//! So every Unsafe result is restated here, through the rewrites' recorded
//! clause maps: each case split records the clause every output clause came
//! from (a case is an instance of its source clause: the same predicates and
//! variables under a stronger constraint), and the nullary expansion records
//! which clauses it kept and which queries it built from `body ⇒ fail` and
//! `fail ⇒ false`. A ground derivation is re-validated on the input problem
//! after the exact maps, else re-attributed by content (also re-validated),
//! else dropped; a witness that the maps cannot restate is dropped. Either way
//! nothing the caller receives names a rewritten clause.
//!
//! Array scalarization keeps clauses one for one but changes predicate
//! arities, so a witness's states and instances name argument positions of
//! the SCALARIZED predicates. Restating its clause indices would send it down
//! the verifier's trusted per-clause path with mis-positioned values, where a
//! genuine counterexample can be refuted; such a witness is dropped instead,
//! and the verifier decides on the counterexample's depth and its own search.
//!
//! The clause maps live in `mapping`. The expanded derivation must still
//! validate on the captured original problem. A rejected mapping loses ground
//! evidence as before; an observed owner refusal is terminal Unknown, never
//! that ordinary rejection fallback.

mod mapping;

use super::{Counterexample, PdrResult, PdrSolver};
use crate::bmc::memory::Budget;
use crate::smt::deadline::{ScopedLaneCancellation, ScopedSmtDeadline};
use crate::smt::resource_observation::ScopedResourceObservation;
use crate::CancellationToken;
use ay_core::time::Instant;
use std::cell::Cell;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

/// Refusal is not a claim that the candidate or original input is refuted.
#[derive(Debug)]
pub(in crate::pdr::solver) struct InputRestatementInterrupted;

/// Same original owner across mapping, native replay and final cleanup.
pub(in crate::pdr::solver) struct InputRestatementControl<'a> {
    solver: &'a PdrSolver,
    deadline: Option<Instant>,
    cancellation: Option<CancellationToken>,
    interrupt: Option<Arc<AtomicBool>>,
    memory: Option<ay_sys::MemoryGroupObservation>,
    terms: Budget,
    stopped: Cell<bool>,
    observation: ScopedResourceObservation,
    _lane: Option<ScopedLaneCancellation>,
    _deadline: Option<ScopedSmtDeadline>,
}

impl InputRestatementControl<'_> {
    pub(in crate::pdr::solver) fn install_memory(&self) -> impl Drop {
        self.terms.install()
    }

    pub(in crate::pdr::solver) fn open(&self) -> bool {
        // Pre-latching also refuses an unwinding/reentrant stop observer.
        if self.stopped.replace(true) {
            return false;
        }
        let closed = self.deadline.is_some_and(|d| Instant::now() >= d)
            || self
                .cancellation
                .as_ref()
                .is_some_and(CancellationToken::is_cancelled)
            || self
                .interrupt
                .as_ref()
                .is_some_and(|f| f.load(Ordering::Relaxed))
            || self.memory.as_ref().is_some_and(|m| m.is_tripped())
            || ay_sys::current_memory_group_soft_tripped()
            || self.observation.first().is_some()
            || self.solver.is_cancelled()
            || !self.terms.open()
            || ay_core::resource::check_stop_requested()
            || self.deadline.is_some_and(|d| Instant::now() >= d);
        self.stopped.set(closed);
        !closed
    }

    /// Final returned-result veto after opaque trace/temporary cleanup.
    /// Prior trace records are observations, not post-flush proof credentials.
    pub(in crate::pdr::solver) fn limit_after_cleanup(&self, result: PdrResult) -> PdrResult {
        if matches!(&result, PdrResult::Unsafe(_)) && !self.open() {
            drop(result);
            PdrResult::Unknown
        } else {
            result
        }
    }
}

impl PdrSolver {
    pub(in crate::pdr::solver) fn input_restatement_owner(&self) -> InputRestatementControl<'_> {
        let deadline = [
            self.solve_deadline,
            crate::smt::deadline::effective_thread_deadline(),
        ]
        .into_iter()
        .flatten()
        .min();
        let mut cancellation = self.config.effective_cancellation_token();
        if let Some(ambient) = crate::smt::deadline::current_lane_token() {
            if let Some(token) = cancellation.as_mut() {
                token.link_upstream(&ambient);
            } else {
                cancellation = Some(ambient.child());
            }
        }
        let cancellation = cancellation.map(|token| token.sticky_child());
        let interrupt = crate::smt::deadline::lane_interrupt_flag();
        let stopped = interrupt
            .as_ref()
            .is_some_and(|f| f.load(Ordering::Relaxed));
        let lane = cancellation
            .as_ref()
            .map(|token| ScopedLaneCancellation::install(token.clone(), interrupt.clone()));
        InputRestatementControl {
            solver: self,
            deadline,
            cancellation,
            interrupt,
            memory: ay_sys::current_memory_group_observation(),
            terms: Budget::capture(self.config.memory_budget(), self.smt.term_memory_budget),
            stopped: Cell::new(stopped),
            observation: ScopedResourceObservation::install(),
            _lane: lane,
            _deadline: deadline.map(ScopedSmtDeadline::install_until),
        }
    }

    pub(in crate::pdr::solver) fn restate_cex_for_input(
        &self,
        mut cex: Counterexample,
        owner: &InputRestatementControl<'_>,
    ) -> Result<Counterexample, InputRestatementInterrupted> {
        if !owner.open() {
            return Err(InputRestatementInterrupted);
        }
        let unchanged = self.problem.structurally_equal(&self.input_problem);
        if !owner.open() {
            return Err(InputRestatementInterrupted);
        }
        if !unchanged {
            // The compact DAG is not rewritten or granted authority by an index
            // map. Retain it only after replay on the actual original source.
            if let Some(evidence) = cex.compact_evidence() {
                let retained = evidence.owner();
                let mut progress = || owner.open();
                let mut control = retained.with_progress(&mut progress);
                if crate::ground_derivation::compact::validate(
                    &self.input_problem,
                    evidence.derivation(),
                    &mut control,
                )
                .is_err()
                {
                    return Err(InputRestatementInterrupted);
                }
            }
            if let Some(derivation) = cex.ground_derivation.take() {
                cex.ground_derivation = self.restate_ground_for_input(derivation, owner)?;
            }
            cex.witness = cex
                .witness
                .take()
                .and_then(|w| self.restate_witness(w, owner));
            self.restate_step_indices(&mut cex, owner);
        }
        if !owner.open() {
            return Err(InputRestatementInterrupted);
        }
        Ok(cex)
    }

    /// `cex` as this solver's caller reads it. A ground derivation it carries
    /// names THIS solver's clauses, which PDR rewrote (nullary-query
    /// expansion, case splits, array scalarization) while callers map clause
    /// indices in the terms of the problem they passed in; so the derivation
    /// is restated over the input clauses, or dropped when it cannot be (the
    /// caller then finds its own evidence). Every Unsafe result passes through
    /// here exactly once (`finish_with_result_trace`).
    fn restate_ground_for_input(
        &self,
        derivation: crate::ground_derivation::GroundDerivation,
        owner: &InputRestatementControl<'_>,
    ) -> Result<Option<crate::ground_derivation::GroundDerivation>, InputRestatementInterrupted>
    {
        // Both mappings revalidate on the original input. Ordinary rejection
        // may try content re-attribution; owner refusal never starts that retry.
        let mapped = self.derivation_through_clause_maps(&derivation, owner)?;
        if !owner.open() {
            return Err(InputRestatementInterrupted);
        }
        if mapped.is_some() {
            return Ok(mapped);
        }
        crate::ground_derivation::reresolve::reresolve_ground_derivation_with_progress(
            &derivation,
            &self.problem,
            &self.input_problem,
            &mut || owner.open(),
        )
        .map_err(|_| InputRestatementInterrupted)
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
#[path = "input_restatement_tests.rs"]
mod clause_map_tests;
