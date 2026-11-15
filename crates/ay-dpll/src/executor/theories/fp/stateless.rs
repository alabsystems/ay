// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One cooperative owner from stateless FP construction to verdict admission.

mod prepare;
#[cfg(test)]
mod tests;
mod transfer;

use ay_fp::FpBuildProgress;
use ay_sat::{SatResult, SatUnknownReason, Solver as SatSolver};

use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult, UnknownOrigin, UnknownReason};

use super::super::ChainSpend;
use super::stop::FpStop;
use prepare::{FpPreparationError, PreparedFp};

/// Private phase observations make stops reproducible without timing or knobs.
#[derive(Clone, Copy, Debug)]
pub(super) enum FpPhase {
    Tseitin,
    Construction(FpBuildProgress),
    CongruenceScan,
    CongruencePlan,
    ClauseTransfer,
    SatLoad,
    SatSearch,
    SatPoll,
    SatReturned,
    ModelExtracted,
    Publication,
}

fn checkpoint(
    stop: &FpStop,
    observe: &impl Fn(FpPhase),
    phase: FpPhase,
) -> std::result::Result<(), UnknownOrigin> {
    observe(phase);
    stop.check()
}

impl Executor {
    /// Resource exhaustion is terminal for recursive FP retry adapters. The
    /// typed reason remains available even before public last_result is set.
    pub(super) fn fp_recorded_resource_stop(&self) -> bool {
        matches!(
            self.last_unknown_reason.map(UnknownReason::origin),
            Some(
                UnknownOrigin::InterruptFlag
                    | UnknownOrigin::SolveDeadline
                    | UnknownOrigin::MemoryBudget
                    | UnknownOrigin::DeterministicResourceBudget
            )
        )
    }

    pub(super) fn solve_fp_stateless(&mut self) -> Result<SolveResult> {
        self.solve_fp_stateless_observed(&|_| {})
    }

    fn solve_fp_stateless_observed(&mut self, observe: &impl Fn(FpPhase)) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        let stop = FpStop::from_executor(self);
        let mut prepared =
            match prepare::prepare(&self.ctx.terms, &self.ctx.assertions, &stop, observe) {
                Ok(prepared) => prepared,
                Err(error) => return Ok(self.fp_preparation_refusal(error, &stop)),
            };
        if let Err(origin) = stop.check() {
            return Ok(self.fp_stopped(origin));
        }

        // Namespace admission happened before either the signed offsets or
        // this allocation. Library-only FP bounds do not cover Tseitin + FP.
        let total_vars = prepared.namespace.total_vars();
        let mut solver = SatSolver::new(total_vars as usize);
        self.apply_random_seed_to_sat(&mut solver);
        self.apply_progress_to_sat(&mut solver);
        solver.set_congruence_enabled(false);
        if total_vars as usize > 50_000 {
            solver.set_reorder_enabled(false);
        }
        if let Some(seed) = self.random_seed {
            solver.set_random_seed(seed);
        }
        if let Err(origin) = transfer::load(&mut solver, &mut prepared, &stop, observe) {
            return Ok(self.fp_stopped(origin));
        }
        self.arm_sat_count_budget(&mut solver, ChainSpend::NONE);
        if let Err(origin) = checkpoint(&stop, observe, FpPhase::SatSearch) {
            return Ok(self.fp_stopped(origin));
        }
        let result = self.solve_sat_under_query_stop(&mut solver, || {
            observe(FpPhase::SatPoll);
            stop.should_stop()
        });
        collect_sat_stats!(self, &solver);
        self.capture_fp_sat_unknown(&result, solver.last_unknown_reason(), &stop);
        // SAT's callback-stop reason is generic Interrupted. Apply our first
        // typed origin AFTER statistics so memory/deadline provenance survives.
        if let Err(origin) = checkpoint(&stop, observe, FpPhase::SatReturned) {
            return Ok(self.fp_stopped(origin));
        }
        if prepared.congruence_incomplete && matches!(result, SatResult::Sat(_)) {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.record_unknown_diagnostic(
                UnknownReason::Incomplete,
                "FP congruence encoding omitted uninterpreted structure: its SAT model is \
                 only a model of a relaxation; UNSAT remains valid",
            );
            return Ok(SolveResult::Unknown);
        }
        self.finish_fp_stateless(result, &prepared, &stop, observe)
    }

    pub(super) fn capture_fp_sat_unknown(
        &mut self,
        result: &SatResult,
        reason: Option<SatUnknownReason>,
        stop: &FpStop,
    ) {
        if matches!(result, SatResult::Unknown) {
            // This fresh solver owns its current Unknown. An earlier ordinary
            // RM branch's Incomplete must not hide this branch's SAT budget.
            let origin = reason
                .map(Self::map_sat_unknown_origin)
                .unwrap_or(UnknownOrigin::IncompleteSolverLane);
            self.record_unknown_from_origin(origin);
            if self.fp_recorded_resource_stop() {
                stop.refuse(origin);
            }
        }
    }

    fn finish_fp_stateless(
        &mut self,
        result: SatResult,
        prepared: &PreparedFp,
        stop: &FpStop,
        observe: &impl Fn(FpPhase),
    ) -> Result<SolveResult> {
        let var_offset = prepared.namespace.offset();
        let cache = &prepared.encoding.cache;
        let (fp_model, bv_model) = if let SatResult::Sat(ref sat_model) = result {
            let fp = Self::extract_fp_model_from_bits_controlled(
                sat_model,
                &cache.term_to_fp,
                &cache.rm_terms,
                var_offset,
                &self.ctx.terms,
                &mut || !stop.should_stop(),
            );
            let Some(fp) = fp else {
                if let Err(origin) = checkpoint(stop, observe, FpPhase::ModelExtracted) {
                    return Ok(self.fp_stopped(origin));
                }
                return Ok(self.fp_model_decode_refusal());
            };
            let bv = if cache.bv_term_bits.is_empty() {
                None
            } else {
                Some(Self::extract_bv_model_from_fp_bits(
                    sat_model,
                    &cache.bv_term_bits,
                    var_offset,
                    &self.ctx.terms,
                ))
            };
            (Some(fp), bv)
        } else {
            (None, None)
        };
        if let Err(origin) = checkpoint(stop, observe, FpPhase::ModelExtracted) {
            return Ok(self.fp_stopped(origin));
        }
        let proposed = self.solve_and_store_model_full(
            result,
            &prepared.tseitin,
            None,
            None,
            None,
            None,
            bv_model,
            fp_model,
            None,
            None,
        );
        if let Err(origin) = checkpoint(stop, observe, FpPhase::Publication) {
            return Ok(self.fp_stopped(origin));
        }
        // Model completion may mutate TermStore; construction did not. Recheck
        // the existing term budget after that mutable window as well.
        if self.should_abort_theory_loop() {
            return Ok(self.finalize_unknown_publication(SolveResult::Unknown));
        }
        proposed
    }

    pub(super) fn fp_stopped(&mut self, origin: UnknownOrigin) -> SolveResult {
        // Use the existing canonical revocation, including any prior model or
        // certificate. No private competing artifact-clearing policy exists.
        self.publish_unknown_from_origin(origin);
        self.record_unknown_diagnostic(
            origin.reason(),
            "FP construction/solve attempt observed a resource stop; no partial encoding \
             or later reset can authorize a verdict from that attempt",
        );
        SolveResult::Unknown
    }

    pub(super) fn fp_model_decode_refusal(&mut self) -> SolveResult {
        self.publish_unknown_from_origin(UnknownOrigin::IncompleteSolverLane);
        self.record_unknown_diagnostic(
            UnknownReason::Incomplete,
            "FP SAT assignment did not provide a complete, well-formed typed model; \
             decoding refused before model publication",
        );
        SolveResult::Unknown
    }

    fn fp_preparation_refusal(&mut self, error: FpPreparationError, stop: &FpStop) -> SolveResult {
        if let FpPreparationError::Stopped(origin) = error {
            return self.fp_stopped(origin);
        }
        if let Err(origin) = stop.check() {
            return self.fp_stopped(origin);
        }
        match error {
            FpPreparationError::Unsupported => {
                self.last_unknown_reason = Some(UnknownReason::Unsupported);
            }
            FpPreparationError::BaseGap => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.record_unknown_diagnostic(
                    UnknownReason::Incomplete,
                    "FP base encoding left an ite condition unresolved; this is not a \
                     congruence-only relaxation and cannot authorize a verdict",
                );
            }
            FpPreparationError::Stopped(origin) => return self.fp_stopped(origin),
        }
        SolveResult::Unknown
    }
}
