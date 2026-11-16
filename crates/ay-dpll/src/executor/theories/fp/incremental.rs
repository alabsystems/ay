// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Persistent FP: caches and defining clauses commit as one owned transaction.
//!
//! A fixed FP offset, global definitions and scoped activations retain the old
//! persistent semantics. Until final admission the Executor holds an empty
//! same-scope shell; cancellation or unwind drops the entire mutated trial.

mod prepare;
#[cfg(test)]
mod tests;
mod transfer;

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::TseitinResult;
use ay_fp::FpBuildProgress;
use ay_sat::{SatResult, Solver as SatSolver};

use crate::executor::Executor;
use crate::executor_types::{ExecutorError, Result, SolveResult, UnknownOrigin, UnknownReason};
use crate::incremental_state::{FpIncrementalAdmission, IncrementalFpState};

use super::super::ChainSpend;
use super::congruence;
use super::stop::FpStop;
use prepare::PreparationError;

// Later global clauses may mention variables preprocessing would eliminate;
// persistent reactivation needs separate qualification before changing this.
const PERSISTENT_FP_SAT_PREPROCESS: bool = false;
const REORDER_DISABLE_VARS: usize = 50_000;

#[derive(Clone, Copy, Debug)]
pub(super) enum IncrementalFpPhase {
    Admission,
    ForeignScan,
    Provenance,
    TrialTaken,
    Tseitin,
    #[cfg(test)]
    Construction(FpBuildProgress),
    #[cfg(not(test))]
    Construction,
    BoolRepair,
    Namespace,
    SatAllocation,
    GlobalDefinition,
    GlobalFpClause,
    PredicateLink,
    ConditionLink,
    BoolLink,
    Activation,
    SatSearch,
    SatPoll,
    SatReturned,
    ModelExtracted,
    Publication,
    Commit,
}

impl IncrementalFpPhase {
    fn construction(progress: FpBuildProgress) -> Self {
        #[cfg(test)]
        {
            Self::Construction(progress)
        }
        #[cfg(not(test))]
        {
            let _ = progress;
            Self::Construction
        }
    }
}

pub(super) fn checkpoint(
    stop: &FpStop,
    observe: &impl Fn(IncrementalFpPhase),
    phase: IncrementalFpPhase,
) -> std::result::Result<(), UnknownOrigin> {
    observe(phase);
    stop.check()
}

enum TrialOutcome {
    Deferred,
    Disabled(Option<SolveResult>),
    Solved(SolveResult),
}

enum TrialFailure {
    Stopped(UnknownOrigin),
    Solver(ExecutorError),
    ModelDecode,
}

impl From<UnknownOrigin> for TrialFailure {
    fn from(origin: UnknownOrigin) -> Self {
        Self::Stopped(origin)
    }
}

impl From<ExecutorError> for TrialFailure {
    fn from(error: ExecutorError) -> Self {
        Self::Solver(error)
    }
}

impl Executor {
    /// A push-time allocation refusal belongs to the next decision attempt,
    /// even when pop or routing removes every FP root before that attempt.
    pub(crate) fn take_pending_fp_namespace_refusal(&mut self) -> Option<UnknownOrigin> {
        self.incr_fp_state
            .as_mut()?
            .take_pending_namespace_refusal()
    }

    pub(in crate::executor) fn reject_pending_fp_namespace_refusal(
        &mut self,
    ) -> Option<SolveResult> {
        let origin = self.take_pending_fp_namespace_refusal()?;
        Some(self.fp_stopped(origin))
    }

    pub(super) fn try_solve_fp_incremental(&mut self) -> Result<Option<SolveResult>> {
        self.try_solve_fp_incremental_observed(&|_| {})
    }

    fn try_solve_fp_incremental_observed(
        &mut self,
        observe: &impl Fn(IncrementalFpPhase),
    ) -> Result<Option<SolveResult>> {
        if let Some(result) = self.reject_pending_fp_namespace_refusal() {
            return Ok(Some(result));
        }
        let state = self
            .incr_fp_state
            .get_or_insert_with(|| Box::new(IncrementalFpState::new()));
        // Before any callback/scan/copy, replace the whole state, not merely SAT.
        // Catching an unwind cannot restore a cache whose clauses were dropped.
        let mut trial = state.take_for_update();
        let stop = FpStop::from_executor(self);
        let attempt = self.run_fp_incremental_trial(&mut trial, &stop, observe);
        // Latch arithmetic failures before another live source can supersede them.
        if let Err(TrialFailure::Stopped(origin)) = &attempt {
            stop.refuse(*origin);
        }
        if let Err(origin) = checkpoint(&stop, observe, IncrementalFpPhase::Commit) {
            return Ok(Some(self.fp_stopped(origin)));
        }
        match attempt {
            Ok(outcome) => {
                let result = match outcome {
                    TrialOutcome::Deferred => None,
                    TrialOutcome::Disabled(result) => {
                        trial.disable_and_teardown();
                        result
                    }
                    TrialOutcome::Solved(result) => Some(result),
                };
                self.incr_fp_state = Some(Box::new(trial));
                Ok(result)
            }
            Err(TrialFailure::Stopped(origin)) => Ok(Some(self.fp_stopped(stop.refuse(origin)))),
            Err(TrialFailure::Solver(error)) => Err(error),
            // The complete trial is discarded, not committed or permanently
            // disabled. A malformed model is incomplete, not a resource stop.
            Err(TrialFailure::ModelDecode) => Ok(Some(self.fp_model_decode_refusal())),
        }
    }

    fn run_fp_incremental_trial(
        &mut self,
        trial: &mut IncrementalFpState,
        stop: &FpStop,
        observe: &impl Fn(IncrementalFpPhase),
    ) -> std::result::Result<TrialOutcome, TrialFailure> {
        checkpoint(stop, observe, IncrementalFpPhase::TrialTaken)?;
        let mut admission_check = || checkpoint(stop, observe, IncrementalFpPhase::Admission);
        match trial.observe_live_assertion_reuse_with_control(
            &self.ctx.terms,
            &self.ctx.assertions,
            &mut admission_check,
        )? {
            FpIncrementalAdmission::Admit => {}
            FpIncrementalAdmission::Defer => return Ok(TrialOutcome::Deferred),
        }
        let mut scan_check = || {
            checkpoint(stop, observe, IncrementalFpPhase::ForeignScan)
                .map_err(|_| ay_fp::FpBuildError::Interrupted)
        };
        let foreign = congruence::scan_foreign_controlled(
            &self.ctx.terms,
            &self.ctx.assertions,
            &mut scan_check,
        )
        .map_err(|error| stop.refuse_build_error(error))?;
        if !foreign.is_empty() {
            return Ok(TrialOutcome::Disabled(None));
        }
        // An activation from a substituted internal query must never survive
        // as if the authored frontend assertion stack owned that activation.
        let mut live = HashSet::default();
        for &term in &self.ctx.assertions {
            checkpoint(stop, observe, IncrementalFpPhase::Provenance)?;
            live.insert(term);
        }
        for term in trial.assertion_activation_scope.keys() {
            checkpoint(stop, observe, IncrementalFpPhase::Provenance)?;
            if !live.contains(term) {
                return Ok(TrialOutcome::Disabled(None));
            }
        }
        let mut prepared =
            match prepare::prepare(&self.ctx.terms, &self.ctx.assertions, trial, stop, observe) {
                Ok(prepared) => prepared,
                Err(PreparationError::Stopped(origin)) => return Err(origin.into()),
                Err(PreparationError::ConversionDecline) => {
                    return Ok(TrialOutcome::Disabled(None))
                }
                Err(PreparationError::Unsupported) => {
                    self.record_unknown_from_origin(UnknownOrigin::UnsupportedFeature);
                    return Ok(TrialOutcome::Disabled(Some(SolveResult::Unknown)));
                }
                Err(PreparationError::EncodingGap) => {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    self.record_unknown_diagnostic(
                        UnknownReason::Incomplete,
                        "persistent FP base encoding left an ite condition unresolved",
                    );
                    return Ok(TrialOutcome::Disabled(Some(SolveResult::Unknown)));
                }
            };
        let mut solver = self.fp_incremental_sat(trial, stop, observe)?;
        transfer::load(
            &mut solver,
            trial,
            &mut prepared,
            &self.ctx.assertions,
            stop,
            observe,
        )?;
        stop.check()?;
        let term_to_var = trial.tseitin_state.term_to_var.clone();
        stop.check()?;
        let var_to_term = trial.tseitin_state.var_to_term.clone();
        stop.check()?;
        let tseitin = TseitinResult::new(
            vec![],
            term_to_var,
            var_to_term,
            1,
            trial.tseitin_state.next_var - 1,
        );
        self.arm_sat_count_budget(&mut solver, ChainSpend::NONE);
        checkpoint(stop, observe, IncrementalFpPhase::SatSearch)?;
        let result = self.solve_sat_under_query_stop(&mut solver, || {
            observe(IncrementalFpPhase::SatPoll);
            stop.should_stop()
        });
        collect_sat_stats!(self, &solver);
        self.capture_fp_sat_unknown(&result, solver.last_unknown_reason(), stop);
        checkpoint(stop, observe, IncrementalFpPhase::SatReturned)?;
        trial.solves = trial.solves.saturating_add(1);
        self.last_statistics
            .set_int("fp_incremental.solves", trial.solves);
        let result =
            self.finish_fp_incremental(result, &tseitin, trial, prepared.offset, stop, observe)?;
        // Rejoin the complete SAT owner only after model admission. The slot in
        // the Executor remains the empty shell until the final Commit check.
        trial.persistent_sat = Some(solver);
        Ok(TrialOutcome::Solved(result))
    }

    fn fp_incremental_sat(
        &mut self,
        trial: &mut IncrementalFpState,
        stop: &FpStop,
        observe: &impl Fn(IncrementalFpPhase),
    ) -> std::result::Result<SatSolver, UnknownOrigin> {
        checkpoint(stop, observe, IncrementalFpPhase::Namespace)?;
        let existing_total = trial
            .persistent_sat
            .as_ref()
            .map_or(0, SatSolver::total_num_vars);
        let total = trial
            .checked_total_vars(existing_total, 0)
            .map_err(|o| stop.refuse(o))?;
        trial
            .checked_total_vars(existing_total, trial.pending_pushes)
            .map_err(|o| stop.refuse(o))?;
        checkpoint(stop, observe, IncrementalFpPhase::SatAllocation)?;
        let random_seed = self.current_random_seed();
        self.record_applied_sat_random_seed_for_test(random_seed);
        let mut solver = match trial.persistent_sat.take() {
            Some(solver) => solver,
            None => {
                let mut solver = SatSolver::new(total);
                solver.set_random_seed(random_seed);
                if self.progress_enabled {
                    solver.set_progress_enabled(true);
                }
                if let Some(path) = &self.progress_json_path {
                    if let Ok(observer) =
                        ay_sat::json_observer::JsonProgressObserver::new_append(path)
                    {
                        solver.set_observer(Some(Box::new(observer)));
                    }
                }
                solver.set_congruence_enabled(false);
                solver.set_preprocess_enabled(PERSISTENT_FP_SAT_PREPROCESS);
                if total > REORDER_DISABLE_VARS {
                    solver.set_reorder_enabled(false);
                }
                solver
            }
        };
        solver.ensure_num_vars(total);
        for _ in 0..trial.pending_pushes {
            checkpoint(stop, observe, IncrementalFpPhase::SatAllocation)?;
            solver.push();
        }
        trial.pending_pushes = 0;
        trial
            .sync_with_solver_total(solver.total_num_vars())
            .map_err(|o| stop.refuse(o))?;
        stop.check()?;
        Ok(solver)
    }

    fn finish_fp_incremental(
        &mut self,
        result: SatResult,
        tseitin: &TseitinResult,
        trial: &IncrementalFpState,
        offset: i32,
        stop: &FpStop,
        observe: &impl Fn(IncrementalFpPhase),
    ) -> std::result::Result<SolveResult, TrialFailure> {
        let cache = &trial.fp_cache;
        let (fp_model, bv_model) = if let SatResult::Sat(ref model) = result {
            let fp = Self::extract_fp_model_from_bits_controlled(
                model,
                &cache.term_to_fp,
                &cache.rm_terms,
                offset,
                &self.ctx.terms,
                &mut || !stop.should_stop(),
            );
            let Some(fp) = fp else {
                checkpoint(stop, observe, IncrementalFpPhase::ModelExtracted)?;
                return Err(TrialFailure::ModelDecode);
            };
            let bv = if cache.bv_term_bits.is_empty() {
                None
            } else {
                Some(Self::extract_bv_model_from_fp_bits(
                    model,
                    &cache.bv_term_bits,
                    offset,
                    &self.ctx.terms,
                ))
            };
            (Some(fp), bv)
        } else {
            (None, None)
        };
        checkpoint(stop, observe, IncrementalFpPhase::ModelExtracted)?;
        let proposed = self.solve_and_store_model_full(
            result, tseitin, None, None, None, None, bv_model, fp_model, None, None,
        );
        if matches!(proposed, Ok(SolveResult::Unknown)) && self.fp_recorded_resource_stop() {
            if let Some(reason) = self.last_unknown_reason {
                stop.refuse(reason.origin());
            }
        }
        checkpoint(stop, observe, IncrementalFpPhase::Publication)?;
        if self.should_abort_theory_loop() {
            let origin = self
                .last_unknown_reason
                .unwrap_or(UnknownReason::Unknown)
                .origin();
            return Err(stop.refuse(origin).into());
        }
        proposed.map_err(TrialFailure::Solver)
    }
}
