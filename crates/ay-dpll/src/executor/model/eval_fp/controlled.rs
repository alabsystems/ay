// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Disposable concrete FP evaluation under one model-read/decision owner.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, TermId, TermStore};
use ay_fp::{FpBuildError, FpBuildProgress, FpConstruction, FpModelValue, FpSolver};
use ay_sat::{SatResult, Solver as SatSolver};

use crate::executor::model::{EvaluationArena, EvaluationAttempt};
use crate::executor::theories::{FpNamespace, FpStop};
use crate::executor_types::UnknownOrigin;

use super::{Executor, Model};

mod clones;
mod concrete;
mod decode;
#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Debug)]
pub(in crate::executor) enum FpEvalPhase {
    Concretize(TermId),
    Construction(FpBuildProgress),
    Namespace,
    ClauseTransfer,
    SatLoad,
    SatSearch,
    SatPoll,
    SatReturned,
    Decode,
    Cleanup,
}

struct Control<'a> {
    executor: &'a Executor,
    stop: FpStop,
    attempt: EvaluationAttempt,
    arena: EvaluationArena,
    observe: &'a dyn Fn(FpEvalPhase),
}

impl Control<'_> {
    fn admit_fp_clone(
        &self,
        temporary: &TermStore,
        expected: &Sort,
        value: &FpModelValue,
    ) -> Result<bool, UnknownOrigin> {
        self.poll(Some(temporary))?;
        let &Sort::FloatingPoint(eb, sb) = expected else {
            return Ok(false);
        };
        if (eb, sb) != (value.eb(), value.sb())
            || !(2..=ay_fp::MAX_ENCODING_EXPONENT_BITS).contains(&eb)
            || !(2..=ay_fp::MAX_ENCODING_SIGNIFICAND_BITS).contains(&sb)
        {
            return Ok(false);
        }
        // Precharge owned field copies and local term payloads in the SAME
        // live arena. Actual store capacity is still polled after insertion;
        // this is the existing term ledger, not a hard allocator/RSS promise.
        let Some(scratch) = Executor::fp_model_clone_scratch_bytes(value) else {
            return Ok(false);
        };
        let temporary_bytes = temporary
            .true_memory_bytes()
            .checked_add(scratch)
            .ok_or_else(|| self.record(UnknownOrigin::MemoryBudget))?;
        if let Some(limit) = self.executor.evaluation_term_memory_limit() {
            self.arena
                .check_usage(
                    self.executor.ctx.terms.true_memory_bytes(),
                    temporary_bytes,
                    Some(limit),
                )
                .map_err(|origin| self.record(origin))?;
        }
        Ok(true)
    }

    fn record(&self, origin: UnknownOrigin) -> UnknownOrigin {
        self.attempt.record_stop(self.stop.refuse(origin))
    }

    fn build_error(&self, error: FpBuildError) -> UnknownOrigin {
        self.record(self.stop.refuse_build_error(error))
    }

    fn poll(&self, temporary: Option<&TermStore>) -> Result<(), UnknownOrigin> {
        if let Some(origin) = self.attempt.stop_origin() {
            return Err(origin);
        }
        self.stop.check().map_err(|origin| self.record(origin))?;
        if let Some(limit) = self.executor.evaluation_term_memory_limit() {
            self.arena.check_usage(
                self.executor.ctx.terms.true_memory_bytes(),
                temporary.map_or(0, TermStore::true_memory_bytes),
                Some(limit),
            )?;
        }
        Ok(())
    }

    fn phase(
        &self,
        temporary: Option<&TermStore>,
        phase: FpEvalPhase,
    ) -> Result<(), UnknownOrigin> {
        self.poll(temporary)?;
        (self.observe)(phase);
        self.poll(temporary)
    }
}

impl Executor {
    /// A resource error is recorded before returning, never erased as an
    /// unavailable operand. The caller owns the evaluation lifetime; this
    /// helper neither creates a fresh allowance nor rearms a stopped attempt.
    pub(in crate::executor) fn evaluate_fp_term_via_bitblast_controlled(
        &self,
        model: &Model,
        term_id: TermId,
        observe: &impl Fn(FpEvalPhase),
    ) -> Result<Option<FpModelValue>, UnknownOrigin> {
        let attempt = self.evaluation_attempt();
        let stop = FpStop::from_executor(self);
        if let Some(origin) = attempt.stop_origin() {
            return Err(self.record_evaluation_stop(origin));
        }
        stop.check()
            .map_err(|origin| self.record_evaluation_stop(origin))?;
        let arena = attempt.temporary_arena()?;
        let control = Control {
            executor: self,
            stop,
            attempt,
            arena,
            observe,
        };
        let result = (|| {
            // Cold capacity accounting precedes the fresh arena allocation.
            control.poll(None)?;
            if !matches!(self.ctx.terms.sort(term_id), Sort::FloatingPoint(..)) {
                return Ok(None);
            }
            let mut concrete_terms = TermStore::new();
            let mut cache = HashMap::default();
            let concrete = self.concretize_term_for_fp_eval_controlled(
                model,
                term_id,
                &mut concrete_terms,
                &mut cache,
                &control,
            )?;
            let result = match concrete {
                Some(term) => self.solve_concrete_fp_eval(&concrete_terms, term, &control),
                None => Ok(None),
            };
            // Release all temporary owners before final result admission.
            drop(cache);
            drop(concrete_terms);
            result
        })();
        if let Err(origin) = result.as_ref() {
            control.record(*origin);
        }
        control.phase(None, FpEvalPhase::Cleanup)?;
        result.map_err(|origin| self.record_evaluation_stop(origin))
    }

    fn solve_concrete_fp_eval(
        &self,
        terms: &TermStore,
        term: TermId,
        control: &Control<'_>,
    ) -> Result<Option<FpModelValue>, UnknownOrigin> {
        control.poll(Some(terms))?;
        let solver = FpSolver::new(terms);
        control.poll(Some(terms))?;
        let mut should_stop = |progress| {
            control
                .phase(Some(terms), FpEvalPhase::Construction(progress))
                .is_err()
        };
        let mut fp = FpConstruction::new(solver, &mut should_stop)
            .map_err(|error| control.build_error(error))?;
        fp.try_get_fp(term)
            .map_err(|error| control.build_error(error))?;
        let mut built = fp.finish().map_err(|error| control.build_error(error))?;
        if built.has_encoding_gap || !built.pending_condition_links.is_empty() {
            return Ok(None);
        }
        control.phase(Some(terms), FpEvalPhase::Namespace)?;
        let namespace =
            FpNamespace::new(0, built.cache.next_var).map_err(|origin| control.record(origin))?;
        // Only the requested result is decoded. No partial/raw cache getters
        // or complete-map clone is needed for a completed concrete value.
        let Some(decomposed) = built.cache.term_to_fp.remove(&term) else {
            return Ok(None);
        };
        control.phase(Some(terms), FpEvalPhase::SatLoad)?;
        let mut sat = SatSolver::new(namespace.total_vars() as usize);
        sat.set_congruence_enabled(false);
        for clause in built.clauses {
            control.phase(Some(terms), FpEvalPhase::ClauseTransfer)?;
            let mut literals = Vec::new();
            for (index, &lit) in clause.literals().iter().enumerate() {
                if index % 256 == 0 {
                    control.poll(Some(terms))?;
                }
                literals.push(crate::cnf_lit_to_sat(lit));
            }
            control.phase(Some(terms), FpEvalPhase::SatLoad)?;
            sat.add_clause(literals);
            control.poll(Some(terms))?;
        }
        drop(built.cache);
        self.arm_sat_count_budget(&mut sat, control.attempt.consumed_spend());
        control.phase(Some(terms), FpEvalPhase::SatSearch)?;
        let result = sat
            .solve_interruptible(|| control.phase(Some(terms), FpEvalPhase::SatPoll).is_err())
            .into_inner();
        control.attempt.debit_solve(&sat);
        if matches!(result, SatResult::Unknown) {
            if let Some(reason) = sat.last_unknown_reason() {
                let origin = Self::map_sat_unknown_origin(reason);
                if matches!(
                    origin,
                    UnknownOrigin::InterruptFlag
                        | UnknownOrigin::SolveDeadline
                        | UnknownOrigin::MemoryBudget
                        | UnknownOrigin::DeterministicResourceBudget
                ) {
                    control.record(origin);
                }
            }
        }
        // The SAT reason has already been latched, so an observer clearing the
        // live source here cannot revive this attempt or authorize decoding.
        (control.observe)(FpEvalPhase::SatReturned);
        control.poll(Some(terms))?;
        match result {
            SatResult::Sat(model) => decode::root(terms, term, decomposed, &model, control),
            _ => Ok(None),
        }
    }
}
