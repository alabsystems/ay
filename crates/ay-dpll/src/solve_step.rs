// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Step-mode solve paths extracted from `lib.rs`.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::time::Instant;
use ay_core::{TermId, TheoryResult, TheorySolver};
use ay_sat::SatResult;

use crate::{
    dpll_support::PhaseTimer, extension, proof_tracker, DpllError, DpllT, FinalCheckResult,
    SolveStepResult, TheoryDispatch,
};

impl<T: TheorySolver> DpllT<'_, T> {
    /// Executes one solving round and returns the next action the caller must take.
    #[must_use = "solve step results must be matched — NeedSplit requires action"]
    pub fn solve_step(&mut self) -> Result<SolveStepResult, DpllError> {
        let mut refinements = 0usize;
        loop {
            self.timings.round_trips += 1;
            let result = {
                let _t = PhaseTimer::new(&mut self.timings.sat_solve);
                // Use a phase-hint extension so the theory solver's suggest_phase
                // guides SAT decisions. Without this, the bare solve() path uses
                // only SAT-internal phase-saving, missing theory-level guidance
                // like "index equalities default to false" (#6282).
                let mut ext = extension::PhaseHintExtension::new(
                    &self.theory,
                    &self.var_to_term,
                    &self.term_to_var,
                    &self.theory_atoms,
                );
                self.sat.solve_with_extension(&mut ext).into_inner()
            };
            match result {
                SatResult::Sat(model) => {
                    {
                        let start = Instant::now();
                        self.sync_theory(&model);
                        self.timings.theory_sync += start.elapsed();
                    }
                    let check = {
                        let start = Instant::now();
                        let result = self.check_theory();
                        self.timings.theory_check += start.elapsed();
                        result
                    };
                    let dispatch = self.dispatch_theory_check(check, true);
                    if matches!(dispatch, TheoryDispatch::Accept) {
                        // (#6825) Run the full N-O fixpoint before accepting.
                        match self.run_final_check_if_needed() {
                            FinalCheckResult::Accept => {
                                let pending_bound_refinements =
                                    self.theory.take_bound_refinements();
                                if !pending_bound_refinements.is_empty() {
                                    self.exit_model_scope_if_active();
                                    return Ok(SolveStepResult::NeedBoundRefinements(
                                        pending_bound_refinements,
                                    ));
                                }
                            }
                            FinalCheckResult::Unknown => {
                                self.exit_model_scope_if_active();
                                return Ok(SolveStepResult::Done(SatResult::Unknown));
                            }
                            FinalCheckResult::Conflict => {
                                self.theory_conflict_count += 1;
                                refinements += 1;
                                if refinements >= Self::MAX_THEORY_REFINEMENTS {
                                    self.exit_model_scope_if_active();
                                    return Ok(SolveStepResult::Done(SatResult::Unknown));
                                }
                                continue;
                            }
                        }
                    }
                    if let Some(result) = dispatch.into_solve_step(model) {
                        // Keep model scope active on SAT so callers can extract
                        // theory model with bounds intact (#5405).
                        if !matches!(result, SolveStepResult::Done(SatResult::Sat(_))) {
                            self.exit_model_scope_if_active();
                        }
                        return Ok(result);
                    }
                    refinements += 1;
                    if refinements >= Self::MAX_THEORY_REFINEMENTS {
                        self.exit_model_scope_if_active();
                        return Ok(SolveStepResult::Done(SatResult::Unknown));
                    }
                }
                SatResult::Unsat(cert) => {
                    self.exit_model_scope_if_active();
                    return Ok(SolveStepResult::Done(SatResult::Unsat(cert)));
                }
                SatResult::Unknown => {
                    self.exit_model_scope_if_active();
                    return Ok(SolveStepResult::Done(SatResult::Unknown));
                }
                #[allow(unreachable_patterns)]
                _ => return Err(DpllError::UnexpectedTheoryResult),
            }
        }
    }

    /// Interruptible variant of [`Self::solve_step`].
    ///
    /// The callback is polled frequently by the SAT solver. Returning `true`
    /// causes the SAT phase to stop and this method to return `Unknown`.
    ///
    /// No production callers remain after the LIA legacy path deletion (#6661).
    /// Kept for test coverage of the interruptible solve path.
    #[cfg(test)]
    pub(crate) fn solve_step_interruptible<F>(
        &mut self,
        should_stop: F,
    ) -> Result<SolveStepResult, DpllError>
    where
        F: Fn() -> bool,
    {
        let mut refinements = 0usize;
        loop {
            if should_stop() {
                self.exit_model_scope_if_active();
                return Ok(SolveStepResult::Done(SatResult::Unknown));
            }
            self.timings.round_trips += 1;
            let result = {
                if self.sat.scope_depth() == 0 {
                    let _t = PhaseTimer::new(&mut self.timings.sat_solve);
                    let mut ext = extension::PhaseHintExtension::new(
                        &self.theory,
                        &self.var_to_term,
                        &self.term_to_var,
                        &self.theory_atoms,
                    );
                    self.sat
                        .solve_interruptible_with_extension(&mut ext, &should_stop)
                        .into_inner()
                } else {
                    self.apply_theory_phase_hints();
                    let _t = PhaseTimer::new(&mut self.timings.sat_solve);
                    self.sat.solve_interruptible(&should_stop).into_inner()
                }
            };
            match result {
                SatResult::Sat(model) => {
                    {
                        let start = Instant::now();
                        self.sync_theory(&model);
                        self.timings.theory_sync += start.elapsed();
                    }
                    let check = {
                        let start = Instant::now();
                        let result = self.check_theory();
                        self.timings.theory_check += start.elapsed();
                        result
                    };
                    let dispatch = self.dispatch_theory_check(check, true);
                    if matches!(dispatch, TheoryDispatch::Accept) {
                        let pending_bound_refinements = self.theory.take_bound_refinements();
                        if !pending_bound_refinements.is_empty() {
                            self.exit_model_scope_if_active();
                            return Ok(SolveStepResult::NeedBoundRefinements(
                                pending_bound_refinements,
                            ));
                        }
                    }
                    if let Some(result) = dispatch.into_solve_step(model) {
                        if !matches!(result, SolveStepResult::Done(SatResult::Sat(_))) {
                            self.exit_model_scope_if_active();
                        }
                        return Ok(result);
                    }
                    refinements += 1;
                    if refinements >= Self::MAX_THEORY_REFINEMENTS {
                        self.exit_model_scope_if_active();
                        return Ok(SolveStepResult::Done(SatResult::Unknown));
                    }
                    if should_stop() {
                        self.exit_model_scope_if_active();
                        return Ok(SolveStepResult::Done(SatResult::Unknown));
                    }
                }
                SatResult::Unsat(cert) => {
                    self.exit_model_scope_if_active();
                    return Ok(SolveStepResult::Done(SatResult::Unsat(cert)));
                }
                SatResult::Unknown => {
                    self.exit_model_scope_if_active();
                    return Ok(SolveStepResult::Done(SatResult::Unknown));
                }
                #[allow(unreachable_patterns)]
                _ => return Err(DpllError::UnexpectedTheoryResult),
            }
        }
    }

    /// Step-mode solver used by eager theory propagation pipelines.
    ///
    /// When `tracking` is `Some`, records theory conflict steps into the proof tracker.
    pub(crate) fn solve_eager_step(
        &mut self,
        tracking: Option<(&mut proof_tracker::ProofTracker, &HashMap<TermId, TermId>)>,
    ) -> Result<SolveStepResult, DpllError> {
        // #2138: Use soft_reset() instead of reset() to preserve learned theory
        // state (HNF cuts, Diophantine analysis, cached atom parses) across
        // solve_eager_step iterations. The full reset() was discarding valuable
        // learned state on every call. soft_reset() clears assertion state while
        // retaining learned artifacts.
        self.theory.soft_reset();

        // Pre-register all theory atoms for eager propagation.
        for &atom in &self.theory_atoms {
            self.theory.internalize_atom(atom);
        }

        // T3: forward the solve deadline so propagate_impl() can terminate a
        // diverging theory churn. This path calls the NON-interruptible
        // solve_with_extension() below, so the propagate-level poll is the only
        // wall-clock guard it has (see propagate.rs).
        let deadline = self.solve_deadline;
        // Combined (dt ++ ematching) conflict-verification support, computed
        // before the `&mut self.theory` / `&mut self.construction_timings`
        // borrows below.
        let support_axioms = self.combined_support_axioms();
        let ext = extension::TheoryExtension::new_with_construction_timings(
            &mut self.theory,
            &self.var_to_term,
            &self.term_to_var,
            &self.theory_atoms,
            &self.theory_atom_set,
            self.terms,
            self.diagnostic_trace.as_ref(),
            Some(&mut self.construction_timings),
        )
        .with_solve_deadline(deadline)
        .with_support_axioms(support_axioms);
        let mut ext = match tracking {
            Some((tracker, negations)) => ext.with_proof_tracking(tracker, negations),
            None => ext,
        };

        let result = {
            // Time the eager SAT+theory solve (#6503). The lazy paths already
            // wrap their solve calls with PhaseTimer; the eager path was missing
            // this, causing time.dpll.sat_solve to report 0.00 for QF_LRA.
            let _t = PhaseTimer::new(&mut self.timings.sat_solve);
            self.sat.solve_with_extension(&mut ext).into_inner()
        };
        self.theory_conflict_count += ext.num_theory_conflicts();
        self.theory_propagation_count += ext.num_theory_propagations();
        self.eager_stats.accumulate_from(ext.eager_stats());
        let new_partial = ext.num_partial_clauses();
        let pending_bound_refinements = ext.take_pending_bound_refinements();
        let pending_split = ext.take_pending_split();
        self.partial_clause_count += new_partial;
        // Drop extension to release borrow on self.theory before final check (#5462).
        drop(ext);

        Ok(match result {
            SatResult::Sat(model) => {
                if new_partial > 0 {
                    // Partial clauses mean the eager BCP dropped theory
                    // conflicts referencing terms not yet in term_to_var.
                    // Instead of escalating to Unknown (#4666), fall back
                    // to the lazy solve_step path which dynamically
                    // registers unmapped terms in check_theory_core (#6546).
                    // The eager BCP already added useful theory clauses to
                    // the SAT solver; solve_step will benefit from them.
                    tracing::debug!(
                        partial_clauses = new_partial,
                        "Eager step produced SAT with partial clauses; falling back to solve_step"
                    );
                    SolveStepResult::Done(SatResult::Unknown)
                } else if self.theory.needs_final_check_after_sat() {
                    // Combined theories use a cheap BCP-time check; run the
                    // full Nelson-Oppen fixpoint once on the candidate model.
                    let full_result = self.theory.check();
                    match full_result {
                        TheoryResult::Sat => {
                            if let Some(split) = pending_split {
                                Self::theory_result_to_step(split)
                            } else if !pending_bound_refinements.is_empty() {
                                SolveStepResult::NeedBoundRefinements(pending_bound_refinements)
                            } else {
                                // #7912: Assert model integrity after eager
                                // SAT + full N-O fixpoint acceptance.
                                debug_assert!(
                                    !model.is_empty(),
                                    "BUG: eager step returning empty SAT model \
                                     after theory acceptance"
                                );
                                SolveStepResult::Done(SatResult::Sat(model))
                            }
                        }
                        other => Self::theory_result_to_step(other),
                    }
                } else if let Some(split) = pending_split {
                    Self::theory_result_to_step(split)
                } else if !pending_bound_refinements.is_empty() {
                    SolveStepResult::NeedBoundRefinements(pending_bound_refinements)
                } else {
                    // #7912: Assert model integrity for eager step
                    // non-final-check path.
                    debug_assert!(
                        !model.is_empty(),
                        "BUG: eager step returning empty SAT model"
                    );
                    SolveStepResult::Done(SatResult::Sat(model))
                }
            }
            SatResult::Unsat(cert) => SolveStepResult::Done(SatResult::Unsat(cert)),
            SatResult::Unknown => {
                if let Some(split) = pending_split {
                    Self::theory_result_to_step(split)
                } else if !pending_bound_refinements.is_empty() {
                    SolveStepResult::NeedBoundRefinements(pending_bound_refinements)
                } else {
                    SolveStepResult::Done(SatResult::Unknown)
                }
            }
            #[allow(unreachable_patterns)]
            _ => return Err(DpllError::UnexpectedTheoryResult),
        })
    }
}
