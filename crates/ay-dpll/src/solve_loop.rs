// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core DPLL(T) solve-loop implementations shared across public entrypoints.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::time::Instant;
use ay_core::{TermId, TheorySolver};
use ay_sat::{AssumeResult, Literal, SatResult};
use std::time::Duration;

use crate::{
    dpll_support::PhaseTimer, proof_tracker, DpllError, DpllT, FinalCheckResult, TheoryDispatch,
};

impl<T: TheorySolver> DpllT<'_, T> {
    /// Internal solve loop used by `solve`, `solve_with_assumptions`, and
    /// their proof-tracking variants.
    ///
    /// Returns `AssumeResult` to propagate unsat core when using assumptions.
    /// When `tracking` is `Some`, records theory conflict steps into the proof tracker.
    pub(crate) fn solve_loop(
        &mut self,
        assumptions: Option<&[Literal]>,
        mut tracking: Option<(&mut proof_tracker::ProofTracker, &HashMap<TermId, TermId>)>,
    ) -> Result<AssumeResult, DpllError> {
        let mut refinements = 0usize;
        // Build the cooperative stop closure ONCE from the installed solve
        // controls (see `set_solve_controls`). Cloned per SAT call because the
        // interruptible entries take the closure by value.
        let ctrl_interrupt = self.solve_interrupt.clone();
        let ctrl_deadline = self.solve_deadline;
        let make_should_stop = move || {
            let interrupt = ctrl_interrupt.clone();
            move || {
                interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                    || ctrl_deadline.is_some_and(|deadline| Instant::now() >= deadline)
            }
        };
        loop {
            // Round-trip budget check: a non-converging refinement loop is a
            // sequence of FULL SAT solves, so `MAX_THEORY_REFINEMENTS` alone is
            // wall-clock-unbounded. Mirror that exit exactly (scope cleanup +
            // Unknown, which the caller classifies via interrupt/deadline).
            if self.solve_controls_tripped() {
                self.exit_model_scope_if_active();
                return Ok(AssumeResult::Unknown);
            }
            self.timings.round_trips += 1;
            let round = self.timings.round_trips;

            let sat_start = Instant::now();
            let result = match assumptions {
                Some(a) => {
                    self.apply_theory_phase_hints();
                    let _t = PhaseTimer::new(&mut self.timings.sat_solve);
                    // The assumption entry takes no `should_stop` closure; the
                    // interrupt flag installed by `set_solve_controls` is
                    // honored at the assumption CDCL loop top instead, and the
                    // deadline is enforced by the round-trip check above.
                    self.sat.solve_with_assumptions(a).into_inner()
                }
                None if self.sat.scope_depth() == 0 => {
                    let _t = PhaseTimer::new(&mut self.timings.sat_solve);
                    let mut ext = crate::extension::PhaseHintExtension::new(
                        &self.theory,
                        &self.var_to_term,
                        &self.term_to_var,
                        &self.theory_atoms,
                    );
                    match self
                        .sat
                        .solve_interruptible_with_extension(&mut ext, make_should_stop())
                        .into_inner()
                    {
                        SatResult::Sat(m) => AssumeResult::Sat(m),
                        SatResult::Unsat(_) => AssumeResult::Unsat(vec![], None),
                        SatResult::Unknown => AssumeResult::Unknown,
                        #[allow(unreachable_patterns)]
                        _ => return Err(DpllError::UnexpectedTheoryResult),
                    }
                }
                None => {
                    // #8423: Use full TheoryExtension (eager propagation) for
                    // scoped (nonzero scope depth) solving. Previously this used
                    // only PhaseHintExtension (phase hints + theory-aware
                    // branching, no eager propagation). Now the assumption-based
                    // CDCL loop runs the full extension callbacks (propagate,
                    // check, backtrack, suggest), matching the eager theory
                    // integration of the scope_depth==0 path.
                    //
                    // This is safe because:
                    // 1. TheoryExtension::backtrack() handles nested push/pop
                    //    via level_trail_positions stack (#5548)
                    // 2. The assumption-based loop notifies the extension of
                    //    backtrack events after conflict analysis
                    // 3. Extension::init() resets theory state at solve start
                    // 4. solve_with_extension() now supports scoped contexts
                    //    via the eager_ext parameter in the assumption loop
                    // T3: forward the solve deadline so propagate_impl() can
                    // terminate a diverging theory churn (see propagate.rs).
                    let deadline = self.solve_deadline;
                    // Combined (dt ++ ematching) conflict-verification support,
                    // computed before the `&mut self.timings` / `&mut self.theory`
                    // borrows below.
                    let support_axioms = self.combined_support_axioms();
                    let _t = PhaseTimer::new(&mut self.timings.sat_solve);
                    let mut ext = crate::extension::TheoryExtension::new(
                        &mut self.theory,
                        &self.var_to_term,
                        &self.term_to_var,
                        &self.theory_atoms,
                        &self.theory_atom_set,
                        self.terms,
                        self.diagnostic_trace.as_ref(),
                    )
                    .with_solve_deadline(deadline)
                    .with_support_axioms(support_axioms);
                    match self
                        .sat
                        .solve_interruptible_with_extension(&mut ext, make_should_stop())
                        .into_inner()
                    {
                        SatResult::Sat(m) => AssumeResult::Sat(m),
                        SatResult::Unsat(_) => AssumeResult::Unsat(vec![], None),
                        SatResult::Unknown => AssumeResult::Unknown,
                        #[allow(unreachable_patterns)]
                        _ => return Err(DpllError::UnexpectedTheoryResult),
                    }
                }
            };
            let sat_duration = sat_start.elapsed();

            match result {
                AssumeResult::Sat(model) => {
                    if self.debug_dpll {
                        safe_eprintln!("[DPLL] SAT returned model with {} vars", model.len());
                    }
                    let sync_start = Instant::now();
                    self.sync_theory(&model);
                    let sync_duration = sync_start.elapsed();
                    self.timings.theory_sync += sync_duration;

                    let check_start = Instant::now();
                    let check =
                        self.check_theory_core(tracking.as_mut().map(|(t, n)| (&mut **t, *n)));
                    let check_duration = check_start.elapsed();
                    self.timings.theory_check += check_duration;
                    let (propagations_added, conflict_size) = Self::check_metrics(&check);
                    let dispatch = self.dispatch_theory_check(check, false);
                    let (check_label, action) = Self::dispatch_label(&dispatch);
                    self.emit_dpll_round_event(
                        round,
                        "sat",
                        sat_duration,
                        sync_duration,
                        check_label,
                        check_duration,
                        propagations_added,
                        conflict_size,
                        action,
                    );
                    match dispatch {
                        TheoryDispatch::Accept => match self.run_final_check_if_needed() {
                            FinalCheckResult::Accept => {
                                // #7912: Assert model integrity at DPLL solve_loop
                                // boundary. SAT solver verified via finalize_sat_model;
                                // theory solver accepted via check(). This structural
                                // check guards the SAT+theory->caller handoff.
                                debug_assert!(
                                    !model.is_empty() || self.theory_atoms.is_empty(),
                                    "BUG: DPLL solve_loop returning empty SAT model \
                                     with {} theory atoms",
                                    self.theory_atoms.len(),
                                );
                                return Ok(AssumeResult::Sat(model));
                            }
                            FinalCheckResult::Unknown => {
                                self.exit_model_scope_if_active();
                                return Ok(AssumeResult::Unknown);
                            }
                            FinalCheckResult::Conflict => {
                                self.theory_conflict_count += 1;
                                refinements += 1;
                                if refinements >= Self::MAX_THEORY_REFINEMENTS {
                                    self.exit_model_scope_if_active();
                                    return Ok(AssumeResult::Unknown);
                                }
                                continue;
                            }
                        },
                        TheoryDispatch::Unknown => {
                            self.exit_model_scope_if_active();
                            return Ok(AssumeResult::Unknown);
                        }
                        TheoryDispatch::Continue => {
                            refinements += 1;
                            if refinements >= Self::MAX_THEORY_REFINEMENTS {
                                self.exit_model_scope_if_active();
                                return Ok(AssumeResult::Unknown);
                            }
                            continue;
                        }
                        _ => return Err(DpllError::UnexpectedTheoryResult),
                    }
                }
                AssumeResult::Unsat(core, _) => {
                    self.exit_model_scope_if_active();
                    self.emit_dpll_round_event(
                        round,
                        "unsat",
                        sat_duration,
                        Duration::ZERO,
                        "sat_unsat",
                        Duration::ZERO,
                        0,
                        0,
                        Some("DeclareUnsat"),
                    );
                    return Ok(AssumeResult::Unsat(core, None));
                }
                AssumeResult::Unknown => {
                    self.exit_model_scope_if_active();
                    self.emit_dpll_round_event(
                        round,
                        "unknown",
                        sat_duration,
                        Duration::ZERO,
                        "sat_unknown",
                        Duration::ZERO,
                        0,
                        0,
                        Some("DeclareUnknown"),
                    );
                    return Ok(AssumeResult::Unknown);
                }
                #[allow(unreachable_patterns)]
                _ => return Err(DpllError::UnexpectedTheoryResult),
            }
        }
    }
}
