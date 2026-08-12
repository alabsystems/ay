// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DPLL(T) solve entry points and incremental scope management.
//!
//! Extracted from `lib.rs` — contains the public `solve`, `solve_with_assumptions`,
//! `push`/`pop`/`reset_theory` methods and their internal helpers.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{TermId, TheorySolver};
use ay_sat::{AssumeResult, Literal, SatResult};

use crate::{proof_tracker, DpllError, DpllT};

impl<T: TheorySolver> DpllT<'_, T> {
    /// Pop the internal model-scope `push()` if one is active.
    ///
    /// Called before every return from a solve method and before any public
    /// scope-mutating operation (`push`, `pop`, `reset_theory`) to maintain
    /// the invariant that internal model scopes never leak past API boundaries (#4520).
    pub(crate) fn exit_model_scope_if_active(&mut self) {
        if self.model_scope_active {
            self.theory.pop();
            self.model_scope_active = false;
        }
        // Clear cached theory atom values when exiting model scope so that
        // the next sync_theory call performs a full assertion (#2138).
        self.prev_theory_atom_values = None;
    }

    /// Communicate SAT model to theory solver
    ///
    /// IMPORTANT: We use the model returned by the SAT solver, not the live assignment.
    /// The model has defaults applied for unassigned variables (via get_model()), whereas
    /// the live assignment may have None values. Using the model ensures the theory solver
    /// sees a complete, consistent assignment.
    ///
    /// Instead of calling `soft_reset()` (which discards all theory state), we use
    /// scope-based `push/pop` to undo only the model-level assertions from the
    /// previous round. This preserves learned theory state (e.g. simplex tableau
    /// structure, cached atom parses) across SAT model iterations (#4520).
    ///
    /// Optimization (#2138): When consecutive SAT models assign the same truth values
    /// to all theory atoms (only Tseitin encoding vars differ), we skip the expensive
    /// pop+push+re-assert cycle entirely. The theory solver already has the correct
    /// state from the previous round.
    pub(crate) fn sync_theory(&mut self, model: &[bool]) {
        let n = self.theory_atoms.len();

        // Fast path: check if theory atom values are identical to previous model.
        // When only Tseitin vars change between SAT models, the theory state is
        // already correct and we can skip the expensive pop+push+re-assert (#2138).
        if let Some(ref prev) = self.prev_theory_atom_values {
            if self.theory_atoms_unchanged_vec(prev, model) {
                self.sync_skipped_identical += 1;
                return;
            }
        }

        // Save prev values BEFORE exit_model_scope clears them (for delta stats).
        let saved_prev = self.prev_theory_atom_values.take();

        // Pop previous model scope if active, then push a fresh one.
        self.exit_model_scope_if_active();
        self.theory.push();
        self.model_scope_active = true;

        // Build current theory atom values and assert to theory solver.
        // Uses Vec<bool> indexed by theory_atoms position to avoid HashMap overhead.
        let debug = self.debug_sync;
        let mut current_values = Vec::with_capacity(n);
        for (idx, &term) in self.theory_atoms.iter().enumerate() {
            if let Some(var) = self.var_for_term(term) {
                let var_idx = var.index();
                let value = if var_idx < model.len() {
                    model[var_idx]
                } else {
                    false
                };
                current_values.push(value);

                // Track per-atom delta statistics for observability (#2138).
                if let Some(ref prev) = saved_prev {
                    if idx < prev.len() && prev[idx] == value {
                        self.sync_delta_unchanged += 1;
                    } else {
                        self.sync_delta_changed += 1;
                    }
                }

                if debug {
                    safe_eprintln!(
                        "[SYNC] term {:?} (var {:?}) = {} (from model)",
                        term,
                        var,
                        value
                    );
                }
                self.theory.assert_literal(term, value);
                self.sync_atoms_asserted += 1;
            } else {
                current_values.push(false);
            }
        }
        self.prev_theory_atom_values = Some(current_values);
    }

    /// Check if all theory atom values in the current model match the previous model.
    ///
    /// O(n) comparison where n = number of theory atoms. Uses `Vec<bool>` indexed
    /// by position in `theory_atoms` to avoid HashMap lookup overhead.
    fn theory_atoms_unchanged_vec(&self, prev: &[bool], model: &[bool]) -> bool {
        for (idx, &term) in self.theory_atoms.iter().enumerate() {
            if let Some(var) = self.var_for_term(term) {
                let var_idx = var.index();
                let cur_value = if var_idx < model.len() {
                    model[var_idx]
                } else {
                    false
                };
                if idx >= prev.len() || prev[idx] != cur_value {
                    return false;
                }
            }
        }
        true
    }

    /// Solve the formula using DPLL(T)
    ///
    /// Note: This basic solve method returns Unknown if the theory requires
    /// splitting (branch-and-bound for LIA). The executor handles splits via
    /// `solve_step()` + `NeedSplit` return variant.
    ///
    /// Remains `pub` (not `pub(crate)`) because integration tests in `tests/`
    /// exercise this method directly. No production callers outside ay-dpll exist;
    /// the Executor layer (via `check_sat()`) is the validated entry point for
    /// external consumers. Part of #5793.
    /// Internal implementation shared by `solve` and `solve_with_proof_tracking`.
    fn solve_impl(
        &mut self,
        tracking: Option<(&mut proof_tracker::ProofTracker, &HashMap<TermId, TermId>)>,
    ) -> Result<SatResult, DpllError> {
        // Clear residual model scope before reset (#4520).
        self.exit_model_scope_if_active();
        self.theory.reset();

        let result = match self.solve_loop(None, tracking)? {
            AssumeResult::Sat(model) => {
                // #7912: Belt-and-suspenders assertion at DPLL layer boundary.
                // The SAT solver already verified this model via finalize_sat_model
                // (always-on) and verify_external_model (debug_assert). This
                // structural check catches corruption in the SAT->DPLL handoff.
                debug_assert!(
                    !model.is_empty() || self.theory_atoms.is_empty(),
                    "BUG: DPLL solve_impl received empty SAT model with {} theory atoms",
                    self.theory_atoms.len(),
                );
                SatResult::Sat(model)
            }
            AssumeResult::Unsat(..) => SatResult::Unsat(ay_sat::ProofCertificate::empty()),
            AssumeResult::Unknown => SatResult::Unknown,
            #[allow(unreachable_patterns)]
            _ => return Err(DpllError::UnexpectedTheoryResult),
        };
        let summary = match &result {
            SatResult::Sat(_) => "sat",
            SatResult::Unsat(_) => "unsat",
            SatResult::Unknown => "unknown",
            #[allow(unreachable_patterns)]
            _ => "unknown",
        };
        self.emit_solve_summary_event(summary);
        self.finish_dpll_tla_trace();
        Ok(result)
    }

    /// Solve using DPLL(T), returning the final result.
    ///
    /// Returns `Unknown` if the theory requires splitting (branch-and-bound for LIA).
    /// The executor handles splits via `solve_step()` + `NeedSplit`.
    #[must_use = "solve results must be checked — ignoring Sat/Unsat loses correctness"]
    pub fn solve(&mut self) -> Result<SatResult, DpllError> {
        self.solve_impl(None)
    }

    /// Solve while recording theory lemmas into a proof tracker.
    ///
    /// Records theory conflict clauses as `TheoryLemma` steps for Alethe export (#328).
    #[cfg(test)]
    pub(crate) fn solve_with_proof_tracking(
        &mut self,
        tracker: &mut proof_tracker::ProofTracker,
        negations: &HashMap<TermId, TermId>,
    ) -> Result<SatResult, DpllError> {
        self.solve_impl(Some((tracker, negations)))
    }

    /// Internal implementation shared by `solve_with_assumptions` and
    /// `solve_with_assumptions_and_proof_tracking`.
    fn solve_with_assumptions_impl(
        &mut self,
        assumptions: &[Literal],
        tracking: Option<(&mut proof_tracker::ProofTracker, &HashMap<TermId, TermId>)>,
    ) -> Result<AssumeResult, DpllError> {
        self.exit_model_scope_if_active();
        self.theory.reset();
        // #8599: Pass borrowed slice directly — solve_loop takes &[Literal],
        // so the prior .to_vec() was an unnecessary per-solve copy.
        let result = self.solve_loop(Some(assumptions), tracking)?;
        let summary = match &result {
            AssumeResult::Sat(_) => "sat",
            AssumeResult::Unsat(..) => "unsat",
            AssumeResult::Unknown => "unknown",
            #[allow(unreachable_patterns)]
            _ => "unknown",
        };
        self.emit_solve_summary_event(summary);
        self.finish_dpll_tla_trace();
        Ok(result)
    }

    /// Solve with assumptions using DPLL(T).
    ///
    /// Like `solve()` but activates only clauses whose selectors are in the
    /// positive assumptions. Returns `AssumeResult` with unsat core when UNSAT.
    pub(crate) fn solve_with_assumptions(
        &mut self,
        assumptions: &[Literal],
    ) -> Result<AssumeResult, DpllError> {
        self.solve_with_assumptions_impl(assumptions, None)
    }

    /// Solve with assumptions while tracking proofs.
    ///
    /// Used for `check-sat-assuming` when `:produce-proofs` is enabled.
    pub(crate) fn solve_with_assumptions_and_proof_tracking(
        &mut self,
        assumptions: &[Literal],
        tracker: &mut proof_tracker::ProofTracker,
        negations: &HashMap<TermId, TermId>,
    ) -> Result<AssumeResult, DpllError> {
        self.solve_with_assumptions_impl(assumptions, Some((tracker, negations)))
    }

    /// Reset the theory solver. Call this before starting a new solve session.
    /// Uses soft_reset() to preserve learned state (e.g., HNF cuts in LIA).
    pub fn reset_theory(&mut self) {
        self.exit_model_scope_if_active();
        self.theory.soft_reset();
    }

    // ========================================================================
    // Incremental Solving (Push/Pop)
    // ========================================================================

    /// Push a new assertion scope.
    ///
    /// All clauses added after this push will be removed when `pop()` is called.
    /// This enables incremental solving where you can add temporary constraints,
    /// solve, and then restore the original state.
    ///
    /// # Example
    /// ```no_run
    /// use ay_core::{TermId, TheoryPropagation, TheoryResult, TheorySolver};
    /// use ay_dpll::DpllT;
    /// use ay_sat::Literal;
    ///
    /// # #[derive(Clone, Copy)]
    /// # struct DummyTheory;
    /// # impl TheorySolver for DummyTheory {
    /// #     fn assert_literal(&mut self, _literal: TermId, _value: bool) {}
    /// #     fn check(&mut self) -> TheoryResult { TheoryResult::Sat }
    /// #     fn propagate(&mut self) -> Vec<TheoryPropagation> { Vec::new() }
    /// #     fn push(&mut self) {}
    /// #     fn pop(&mut self) {}
    /// #     fn reset(&mut self) {}
    /// # }
    ///
    /// let mut dpll = DpllT::new(10, DummyTheory);
    /// let base_clause: Vec<Literal> = vec![]; // Permanent
    /// let temp_clause: Vec<Literal> = vec![]; // Will be removed by pop()
    ///
    /// dpll.add_clause(base_clause);
    /// dpll.push();
    /// dpll.add_clause(temp_clause);
    /// let _result = dpll.solve();
    /// dpll.pop(); // temp_clause is now inactive
    /// ```
    ///
    /// # Invariants
    /// - INV-PUSH-1: After push(), scope depth increases by 1
    /// - INV-PUSH-2: SAT solver and theory solver scopes are synchronized
    pub fn push(&mut self) {
        self.exit_model_scope_if_active();
        self.sat.push();
        self.theory.push();
        if let Some(ref diag) = self.diagnostic_trace {
            let level = u32::try_from(self.scope_depth()).unwrap_or(u32::MAX);
            diag.emit_push(level);
        }
    }

    /// Pop the most recent assertion scope.
    ///
    /// Removes all clauses added since the last `push()` and restores the
    /// theory solver state. Returns `false` if there is no active scope to pop.
    ///
    /// # Invariants
    /// - INV-POP-1: After pop(), scope depth decreases by 1 (if > 0)
    /// - INV-POP-2: SAT solver and theory solver scopes remain synchronized
    /// - INV-POP-3: Learned clauses that depend only on base assertions are preserved
    pub fn pop(&mut self) -> bool {
        self.exit_model_scope_if_active();
        let from_level = self.scope_depth();
        if !self.sat.pop() {
            return false;
        }
        self.theory.pop();
        if let Some(ref diag) = self.diagnostic_trace {
            let from_level = u32::try_from(from_level).unwrap_or(u32::MAX);
            let to_level = u32::try_from(self.scope_depth()).unwrap_or(u32::MAX);
            diag.emit_pop(from_level, to_level);
        }
        true
    }

    /// Get the current scope depth.
    ///
    /// Returns 0 when no push() calls are active.
    #[must_use]
    pub fn scope_depth(&self) -> usize {
        self.sat.scope_depth()
    }

    /// Extract learned clauses from the SAT solver.
    ///
    /// Used in branch-and-bound to preserve learned clauses across solver recreations.
    #[must_use]
    pub fn get_learned_clauses(&self) -> Vec<Vec<Literal>> {
        self.sat.get_learned_clauses()
    }

    /// Add learned clauses from a previous solve session.
    ///
    /// Used in branch-and-bound to restore learned clauses after recreating the solver.
    /// Automatically expands the solver's variable count if learned clauses reference
    /// variables beyond the current `num_vars` (#4797).
    pub fn add_learned_clauses(&mut self, clauses: Vec<Vec<Literal>>) {
        // Find the maximum variable referenced across all learned clauses.
        // The previous solver may have allocated more variables (e.g., from
        // split atoms applied during solving) than the current solver has after
        // re-applying accumulated splits. Expand to accommodate.
        let max_var = clauses
            .iter()
            .flat_map(|c| c.iter())
            .map(|l| l.variable().index())
            .max();
        if let Some(max_var) = max_var {
            self.sat.ensure_num_vars(max_var + 1);
        }
        for clause in clauses {
            self.sat.add_preserved_learned(clause);
        }
    }
}
