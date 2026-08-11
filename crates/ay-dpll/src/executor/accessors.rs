// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Result, statistics, and provenance accessors.

use super::*;

impl Executor {
    /// Access the trail provenance data from the last SAT result (#8153, #8307).
    pub(crate) fn last_trail_provenance(&self) -> Option<&HashMap<u32, (u32, bool, Vec<u32>)>> {
        self.last_trail_provenance.as_ref()
    }

    /// Access the var-to-term mapping from the last Tseitin encoding (#8307).
    ///
    /// Maps 0-based SAT variable index to TermId. Used by `model_provenance()`
    /// to convert reason clause variable indices back to `Term` handles.
    pub(crate) fn last_var_to_term(&self) -> Option<&HashMap<u32, TermId>> {
        self.last_var_to_term.as_ref()
    }

    /// Look up the SAT variable index for a term ID from the last model (#8153).
    pub(crate) fn last_model_term_to_var(&self, term_id: TermId) -> Option<u32> {
        self.last_model.as_ref()?.term_to_var.get(&term_id).copied()
    }

    /// Capture trail provenance from the persistent SAT solver (#8153, #8307).
    ///
    /// Called after check-sat returns SAT, when pipeline borrows are released.
    /// Queries `incr_theory_state.persistent_sat` (or `lia_persistent_sat`)
    /// for each variable in the model's `term_to_var` mapping.
    ///
    /// For propagated variables, also captures the reason clause's antecedent
    /// variable indices so that `model_provenance()` can populate
    /// `antecedent_terms` with real data instead of an empty vec.
    pub(crate) fn capture_trail_provenance(&mut self) {
        let model = match self.last_model.as_ref() {
            Some(m) => m,
            None => return,
        };
        let sat = self
            .incr_theory_state
            .as_ref()
            .and_then(|s| s.persistent_sat.as_ref().or(s.lia_persistent_sat.as_ref()));
        let sat = match sat {
            Some(s) => s,
            None => return,
        };
        let mut provenance = HashMap::default();
        let sat_num_vars = sat.total_num_vars();
        for (_, &var_idx) in &model.term_to_var {
            // Optimization blocking constraints may introduce variables beyond
            // the persistent SAT solver's variable count (#8515). Skip them to
            // avoid out-of-bounds access in var_level/var_assignment_kind.
            if (var_idx as usize) >= sat_num_vars {
                continue;
            }
            let var = ay_sat::Variable::new(var_idx);
            if let Some(level) = sat.var_level(var) {
                let kind = sat.var_assignment_kind(var);
                let is_propagated = kind == ay_sat::VarAssignmentKind::Propagated;
                let antecedents = if is_propagated {
                    sat.var_reason_variable_indices(var).unwrap_or_default()
                } else {
                    vec![]
                };
                provenance.insert(var_idx, (level, is_propagated, antecedents));
            }
        }
        self.last_trail_provenance = Some(provenance);
    }

    // DT axiom generation functions (dt_selector_axioms, dt_acyclicity_depth_axioms,
    // dt_occurs_check_unsat_from_equalities) moved to executor/dt_axioms.rs.

    /// Execute a sequence of commands
    ///
    /// Returns outputs for each command that produces output.
    #[must_use = "command results must be checked — errors indicate parse/solve failures"]
    pub fn execute_all(&mut self, commands: &[Command]) -> Result<Vec<String>> {
        let mut outputs = Vec::new();
        for cmd in commands {
            if let Some(output) = self.execute(cmd)? {
                outputs.push(output);
            }
        }
        Ok(outputs)
    }

    // check_sat, check_sat_interruptible, check_sat_guarded, set_interrupt,
    // set_timeout, set_solve_controls, clear_solve_controls, make_should_stop,
    // should_abort_theory_loop, check_sat_internal, route_to_solver:
    // moved to executor/check_sat.rs

    /// Get the current logic
    pub fn logic(&self) -> Option<&str> {
        self.ctx.logic()
    }

    /// Get the number of assertions
    pub fn assertion_count(&self) -> usize {
        self.ctx.assertions.len()
    }

    /// Get the last check-sat result.
    ///
    /// Read-only accessor for the result of the last solve call. The result
    /// was validated during solve (via `finalize_sat_model_validation()`).
    /// This accessor does not bypass verification — it reads an already-validated value.
    ///
    /// `pub(crate)`: External consumers use `api::Solver::last_result()` or the
    /// narrow `last_result_is_unsat()` predicate. Part of #5787 (Phase 6).
    pub(crate) fn last_result(&self) -> Option<&SolveResult> {
        self.last_result.as_ref()
    }

    /// Returns `true` if the last check-sat call returned UNSAT.
    ///
    /// Narrow predicate for callers that only need a boolean check
    /// (e.g., proof file writing) without matching on `SolveResult` variants.
    pub fn last_result_is_unsat(&self) -> bool {
        self.last_result.as_ref().is_some_and(SolveResult::is_unsat)
    }

    /// Returns `true` if the last check-sat call returned SAT.
    ///
    /// Narrow predicate mirroring [`Self::last_result_is_unsat`]. Note that
    /// assertion-stack mutations (`push`/`pop`/`assert`/`reset`) invalidate
    /// the last result, after which all three `last_result_is_*` predicates
    /// return `false`. Callers presenting the verdict to users (e.g.
    /// `--explain`) must handle that no-result state explicitly instead of
    /// defaulting to SAT.
    pub fn last_result_is_sat(&self) -> bool {
        self.last_result.as_ref().is_some_and(SolveResult::is_sat)
    }

    /// Returns `true` if the last check-sat call returned UNKNOWN.
    pub fn last_result_is_unknown(&self) -> bool {
        self.last_result
            .as_ref()
            .is_some_and(SolveResult::is_unknown)
    }

    /// Structured reason for the last Unknown result.
    ///
    /// Returns the reason why the solver returned Unknown, if available.
    /// Returns `None` if the last result was not Unknown or if no reason was recorded.
    #[must_use]
    pub fn unknown_reason(&self) -> Option<UnknownReason> {
        match self.last_result {
            Some(SolveResult::Unknown) => self.last_unknown_reason,
            _ => None,
        }
    }

    /// True when the last SAT result passed either ordinary final model
    /// validation or the independently checked total-projection lane (#5903).
    pub(crate) fn was_model_validated(&self) -> bool {
        self.last_model_validated
    }

    /// Take the [`SatCertificate`](model::sat_emit::SatCertificate) minted by a
    /// complete private SAT-emission lane, if the last emitted verdict was
    /// `Sat`.
    ///
    /// The API boundary calls this to build a public `Sat` `VerifiedSolveResult`;
    /// because the certificate can only be minted inside the ordinary or
    /// checked-projection chokepoint, a `Sat` that went through neither yields
    /// `None` here and is fail-closed to `Unknown` at the boundary
    /// (#sat-chokepoint).
    pub(crate) fn take_sat_certificate(&mut self) -> Option<SatCertificate> {
        let certificate = self.last_sat_certificate.take()?;
        certificate.is_current_for(self).then_some(certificate)
    }

    /// Return the admitted MaxSMT accounting for the current SAT result.
    ///
    /// The violated indices were captured from the temporary relaxation
    /// indicators before those internal symbols were removed. `None` means the
    /// current result is not an admitted MaxSMT witness.
    pub(crate) fn last_maxsmt_outcome(&self) -> Option<(u64, bool, &[usize])> {
        Some((
            self.last_soft_cost?,
            self.last_soft_cost_optimal,
            self.last_soft_violations.as_deref()?,
        ))
    }

    /// Test-only hook for consumer-boundary model extraction canaries.
    #[cfg(test)]
    pub(crate) fn set_model_validated_for_testing(&mut self, validated: bool) {
        self.last_model_validated = validated;
    }

    /// Get statistics from the last check-sat call
    ///
    /// Returns statistics about the solving process including:
    /// - SAT-level stats: conflicts, decisions, propagations, restarts
    /// - Theory-level stats: theory conflicts and propagations
    /// - Problem size: variables, clauses, assertions
    ///
    /// # Example
    ///
    /// ```no_run
    /// use ay_dpll::Executor;
    ///
    /// let mut exec = Executor::new();
    /// // ... setup and check_sat ...
    /// let stats = exec.statistics();
    /// println!("Conflicts: {}", stats.conflicts);
    /// println!("Decisions: {}", stats.decisions);
    /// ```
    #[must_use]
    pub fn statistics(&self) -> &Statistics {
        &self.last_statistics
    }

    /// Alias for `statistics()` (backward compat with tests).
    #[must_use]
    pub fn get_statistics(&self) -> &Statistics {
        &self.last_statistics
    }

    /// Return the reason for the last `Unknown` result, if any.
    #[must_use]
    pub fn get_reason_unknown(&self) -> Option<UnknownReason> {
        self.last_unknown_reason
    }

    // produce_assignments_enabled, produce_unsat_cores_enabled, get_assignment,
    // get_unsat_core, get_unsat_assumptions moved to executor/commands.rs
    // get_proof and produce_proofs_enabled moved to executor/proof.rs
}
