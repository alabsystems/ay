// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MaxSMT solving for native API soft constraints.
//!
//! [`Solver::check_sat_max`] deliberately reuses the executor's `(assert-soft)`
//! engine instead of maintaining a second relaxation/cardinality implementation.
//! It accepts one API-owned soft set only. Parsed SMT-LIB softs and arithmetic
//! objectives are rejected as unsupported rather than merged or silently
//! displaced: their ownership/result-index semantics require a joint API that
//! does not exist yet. API softs are installed in the elaboration context for
//! one `(check-sat)` command and the empty parsed set is restored immediately
//! afterward on every normal success/error/Unknown exit. The executor owns
//! the deeper transaction: temporary assertions, parsed-assertion alignment,
//! symbols, probe state, and solve artefacts are restored before an optimal
//! witness is revalidated over the user's hard assertions.
//!
//! The current exact weighted encoding replicates each relaxation indicator by
//! its weight, so exact solving is capped at a bounded total weight. Larger or
//! overflowing instances return honest `Unknown`; the API never labels the
//! executor's count/greedy fallback as an optimum.

use ay_core::time::Instant;
use ay_frontend::{Command, SoftAssertion};

use crate::api::types::maxsmt::{MaxSmtResult, SoftConstraint};
use crate::api::types::{NativeReplayEventKind, SolveResult, SolverError, Term};
use crate::api::Solver;
use crate::executor::optimization::MAXSMT_EXACT_MAX_TOTAL_WEIGHT;
use crate::UnknownReason;

impl Solver {
    /// Assert a soft constraint with the given weight and optional group.
    ///
    /// Soft constraints are not required to be satisfied. The solver will
    /// maximize the total weight of satisfied soft constraints when
    /// [`check_sat_max`](Self::check_sat_max) is called.
    ///
    /// Returns the index used by [`MaxSmtResult::violated_softs`].
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `term` is not Boolean.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Logic, Solver, Sort};
    ///
    /// let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    /// let x = solver.declare_const("x", Sort::Int);
    /// let zero = solver.int_const(0);
    /// let x_pos = solver.try_gt(x, zero).unwrap();
    /// let idx = solver.assert_soft(x_pos, 1, None).unwrap();
    /// assert_eq!(idx, 0);
    /// ```
    #[must_use = "this returns a Result that must be checked"]
    pub fn assert_soft(
        &mut self,
        term: Term,
        weight: u64,
        group: Option<&str>,
    ) -> Result<usize, SolverError> {
        if let Some(message) = self
            .executor
            .array_ext_witness_registration_error(&[term.0])
        {
            return Err(SolverError::InvalidArgument {
                operation: "assert_soft",
                message,
            });
        }
        self.expect_bool("assert_soft", term)?;
        self.executor.note_api_optimization_mutation();
        let idx = self.soft_constraints.len();
        self.soft_constraints.push(SoftConstraint {
            term,
            weight,
            group: group.map(String::from),
        });
        Ok(idx)
    }

    /// Return the number of registered API-level soft constraints.
    #[must_use]
    pub fn num_soft_constraints(&self) -> usize {
        self.soft_constraints.len()
    }

    /// Truncate the API-level soft-constraint list to `len` entries.
    ///
    /// Used by scoped optimization (`Z3_optimize_push`/`Z3_optimize_pop`) to
    /// restore the soft set to the length at the matching push. A `len` at or
    /// above the current length is a no-op.
    pub fn truncate_soft_constraints(&mut self, len: usize) {
        if len < self.soft_constraints.len() {
            self.executor.note_api_optimization_mutation();
            self.soft_constraints.truncate(len);
        }
    }

    /// Number of soft constraints parsed into the elaboration context via
    /// `(assert-soft ...)` (for example through SMT-LIB parsing).
    ///
    /// Parsed softs are distinct from API-level softs counted by
    /// [`num_soft_constraints`](Self::num_soft_constraints). A native
    /// [`check_sat_max`](Self::check_sat_max) temporarily installs only its API
    /// set, then restores this parsed set before returning.
    #[must_use]
    pub fn num_parsed_soft_constraints(&self) -> usize {
        self.executor.context().soft_constraints().len()
    }

    /// Solve the API MaxSMT problem exactly when its weighted encoding is within
    /// the supported bound.
    ///
    /// The operation is transactional: temporary relaxation/cardinality
    /// assertions, parsed alignment entries, internal symbols, scopes, probe
    /// results, and objective artefacts never leak. A returned `Optimal` keeps a
    /// model only after the executor restores the hard formula and revalidates
    /// that model through the public SAT-admission funnel.
    ///
    /// If the total soft weight overflows `u64`, exceeds the exact encoding cap,
    /// or an internal optimization probe is inconclusive, this returns
    /// [`MaxSmtStatus::Unknown`](crate::api::MaxSmtStatus::Unknown) and retires
    /// every prior/current model and optimum. It never presents an approximate
    /// count/greedy solution as optimal.
    ///
    /// This entrypoint is exclusively for softs registered through
    /// [`assert_soft`](Self::assert_soft). If parsed `(assert-soft ...)` entries
    /// or arithmetic `maximize`/`minimize` objectives are present, it returns
    /// `Unknown(Unsupported)` and does not solve a silently truncated problem.
    ///
    /// # Errors
    ///
    /// Returns a [`SolverError`] if command elaboration, artifact export, or the
    /// executor fails. Even on error the parsed soft set and all solve artefacts
    /// are restored/retired before control returns to the caller.
    #[must_use = "this returns a Result that must be checked"]
    pub fn check_sat_max(&mut self) -> Result<MaxSmtResult, SolverError> {
        if !self.executor.context().soft_constraints().is_empty()
            || !self.executor.context().objectives().is_empty()
        {
            self.clear_last_solve_state(true, false);
            self.record_native_replay_event(NativeReplayEventKind::CheckSat);
            self.last_unknown_reason = Some(UnknownReason::Unsupported);
            return Ok(MaxSmtResult::unknown());
        }

        if self.soft_constraints.is_empty() {
            let result = self.check_sat();
            return Ok(if result.is_sat() {
                MaxSmtResult::optimal(0, 0, Vec::new())
            } else if result.is_unsat() {
                MaxSmtResult::hard_unsatisfiable()
            } else {
                MaxSmtResult::unknown()
            });
        }

        // A rejected/preflight/unsupported query still supersedes the preceding
        // public result. Retire it before ANY fallible operation.
        self.clear_last_solve_state(true, false);
        self.record_native_replay_event(NativeReplayEventKind::CheckSat);
        self.reject_composite_bv_cnf_export("check_sat_max")?;

        let deadline = self.timeout.map(|duration| Instant::now() + duration);
        if self.preflight_check(deadline).is_some() {
            return Ok(MaxSmtResult::unknown());
        }

        // SMT-LIB `:id` denotes grouped/independent soft objectives, not a
        // cosmetic label. MaxSmtResult represents one flat weighted objective,
        // so flattening groups would publish the wrong optimization problem.
        // Until the result/API can represent exact group semantics, refuse the
        // feature honestly and expose no model or partial objective.
        if self
            .soft_constraints
            .iter()
            .any(|soft| soft.group.is_some())
        {
            self.last_unknown_reason = Some(UnknownReason::Unsupported);
            return Ok(MaxSmtResult::unknown());
        }

        let total_weight = match self
            .soft_constraints
            .iter()
            .try_fold(0u64, |sum, soft| sum.checked_add(soft.weight))
        {
            Some(total) if total <= MAXSMT_EXACT_MAX_TOTAL_WEIGHT => total,
            Some(_) | None => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                return Ok(MaxSmtResult::unknown());
            }
        };

        let native_softs: Vec<SoftAssertion> = self
            .soft_constraints
            .iter()
            .map(|soft| SoftAssertion {
                term: soft.term.0,
                weight: soft.weight,
                id: soft.group.clone(),
            })
            .collect();
        let expected_native_softs = native_softs.clone();

        // Install exactly the native soft set for one executor command. Restore
        // the parsed set before inspecting or propagating the command outcome,
        // including the executor-error path.
        let parsed_softs = self
            .executor
            .context_mut()
            .replace_soft_constraints(native_softs);
        self.install_solve_controls(deadline);
        let execution = self.executor.execute(&Command::CheckSat);
        self.executor.clear_solve_controls();
        #[cfg(test)]
        if self.corrupt_native_soft_transaction {
            self.corrupt_native_soft_transaction = false;
            let mut installed = self
                .executor
                .context_mut()
                .replace_soft_constraints(Vec::new());
            if let Some(first) = installed.first_mut() {
                first.weight = first.weight.wrapping_add(1);
            }
            let displaced = self
                .executor
                .context_mut()
                .replace_soft_constraints(installed);
            debug_assert!(displaced.is_empty());
        }
        let installed_native_softs = self
            .executor
            .context_mut()
            .replace_soft_constraints(parsed_softs);

        // This is an authentication check, not a debug-only shape assertion:
        // outcome indices are interpreted against the caller-owned native set.
        // A reordered/substituted term at the same length would otherwise bind
        // the executor's proof-shaped accounting to different constraints.
        if installed_native_softs != expected_native_softs {
            return Ok(self.reject_inconsistent_maxsmt(
                "executor mutated or reordered the installed native soft-constraint set"
                    .to_string(),
            ));
        }

        if let Err(error) = execution {
            self.record_executor_failure_unknown(&error);
            return Err(error.into());
        }

        let result = self
            .executor
            .last_result()
            .cloned()
            .unwrap_or(SolveResult::Unknown);
        if result == SolveResult::Unknown && self.last_unknown_reason.is_none() {
            self.classify_unknown_reason(deadline);
        }

        if result.is_unsat() {
            return Ok(MaxSmtResult::hard_unsatisfiable());
        }
        if !result.is_sat() {
            return Ok(MaxSmtResult::unknown());
        }

        if !self.executor.was_model_validated() {
            return Ok(self.reject_inconsistent_maxsmt(
                "executor returned SAT from MaxSMT without an admitted model".to_string(),
            ));
        }

        let Some((violated_weight, optimal, violated_softs)) = self.executor.last_maxsmt_outcome()
        else {
            return Ok(self.reject_inconsistent_maxsmt(
                "executor returned SAT from MaxSMT without objective accounting".to_string(),
            ));
        };
        let violated_softs = violated_softs.to_vec();

        if !optimal {
            // The executor may retain a feasible fallback witness for SMT-LIB
            // reporting. The native result type has no Approximate status, so
            // fail closed and expose neither that witness nor its upper bound.
            self.executor.begin_public_solve(false);
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(MaxSmtResult::unknown());
        }

        // Treat accounting as proof-shaped data: independently check every
        // index, reject duplicates, recompute the violated weight, and require
        // exact partitioning of the caller's total weight before publication.
        let mut seen = vec![false; self.soft_constraints.len()];
        let recomputed_violated_weight = violated_softs.iter().try_fold(0u64, |sum, &index| {
            let soft = self.soft_constraints.get(index)?;
            if std::mem::replace(&mut seen[index], true) {
                return None;
            }
            sum.checked_add(soft.weight)
        });
        if recomputed_violated_weight != Some(violated_weight) {
            return Ok(self.reject_inconsistent_maxsmt(format!(
                "executor MaxSMT accounting mismatch: reported violated weight {violated_weight}, recomputed {recomputed_violated_weight:?}"
            )));
        }
        let Some(satisfied_weight) = total_weight.checked_sub(violated_weight) else {
            return Ok(self.reject_inconsistent_maxsmt(format!(
                "executor MaxSMT violated weight {violated_weight} exceeds total {total_weight}"
            )));
        };

        Ok(MaxSmtResult::optimal(
            satisfied_weight,
            violated_weight,
            violated_softs,
        ))
    }

    /// Fail closed when executor accounting violates the native API contract.
    fn reject_inconsistent_maxsmt(&mut self, detail: String) -> MaxSmtResult {
        self.executor.begin_public_solve(false);
        self.last_unknown_reason = Some(UnknownReason::InternalError);
        self.last_executor_error = Some(detail);
        self.last_artifact_export_failure = None;
        MaxSmtResult::unknown()
    }

    /// Corrupt one installed-soft transaction for the release-soundness canary.
    #[cfg(test)]
    pub(crate) fn corrupt_native_soft_transaction_for_test(&mut self) {
        self.corrupt_native_soft_transaction = true;
    }
}
