// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core `check_sat` and `check_sat_assuming` entrypoints with shared
//! preflight and result-classification helpers.

use ay_core::time::Instant;
use std::sync::atomic::Ordering;
use std::time::Duration;

use crate::api::types::{
    NativeReplayEventKind, SolveResult, SolverError, Term, VerifiedSolveResult,
};
use crate::api::Solver;
use crate::{ExecutorError, UnknownReason};

/// Reject a native operation that may issue more than one decision query while
/// the process-wide single-artifact BV CNF export is enabled.
///
/// The exporter intentionally represents exactly one top-level decision. A
/// composite operation would otherwise let its last internal probe overwrite
/// the artifact for an earlier probe (or for the caller's preceding check).
pub(super) fn reject_bv_cnf_export_operation(operation: &'static str) -> Result<(), SolverError> {
    if !crate::Executor::bv_cnf_export_requested() {
        return Ok(());
    }

    let error = match crate::Executor::invalidate_bv_cnf_export_for_rejected_check() {
        Ok(()) => ExecutorError::ArtifactExport(format!(
            "--dump-bv-cnf does not support composite native operation {operation} because it may run multiple internal decision probes"
        )),
        Err(error) => error,
    };
    Err(SolverError::ExecutorError(error))
}

impl Solver {
    /// Env-gated query capture (`AY_DUMP_QUERY_DIR`): serialize the live
    /// assertion stack (plus the call's assumptions, asserted — a
    /// satisfiability-equivalent batch rendering of `check-sat-assuming`) as a
    /// self-contained SMT-LIB2 script into the given directory, one file per
    /// native check. Diagnostic-only: inert unless the variable is set, never
    /// alters solving. Intended for extracting embedded-consumer queries
    /// (e.g. verifier VCs) into standalone repro files.
    fn dump_query_if_requested(&self, assumptions: &[Term]) {
        let Ok(dir) = std::env::var("AY_DUMP_QUERY_DIR") else {
            return;
        };
        static COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let mut ids = self.executor.ctx.assertions.clone();
        ids.extend(assumptions.iter().map(|t| t.0));
        let script = self.executor.to_smtlib2_for(&ids);
        let path =
            std::path::Path::new(&dir).join(format!("query-{}-{:05}.smt2", std::process::id(), n));
        let _ = std::fs::create_dir_all(&dir);
        let _ = std::fs::write(path, script);
    }

    /// Reject a solver state that contains both parser-owned and native-API
    /// soft constraints.
    ///
    /// The two sets have distinct ownership and index spaces. Native feasibility
    /// checks intentionally do not optimize either set, but accepting their
    /// coexistence here would still let a caller cross a public decision boundary
    /// with an ambiguous optimization problem that other entrypoints handle
    /// differently. Fail closed until the sets have one joint representation.
    fn reject_mixed_soft_ownership(&mut self) -> Option<VerifiedSolveResult> {
        if self.soft_constraints.is_empty() || self.executor.context().soft_constraints().is_empty()
        {
            return None;
        }
        self.last_unknown_reason = Some(UnknownReason::Unsupported);
        Some(VerifiedSolveResult::from_validated(
            SolveResult::Unknown,
            None,
        ))
    }

    /// Instance wrapper for [`reject_bv_cnf_export_operation`] that also
    /// preserves the failure in the normal native-API diagnostic fields.
    pub(super) fn reject_composite_bv_cnf_export(
        &mut self,
        operation: &'static str,
    ) -> Result<(), SolverError> {
        match reject_bv_cnf_export_operation(operation) {
            Ok(()) => Ok(()),
            Err(error) => {
                self.last_unknown_reason = Some(UnknownReason::InternalError);
                self.last_artifact_export_failure = match &error {
                    SolverError::ExecutorError(ExecutorError::ArtifactExport(detail)) => {
                        Some(detail.clone())
                    }
                    _ => None,
                };
                self.last_executor_error = Some(error.to_string());
                Err(error)
            }
        }
    }

    /// Return the typed artifact-export failure recorded by an infallible solve
    /// API. The `try_check_sat*` family uses this to avoid collapsing a
    /// certificate failure into a successful `Ok(Unknown)`.
    pub(super) fn last_artifact_export_error(&self) -> Option<SolverError> {
        Some(SolverError::ExecutorError(ExecutorError::ArtifactExport(
            self.last_artifact_export_failure.clone()?,
        )))
    }

    /// Record an executor failure for the infallible compatibility APIs while
    /// retaining a typed artifact-export payload for fallible callers.
    pub(super) fn record_executor_failure_unknown(&mut self, error: &ExecutorError) {
        // An errored decision query admits no model, certificate, proof, or
        // optimum. Drop any partial artefacts left by the failed executor path.
        self.executor.begin_public_solve(false);
        self.last_unknown_reason = Some(UnknownReason::InternalError);
        self.last_artifact_export_failure = match error {
            ExecutorError::ArtifactExport(detail) => Some(detail.clone()),
            _ => None,
        };
        self.last_executor_error = Some(error.to_string());
    }

    /// Reset last-solve state fields before a new check-sat call.
    pub(super) fn clear_last_solve_state(
        &mut self,
        clear_assumptions: bool,
        preserve_pareto_enumeration: bool,
    ) {
        // Do this BEFORE preflight. An interrupt/timeout/memory rejection never
        // enters Executor, but it still supersedes the previous query and must
        // revoke that query's model/certificate/objective artefacts.
        self.executor
            .begin_public_solve(preserve_pareto_enumeration);
        if clear_assumptions {
            self.last_assumptions = None;
        }
        self.last_unknown_reason = None;
        self.last_executor_error = None;
        self.last_artifact_export_failure = None;
    }

    fn preflight_unknown(&mut self, reason: UnknownReason) -> VerifiedSolveResult {
        self.last_unknown_reason = Some(reason);
        if crate::Executor::bv_cnf_export_requested() {
            let error = match crate::Executor::invalidate_bv_cnf_export_for_rejected_check() {
                Ok(()) => ExecutorError::ArtifactExport(format!(
                    "BV CNF export cannot complete because check-sat preflight returned {reason}"
                )),
                Err(error) => error,
            };
            self.last_artifact_export_failure = match &error {
                ExecutorError::ArtifactExport(detail) => Some(detail.clone()),
                _ => None,
            };
            self.last_executor_error = Some(error.to_string());
        }
        VerifiedSolveResult::from_validated(SolveResult::Unknown, None)
    }

    /// Pre-check interrupt, memory, and deadline before entering the executor.
    /// Returns `Some(Unknown)` with the appropriate reason if a preflight
    /// condition fires, or `None` if the solve should proceed.
    pub(super) fn preflight_check(
        &mut self,
        deadline: Option<Instant>,
    ) -> Option<VerifiedSolveResult> {
        if self.interrupt.load(Ordering::Relaxed) {
            return Some(self.preflight_unknown(UnknownReason::Interrupted));
        }

        if crate::memory::memory_exceeded(self.memory_limit) || ay_sys::process_memory_exceeded() {
            return Some(self.preflight_unknown(UnknownReason::MemoryLimit));
        }

        // Per-instance term memory check (#6563): prevents cross-instance
        // budget interference when multiple solvers run in the same process.
        if let Some(limit) = self.term_memory_limit {
            if self.terms().instance_memory_exceeded(limit) {
                return Some(self.preflight_unknown(UnknownReason::MemoryLimit));
            }
        }

        if let Some(dl) = deadline {
            if Instant::now() >= dl {
                return Some(self.preflight_unknown(UnknownReason::Timeout));
            }
        }

        None
    }

    /// Forward solve-control limits to the executor and install the interrupt
    /// handle and deadline.
    pub(super) fn install_solve_controls(&mut self, deadline: Option<Instant>) {
        self.executor
            .set_learned_clause_limit(self.learned_clause_limit);
        self.executor
            .set_clause_db_bytes_limit(self.clause_db_bytes_limit);
        self.executor
            .set_solve_controls(Some(self.interrupt.clone()), deadline);
    }

    /// Classify an `Unknown` result that has no reason yet, using executor
    /// state, interrupt flag, deadline, and memory limit.
    pub(super) fn classify_unknown_reason(&mut self, deadline: Option<Instant>) {
        if let Some(reason) = self.executor.unknown_reason() {
            self.last_unknown_reason = Some(reason);
        } else if self.interrupt.load(Ordering::Relaxed) {
            self.last_unknown_reason = Some(UnknownReason::Interrupted);
        } else if deadline.is_some_and(|d| Instant::now() >= d) {
            self.last_unknown_reason = Some(UnknownReason::Timeout);
        } else if crate::memory::memory_exceeded(self.memory_limit)
            || ay_sys::process_memory_exceeded()
            || self
                .term_memory_limit
                .is_some_and(|limit| self.terms().instance_memory_exceeded(limit))
        {
            self.last_unknown_reason = Some(UnknownReason::MemoryLimit);
        } else {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
        }
    }

    // =========================================================================
    // Solving
    // =========================================================================

    /// Check satisfiability of the current assertions.
    ///
    /// This native entrypoint is a hard-formula feasibility query; use
    /// [`optimize_check`](Self::optimize_check) for arithmetic objectives or
    /// [`check_sat_max`](Self::check_sat_max) for API-owned soft constraints.
    /// A state containing both parser-owned and API-owned soft sets is rejected
    /// as `Unknown(Unsupported)` because their distinct index spaces cannot be
    /// represented jointly.
    ///
    /// Returns a `VerifiedSolveResult` where Sat results carry validation
    /// provenance. Use [`was_model_validated()`](VerifiedSolveResult::was_model_validated)
    /// to check whether model validation actually ran. Part of #5748, #5973.
    pub fn check_sat(&mut self) -> VerifiedSolveResult {
        self.dump_query_if_requested(&[]);
        self.clear_last_solve_state(true, false);
        self.record_native_replay_event(NativeReplayEventKind::CheckSat);
        if let Some(rejected) = self.reject_mixed_soft_ownership() {
            return rejected;
        }

        let deadline = self.timeout.map(|d| Instant::now() + d);
        if let Some(early) = self.preflight_check(deadline) {
            return early;
        }

        self.install_solve_controls(deadline);
        let exec_result = self.executor.check_sat();
        self.executor.clear_solve_controls();

        let result = match exec_result {
            Ok(r) => r,
            Err(e) => {
                self.record_executor_failure_unknown(&e);
                SolveResult::Unknown
            }
        };

        if result == SolveResult::Unknown && self.last_unknown_reason.is_none() {
            self.classify_unknown_reason(deadline);
        }

        let sat_certificate = self.executor.take_sat_certificate();
        VerifiedSolveResult::from_validated(result, sat_certificate)
    }

    /// Check satisfiability with an additional cooperative interrupt callback.
    ///
    /// This is intended for portfolio/search callers that need to stop a running
    /// check from outside the solver's built-in interrupt flag or timeout. The
    /// callback should be cheap and non-blocking.
    pub fn check_sat_interruptible<F>(&mut self, should_stop: F) -> VerifiedSolveResult
    where
        F: Fn() -> bool + Send + 'static,
    {
        self.clear_last_solve_state(true, false);
        self.record_native_replay_event(NativeReplayEventKind::CheckSat);
        if let Some(rejected) = self.reject_mixed_soft_ownership() {
            return rejected;
        }

        let deadline = self.timeout.map(|d| Instant::now() + d);
        if let Some(early) = self.preflight_check(deadline) {
            return early;
        }

        self.install_solve_controls(deadline);
        let exec_result = self.executor.check_sat_interruptible(should_stop);
        self.executor.clear_solve_controls();

        let result = match exec_result {
            Ok(r) => r,
            Err(e) => {
                self.record_executor_failure_unknown(&e);
                SolveResult::Unknown
            }
        };

        if result == SolveResult::Unknown && self.last_unknown_reason.is_none() {
            self.classify_unknown_reason(deadline);
        }

        let sat_certificate = self.executor.take_sat_certificate();
        VerifiedSolveResult::from_validated(result, sat_certificate)
    }

    /// Check satisfiability with a per-call timeout override.
    ///
    /// This is a convenience method that temporarily overrides the solver's
    /// timeout for a single check-sat call, then restores the previous setting.
    /// Useful when different queries in the same solver need different timeouts
    /// (e.g., a quick pre-check with 100ms followed by a full solve with 5s).
    ///
    /// Returns `Unknown` with reason `Timeout` if the deadline expires.
    ///
    /// # Example
    ///
    /// ```
    /// use std::time::Duration;
    /// use ay_dpll::api::{Logic, SolveResult, Solver, Sort};
    ///
    /// let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    /// let x = solver.declare_const("x", Sort::Int);
    /// let zero = solver.int_const(0);
    /// let x_gt_zero = solver.gt(x, zero);
    /// solver.assert_term(x_gt_zero);
    ///
    /// let result = solver.check_sat_with_timeout(Duration::from_millis(5000));
    /// assert!(result.is_sat());
    /// ```
    pub fn check_sat_with_timeout(&mut self, timeout: Duration) -> VerifiedSolveResult {
        let saved = self.timeout;
        self.timeout = Some(timeout);
        let result = self.check_sat();
        self.timeout = saved;
        result
    }

    /// Check satisfiability under temporary assumptions
    ///
    /// Unlike `assert_term()`, assumptions are temporary - they only apply to this
    /// single check-sat call and do not affect the assertion stack.
    /// This is likewise a hard-formula feasibility query, not assumption-scoped
    /// optimization; mixed parser/API soft ownership is rejected fail-closed.
    ///
    /// After an UNSAT result, call `get_unsat_assumptions()` to get the subset
    /// of assumptions that contributed to unsatisfiability.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Solver, Sort, SolveResult, Logic};
    ///
    /// let mut solver = Solver::new(Logic::QfLia);
    /// let x = solver.declare_const("x", Sort::Int);
    /// let zero = solver.int_const(0);
    /// let one = solver.int_const(1);
    ///
    /// // Assert x >= 0 permanently
    /// let x_ge_0 = solver.ge(x, zero);
    /// solver.assert_term(x_ge_0);
    ///
    /// // Check with temporary assumption x < 0 - should be UNSAT
    /// let x_lt_0 = solver.lt(x, zero);
    /// assert!(solver.check_sat_assuming(&[x_lt_0]).is_unsat());
    ///
    /// // Original assertion still holds, without the assumption
    /// let x_eq_1 = solver.eq(x, one);
    /// assert_eq!(solver.check_sat_assuming(&[x_eq_1]), SolveResult::Sat);
    /// ```
    pub fn check_sat_assuming(&mut self, assumptions: &[Term]) -> VerifiedSolveResult {
        self.dump_query_if_requested(assumptions);
        self.clear_last_solve_state(false, false);
        self.record_native_replay_event(NativeReplayEventKind::CheckSatAssuming {
            assumptions: assumptions.iter().map(|term| term.0).collect(),
        });
        if let Some(rejected) = self.reject_mixed_soft_ownership() {
            return rejected;
        }

        let deadline = self.timeout.map(|d| Instant::now() + d);
        if let Some(early) = self.preflight_check(deadline) {
            return early;
        }

        self.install_solve_controls(deadline);

        let assumption_ids: Vec<_> = assumptions.iter().map(|t| t.0).collect();
        self.last_assumptions = Some(assumptions.iter().map(|t| (t.0, *t)).collect());

        // User-facing entry: named assertions are assumption-tracked when
        // `:produce-unsat-cores` is on, so `try_get_unsat_core` after an
        // assumption-bearing UNSAT includes named participants
        // (#unsat-core-assumptions). Internal solver probes bypass this.
        let exec_result = self
            .executor
            .check_sat_assuming_with_named_cores(&assumption_ids);
        self.executor.clear_solve_controls();

        let result = match exec_result {
            Ok(r) => r,
            Err(e) => {
                self.record_executor_failure_unknown(&e);
                SolveResult::Unknown
            }
        };

        if result == SolveResult::Unknown && self.last_unknown_reason.is_none() {
            self.classify_unknown_reason(deadline);
        }

        let sat_certificate = self.executor.take_sat_certificate();
        VerifiedSolveResult::from_validated(result, sat_certificate)
    }
}
