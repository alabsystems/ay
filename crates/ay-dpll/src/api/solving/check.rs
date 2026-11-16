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
use crate::executor::NativeSoftQueryBinding;
use crate::{ExecutorError, UnknownReason};

/// Whether a native feasibility call is the caller-visible authored decision
/// or one probe inside a composite API operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NativeCheckAuthorityOrigin {
    AuthoredPlain,
    Internal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NativeQueryBoundary {
    External,
    Continuation,
}

/// One immutable control envelope for a complete native solve/publication
/// transaction.
///
/// Native APIs have their own timeout/RSS/term-store settings, while parsing
/// SMT-LIB into the same [`Solver`] can configure `:timeout` and `:max-memory`
/// directly on the executor. Planning the effective limits once prevents
/// nested executor checks from renewing the relative timeout before
/// certification, keeps a tighter parsed RSS ceiling from being overwritten,
/// and makes nested executor probes inherit the native term-store envelope.
#[derive(Clone, Debug)]
pub(super) struct NativePublicationControls {
    deadline: Option<Instant>,
    owner: Option<ay_core::resource::Guard>,
    effective_memory_limit: Option<usize>,
    effective_term_memory_limit: Option<usize>,
    previous_interrupt: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
    previous_memory_limit: Option<usize>,
    previous_term_memory_limit: Option<usize>,
}

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
    /// Env-gated query capture (`--dump-query-dir`): serialize the live
    /// assertion stack (plus the call's assumptions, asserted — a
    /// satisfiability-equivalent batch rendering of `check-sat-assuming`) as a
    /// self-contained SMT-LIB2 script into the given directory, one file per
    /// native check. Diagnostic-only: inert unless the variable is set, never
    /// alters solving. Intended for extracting embedded-consumer queries
    /// (e.g. verifier VCs) into standalone repro files.
    fn dump_query_if_requested(&self, assumptions: &[Term]) {
        let Some(dir) = ay_core::misc_cli_flags().dump_query_dir.clone() else {
            return;
        };
        static COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let script = self.query_dump_script(assumptions);
        let path =
            std::path::Path::new(&dir).join(format!("query-{}-{:05}.smt2", std::process::id(), n));
        let _ = std::fs::create_dir_all(&dir);
        let _ = std::fs::write(path, script);
    }

    /// Build the exact script `--dump-query-dir` would write for a check with
    /// the given assumptions: the live assertion stack plus the assumptions,
    /// serialized as a self-contained SMT-LIB2 script (sort + symbol
    /// declarations included). Exposed crate-internally so the dump format is
    /// unit-testable without touching process-global environment state.
    pub(crate) fn query_dump_script(&self, assumptions: &[Term]) -> String {
        let mut ids = self.executor.ctx.assertions.clone();
        ids.extend(assumptions.iter().map(|term| term.id()));
        self.executor.to_smtlib2_for(&ids)
    }

    /// Reject a solver state that contains both parser-owned and native-API
    /// soft constraints.
    ///
    /// The two sets have distinct ownership and index spaces. Native feasibility
    /// checks intentionally do not optimize either set, but accepting their
    /// coexistence here would still let a caller cross a public decision boundary
    /// with an ambiguous optimization problem that other entrypoints handle
    /// differently. Fail closed until the sets have one joint representation.
    pub(super) fn reject_mixed_soft_ownership(&mut self) -> Option<VerifiedSolveResult> {
        if self.soft_constraints.is_empty() || self.executor.context().soft_constraints().is_empty()
        {
            return None;
        }
        self.executor
            .replace_last_result_with_unknown(UnknownReason::Unsupported);
        self.last_unknown_reason = Some(UnknownReason::Unsupported);
        Some(self.finish_verified_result(SolveResult::Unknown))
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
                self.last_model_extraction_failure = None;
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

    /// Return a typed terminal extraction or artifact-export failure recorded
    /// by an infallible compatibility solve API. The `try_check_sat*` family
    /// must not collapse either refusal into a successful `Ok(Unknown)`.
    pub(super) fn last_artifact_export_error(&self) -> Option<SolverError> {
        if let Some(error) = self.last_model_extraction_failure {
            return Some(SolverError::ExecutorError(ExecutorError::ModelExtraction(
                error,
            )));
        }
        Some(SolverError::ExecutorError(ExecutorError::ArtifactExport(
            self.last_artifact_export_failure.clone()?,
        )))
    }

    /// Record an executor failure for the infallible compatibility APIs while
    /// retaining a typed artifact-export payload for fallible callers.
    ///
    /// The published reason is the error's own ([`ExecutorError::unknown_reason`]):
    /// a theory mix with no combined decision procedure is `Incomplete`, with
    /// the refusal as its diagnostic, and any other executor error
    /// `InternalError` ([`crate::Executor::replace_last_result_with_executor_error`],
    /// which the CLI publishes through too). The error text is kept either way
    /// ([`Self::executor_error`]).
    pub(super) fn record_executor_failure_unknown(&mut self, error: &ExecutorError) {
        // An errored decision query admits no model, certificate, proof, or
        // optimum. Drop any partial artefacts left by the failed executor path.
        self.executor.begin_public_solve(false);
        self.executor.replace_last_result_with_executor_error(error);
        self.last_unknown_reason = Some(error.unknown_reason());
        self.last_model_extraction_failure = match error {
            ExecutorError::ModelExtraction(error) => Some(*error),
            _ => None,
        };
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
        self.clear_last_solve_state_at_boundary(
            clear_assumptions,
            preserve_pareto_enumeration,
            NativeQueryBoundary::External,
        );
    }

    fn clear_last_solve_state_at_boundary(
        &mut self,
        clear_assumptions: bool,
        preserve_pareto_enumeration: bool,
        boundary: NativeQueryBoundary,
    ) {
        // Do this BEFORE preflight. An interrupt/timeout/memory rejection never
        // enters Executor, but it still supersedes the previous query and must
        // revoke that query's model/certificate/objective artefacts.
        match boundary {
            NativeQueryBoundary::External => self
                .executor
                .begin_external_decision_query(preserve_pareto_enumeration),
            NativeQueryBoundary::Continuation => {
                self.executor
                    .begin_public_solve(preserve_pareto_enumeration);
            }
        }
        if clear_assumptions {
            self.last_assumptions = None;
        }
        self.last_unknown_reason = None;
        self.last_executor_error = None;
        self.last_artifact_export_failure = None;
        self.last_model_extraction_failure = None;
    }

    pub(super) fn preflight_unknown(&mut self, reason: UnknownReason) -> VerifiedSolveResult {
        self.executor.replace_last_result_with_unknown(reason);
        self.last_unknown_reason = Some(reason);
        if crate::Executor::bv_cnf_export_requested() {
            let error = match crate::Executor::invalidate_bv_cnf_export_for_rejected_check() {
                Ok(()) => ExecutorError::ArtifactExport(format!(
                    "BV CNF export cannot complete because check-sat preflight returned {reason}"
                )),
                Err(error) => error,
            };
            self.last_model_extraction_failure = None;
            self.last_artifact_export_failure = match &error {
                ExecutorError::ArtifactExport(detail) => Some(detail.clone()),
                _ => None,
            };
            self.last_executor_error = Some(error.to_string());
        }
        self.finish_verified_result(SolveResult::Unknown)
    }

    /// Cross the sole native-API result boundary.
    ///
    /// Definite wrappers can only be built by consuming the executor's exact
    /// one-shot SAT/UNSAT capability. A missing capability is a certification
    /// failure, not a wrapper-local state: publish the registered Unknown on
    /// the executor first so every stale artifact is revoked and both views of
    /// the last query remain identical.
    pub(super) fn finish_verified_result(&mut self, result: SolveResult) -> VerifiedSolveResult {
        self.executor
            .trace_unknown_funnel("api-finish-enter", None, Some(&result), false);
        let effective_term_limit =
            Self::earliest_optional(self.executor.term_memory_limit(), self.term_memory_limit);
        let result = if !result.is_unknown()
            && (ay_core::TermStore::global_memory_exceeded()
                || effective_term_limit
                    .is_some_and(|limit| self.terms().true_memory_bytes() > limit))
        {
            self.executor
                .publish_unknown_from_origin(crate::UnknownOrigin::MemoryBudget);
            SolveResult::Unknown
        } else {
            result
        };
        // Solver-level controls remain installed until after this consumer.
        // Revoke a definite token before taking it when an interrupt, deadline,
        // or memory limit fired after certification but before publication.
        let result = self
            .executor
            .decline_definite_publication_on_external_stop(result);
        let sat_certificate = self.executor.take_sat_certificate();
        let unsat_certificate = self.executor.take_unsat_certificate();
        let verified = match result {
            SolveResult::Sat => match sat_certificate {
                Some(certificate) => VerifiedSolveResult::certified_sat(certificate),
                None => {
                    let published = self
                        .executor
                        .reject_uncertified_verdict_for_publication(
                            "computed SAT reached the native API boundary without its model-validation capability"
                                .to_string(),
                        );
                    match published {
                        SolveResult::Unknown => {
                            self.last_unknown_reason = self.executor.unknown_reason();
                            VerifiedSolveResult::unknown()
                        }
                        SolveResult::Sat | SolveResult::Unsat(_) => unreachable!(
                            "reject_uncertified_verdict_for_publication must fail closed"
                        ),
                    }
                }
            },
            SolveResult::Unsat(proof) => match unsat_certificate {
                Some(certificate) => VerifiedSolveResult::certified_unsat(proof, certificate),
                None => {
                    let published = self
                        .executor
                        .reject_uncertified_verdict_for_publication(
                            "computed UNSAT reached the native API boundary without its sealed exact-query certification capability"
                                .to_string(),
                        );
                    match published {
                        SolveResult::Unknown => {
                            self.last_unknown_reason = self.executor.unknown_reason();
                            VerifiedSolveResult::unknown()
                        }
                        SolveResult::Sat | SolveResult::Unsat(_) => unreachable!(
                            "reject_uncertified_verdict_for_publication must fail closed"
                        ),
                    }
                }
            },
            SolveResult::Unknown => match self
                .executor
                .finalize_unknown_publication(SolveResult::Unknown)
            {
                SolveResult::Unknown => {
                    self.last_unknown_reason = self.executor.unknown_reason();
                    VerifiedSolveResult::unknown()
                }
                SolveResult::Sat | SolveResult::Unsat(_) => {
                    unreachable!("finalize_unknown_publication changed an Unknown verdict")
                }
            },
        };
        self.executor.trace_unknown_funnel(
            "api-finish-return",
            None,
            Some(verified.result()),
            false,
        );
        verified
    }

    /// Reject invalid raw handles and solver-generated array witnesses before
    /// diagnostic query dumping or any other code can traverse caller roots.
    fn reject_native_array_ext_witness_capture(
        &mut self,
        extra: &[Term],
    ) -> Option<VerifiedSolveResult> {
        let mut roots = self.executor.context().assertions.clone();
        roots.extend(
            self.executor
                .context()
                .soft_constraints()
                .iter()
                .map(|soft| soft.term),
        );
        roots.extend(
            self.executor
                .context()
                .objectives()
                .iter()
                .map(|objective| objective.term),
        );
        roots.extend(extra.iter().map(|term| term.id()));
        self.executor
            .array_ext_witness_registration_error(&roots)
            .map(|_| self.preflight_unknown(UnknownReason::Incomplete))
    }

    /// Pre-check interrupt, memory, and deadline before entering the executor.
    /// Returns `Some(Unknown)` with the appropriate reason if a preflight
    /// condition fires, or `None` if the solve should proceed.
    pub(super) fn preflight_check(
        &mut self,
        controls: &NativePublicationControls,
    ) -> Option<VerifiedSolveResult> {
        if let Some(origin) = self.executor.take_pending_fp_namespace_refusal() {
            return Some(self.preflight_unknown(origin.reason()));
        }
        if self.interrupt.load(Ordering::Relaxed) {
            return Some(self.preflight_unknown(UnknownReason::Interrupted));
        }

        if crate::memory::memory_exceeded(controls.effective_memory_limit)
            || ay_sys::process_memory_exceeded()
            || ay_sys::current_memory_group_soft_tripped()
        {
            return Some(self.preflight_unknown(UnknownReason::MemoryLimit));
        }

        // Per-instance term memory check (#6563): prevents cross-instance
        // budget interference when multiple solvers run in the same process.
        if ay_core::TermStore::global_memory_exceeded() {
            return Some(self.preflight_unknown(UnknownReason::MemoryLimit));
        }
        if let Some(limit) = controls.effective_term_memory_limit {
            if self.terms().true_memory_bytes() > limit {
                return Some(self.preflight_unknown(UnknownReason::MemoryLimit));
            }
        }

        if let Some(dl) = controls.deadline {
            if Instant::now() >= dl {
                return Some(self.preflight_unknown(UnknownReason::Timeout));
            }
        }

        None
    }

    /// Plan one absolute native publication deadline and one effective RSS
    /// ceiling from both configuration surfaces.
    ///
    /// `now` is sampled exactly once. Consequently an API timeout and a parsed
    /// SMT-LIB timeout are compared as durations from the same origin, and the
    /// winning absolute deadline is retained through solve, certification, and
    /// final capability consumption.
    pub(super) fn native_publication_controls(&self) -> NativePublicationControls {
        self.native_publication_controls_at(Instant::now())
    }

    pub(super) fn native_maxsmt_publication_controls_at(
        &self,
        now: Instant,
    ) -> NativePublicationControls {
        let roots: Vec<_> = self
            .soft_constraints
            .iter()
            .map(|soft| soft.term.id())
            .collect();
        self.native_publication_controls_for_roots_at(now, &roots)
    }

    pub(super) fn native_optimization_publication_controls_at(
        &self,
        now: Instant,
    ) -> NativePublicationControls {
        let roots: Vec<_> = self
            .soft_constraints
            .iter()
            .map(|soft| soft.term.id())
            .chain(
                self.executor
                    .context()
                    .soft_constraints()
                    .iter()
                    .map(|soft| soft.term),
            )
            .chain(
                self.executor
                    .context()
                    .objectives()
                    .iter()
                    .map(|objective| objective.term),
            )
            .collect();
        self.native_publication_controls_for_roots_at(now, &roots)
    }

    pub(super) fn begin_model_evaluation_read(&self) -> crate::executor::EvaluationReadScope {
        // A model read receives its ordinary timeout; opting in to a
        // quantified decision backstop does not enlarge getter budgets.
        let controls = self.nominal_native_publication_controls_at(Instant::now());
        self.executor.begin_native_evaluation_read(
            self.interrupt.clone(),
            controls.deadline,
            controls.effective_memory_limit,
            controls.effective_term_memory_limit,
        )
    }

    fn native_publication_controls_at(&self, now: Instant) -> NativePublicationControls {
        self.native_publication_controls_for_roots_at(now, &[])
    }

    fn native_publication_controls_for_roots_at(
        &self,
        now: Instant,
        extra_roots: &[ay_core::TermId],
    ) -> NativePublicationControls {
        let controls = self.nominal_native_publication_controls_at(now);
        let timeout = Self::earliest_optional(self.timeout, self.executor.timeout());
        let plan = self
            .executor
            .decision_deadline_at(now, timeout, extra_roots);
        NativePublicationControls {
            deadline: plan.deadline,
            owner: plan.owner,
            ..controls
        }
    }

    fn nominal_native_publication_controls_at(&self, now: Instant) -> NativePublicationControls {
        let previous_deadline = self.executor.current_solve_deadline();
        let api_deadline = self.timeout.and_then(|timeout| now.checked_add(timeout));
        let parsed_deadline = self
            .executor
            .timeout()
            .and_then(|timeout| now.checked_add(timeout));
        let deadline = Self::earliest_optional(
            previous_deadline,
            Self::earliest_optional(api_deadline, parsed_deadline),
        );
        let previous_memory_limit = self.executor.memory_limit();
        let effective_memory_limit =
            Self::earliest_optional(previous_memory_limit, self.memory_limit);
        let previous_term_memory_limit = self.executor.term_memory_limit();
        let effective_term_memory_limit =
            Self::earliest_optional(previous_term_memory_limit, self.term_memory_limit);
        NativePublicationControls {
            deadline,
            owner: None,
            effective_memory_limit,
            effective_term_memory_limit,
            previous_interrupt: self.executor.current_solve_interrupt(),
            previous_memory_limit,
            previous_term_memory_limit,
        }
    }

    fn earliest_optional<T: Ord>(left: Option<T>, right: Option<T>) -> Option<T> {
        match (left, right) {
            (Some(left), Some(right)) => Some(left.min(right)),
            (Some(value), None) | (None, Some(value)) => Some(value),
            (None, None) => None,
        }
    }

    /// Forward one precomputed control envelope to the executor.
    pub(super) fn install_solve_controls(
        &mut self,
        controls: &NativePublicationControls,
    ) -> crate::executor::CommandDeadlineScope {
        let scope = self
            .executor
            .snapshot_command_publication_deadline(controls.owner.as_ref());
        self.executor
            .set_memory_limit(controls.effective_memory_limit);
        self.executor
            .set_term_memory_limit(controls.effective_term_memory_limit);
        self.executor
            .set_learned_clause_limit(self.learned_clause_limit);
        self.executor
            .set_clause_db_bytes_limit(self.clause_db_bytes_limit);
        if scope.was_active() {
            // A continuation can inherit a narrowed search slice without
            // replacing the command's wider certification envelope.
            self.executor.set_interrupt(self.interrupt.clone());
        } else {
            self.executor
                .set_solve_controls(Some(self.interrupt.clone()), controls.deadline);
        }
        scope
    }

    /// Restore executor-owned controls after every native Result path.
    pub(super) fn restore_solve_controls(
        &mut self,
        controls: &NativePublicationControls,
        deadline_scope: crate::executor::CommandDeadlineScope,
    ) {
        self.executor
            .restore_solve_interrupt(controls.previous_interrupt.clone());
        self.executor
            .set_memory_limit(controls.previous_memory_limit);
        self.executor
            .set_term_memory_limit(controls.previous_term_memory_limit);
        drop(deadline_scope);
    }

    /// Classify an `Unknown` result that has no reason yet, using executor
    /// state, interrupt flag, deadline, and memory limit.
    pub(super) fn classify_unknown_reason(&mut self, controls: &NativePublicationControls) {
        let reason = if let Some(reason) = self.executor.unknown_reason() {
            reason
        } else if self.interrupt.load(Ordering::Relaxed) {
            UnknownReason::Interrupted
        } else if controls.deadline.is_some_and(|d| Instant::now() >= d) {
            UnknownReason::Timeout
        } else if crate::memory::memory_exceeded(controls.effective_memory_limit)
            || ay_sys::process_memory_exceeded()
            || ay_sys::current_memory_group_soft_tripped()
            || controls
                .effective_term_memory_limit
                .is_some_and(|limit| self.terms().instance_memory_exceeded(limit))
        {
            UnknownReason::MemoryLimit
        } else {
            UnknownReason::Incomplete
        };
        self.executor.replace_last_result_with_unknown(reason);
        self.last_unknown_reason = Some(reason);
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
    /// Returns a `VerifiedSolveResult` where Sat results carry sealed admission
    /// provenance. Use
    /// [`was_model_validated()`](VerifiedSolveResult::was_model_validated) to
    /// check whether either ordinary final model validation or an independently
    /// checked constructive model certificate admitted the result. Part of
    /// #5748, #5973.
    pub fn check_sat(&mut self) -> VerifiedSolveResult {
        self.check_sat_with_authority_origin(
            NativeCheckAuthorityOrigin::AuthoredPlain,
            NativeQueryBoundary::External,
        )
    }

    /// Run a solver-internal feasibility query without caller-authored query
    /// authority.
    ///
    /// This is public only so sibling workspace crates such as the CHC proof
    /// and executor adapters can make their synthesized-query origin explicit.
    /// Ordinary embedders should call [`Self::check_sat`].
    #[doc(hidden)]
    pub fn check_sat_internal_query(&mut self) -> VerifiedSolveResult {
        self.check_sat_with_authority_origin(
            NativeCheckAuthorityOrigin::Internal,
            NativeQueryBoundary::External,
        )
    }

    /// Run a native feasibility probe that must never acquire authored-query
    /// authority from reusing the public `Solver` object.
    pub(crate) fn check_sat_internal_api(&mut self) -> VerifiedSolveResult {
        self.check_sat_with_authority_origin(
            NativeCheckAuthorityOrigin::Internal,
            NativeQueryBoundary::Continuation,
        )
    }

    pub(super) fn check_sat_authored_continuation(&mut self) -> VerifiedSolveResult {
        self.check_sat_with_authority_origin(
            NativeCheckAuthorityOrigin::AuthoredPlain,
            NativeQueryBoundary::Continuation,
        )
    }

    fn check_sat_with_authority_origin(
        &mut self,
        authority_origin: NativeCheckAuthorityOrigin,
        boundary: NativeQueryBoundary,
    ) -> VerifiedSolveResult {
        self.clear_last_solve_state_at_boundary(true, false, boundary);
        self.executor.bind_unsat_query_assumptions(&[]);
        self.record_native_replay_event(NativeReplayEventKind::CheckSat);
        if let Some(rejected) = self.reject_native_array_ext_witness_capture(&[]) {
            return rejected;
        }
        self.dump_query_if_requested(&[]);
        if let Some(rejected) = self.reject_mixed_soft_ownership() {
            return rejected;
        }

        let controls = self.native_publication_controls();
        if let Some(early) = self.preflight_check(&controls) {
            return early;
        }

        let native_softs = if authority_origin == NativeCheckAuthorityOrigin::AuthoredPlain {
            self.soft_constraints
                .iter()
                .map(|soft| NativeSoftQueryBinding {
                    term: soft.term.id(),
                    weight: soft.weight,
                    group: soft.group.clone(),
                })
                .collect()
        } else {
            Vec::new()
        };

        let deadline_scope = self.install_solve_controls(&controls);
        self.executor
            .trace_unknown_funnel("native-exec-enter", None, None, false);
        let exec_result = if authority_origin == NativeCheckAuthorityOrigin::AuthoredPlain {
            self.executor.solve_authored_plain_hard_query(&native_softs)
        } else {
            self.executor.check_sat()
        };

        let result = match exec_result {
            Ok(r) => r,
            Err(e) => {
                self.record_executor_failure_unknown(&e);
                SolveResult::Unknown
            }
        };

        self.executor
            .trace_unknown_funnel("native-exec-return", None, Some(&result), false);
        let result = self.executor.certify_unsat_for_publication(result, &[]);
        self.executor
            .trace_unknown_funnel("native-unsat-cert-return", None, Some(&result), false);
        if result == SolveResult::Unknown && self.last_unknown_reason.is_none() {
            self.classify_unknown_reason(&controls);
        }
        // Certification is part of the caller's check-sat transaction. Keep
        // the original absolute deadline and interrupt installed while it runs
        // so a nested trust re-confirmation cannot escape the caller's limits.
        let verified = self.finish_verified_result(result);
        self.executor.trace_unknown_funnel(
            "native-verified-return",
            None,
            Some(verified.result()),
            false,
        );
        self.restore_solve_controls(&controls, deadline_scope);
        verified
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
        self.check_sat_interruptible_with_authority_origin(
            NativeCheckAuthorityOrigin::AuthoredPlain,
            NativeQueryBoundary::External,
            should_stop,
        )
    }

    /// Interruptible solver-internal feasibility query without caller-authored
    /// query authority.
    ///
    /// This mirrors [`Self::check_sat_internal_query`] so a composite caller
    /// cannot accidentally acquire projection authority merely by choosing the
    /// interruptible entrypoint.
    #[doc(hidden)]
    pub fn check_sat_interruptible_internal_query<F>(
        &mut self,
        should_stop: F,
    ) -> VerifiedSolveResult
    where
        F: Fn() -> bool + Send + 'static,
    {
        self.check_sat_interruptible_with_authority_origin(
            NativeCheckAuthorityOrigin::Internal,
            NativeQueryBoundary::External,
            should_stop,
        )
    }

    fn check_sat_interruptible_with_authority_origin<F>(
        &mut self,
        authority_origin: NativeCheckAuthorityOrigin,
        boundary: NativeQueryBoundary,
        should_stop: F,
    ) -> VerifiedSolveResult
    where
        F: Fn() -> bool + Send + 'static,
    {
        self.clear_last_solve_state_at_boundary(true, false, boundary);
        self.executor.bind_unsat_query_assumptions(&[]);
        self.record_native_replay_event(NativeReplayEventKind::CheckSat);
        if let Some(rejected) = self.reject_mixed_soft_ownership() {
            return rejected;
        }

        let controls = self.native_publication_controls();
        if let Some(early) = self.preflight_check(&controls) {
            return early;
        }

        let native_softs = if authority_origin == NativeCheckAuthorityOrigin::AuthoredPlain {
            self.soft_constraints
                .iter()
                .map(|soft| NativeSoftQueryBinding {
                    term: soft.term.id(),
                    weight: soft.weight,
                    group: soft.group.clone(),
                })
                .collect()
        } else {
            Vec::new()
        };
        let deadline_scope = self.install_solve_controls(&controls);
        let publication = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            crate::executor::with_interruptible_publication_context(
                self,
                |solver| &mut solver.executor,
                should_stop,
                |solver| {
                    let exec_result =
                        if authority_origin == NativeCheckAuthorityOrigin::AuthoredPlain {
                            solver
                                .executor
                                .solve_authored_plain_hard_query(&native_softs)
                        } else {
                            solver.executor.check_sat()
                        };
                    let result = match exec_result {
                        Ok(result) => solver.executor.certify_unsat_for_publication(result, &[]),
                        Err(error) => return Err(error),
                    };
                    if result == SolveResult::Unknown && solver.last_unknown_reason.is_none() {
                        solver.classify_unknown_reason(&controls);
                    }
                    Ok(solver.finish_verified_result(result))
                },
                |solver, outcome| match outcome {
                    Ok(verified) => solver.finish_interruptible_publication(verified),
                    Err(error) => {
                        if solver
                            .executor
                            .finalize_external_stop_for_publication()
                            .is_none()
                        {
                            solver.record_executor_failure_unknown(&error);
                        }
                        solver.finish_verified_result(SolveResult::Unknown)
                    }
                },
            )
        }));
        self.restore_solve_controls(&controls, deadline_scope);
        match publication {
            Ok(verified) => verified,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }

    fn finish_interruptible_publication(
        &mut self,
        verified: VerifiedSolveResult,
    ) -> VerifiedSolveResult {
        let result = self
            .executor
            .decline_definite_publication_on_external_stop(verified.result().clone());
        if result.is_unknown() && !verified.is_unknown() {
            self.finish_verified_result(result)
        } else {
            verified
        }
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
        self.check_sat_assuming_at_boundary(assumptions, NativeQueryBoundary::External)
    }

    pub(super) fn check_sat_assuming_continuation(
        &mut self,
        assumptions: &[Term],
    ) -> VerifiedSolveResult {
        self.check_sat_assuming_at_boundary(assumptions, NativeQueryBoundary::Continuation)
    }

    fn check_sat_assuming_at_boundary(
        &mut self,
        assumptions: &[Term],
        boundary: NativeQueryBoundary,
    ) -> VerifiedSolveResult {
        // A malformed/foreign handle still starts a new decision query. Retire
        // the previous result and replenish external query budgets before the
        // first fallible lookup so an early resolution error cannot expose a
        // stale model/certificate or leave a spent finite-array ledger active.
        self.clear_last_solve_state_at_boundary(true, false, boundary);
        let assumption_ids = match self.resolve_terms("check_sat_assuming", assumptions) {
            Ok(ids) => ids,
            Err(error) => {
                self.last_executor_error = Some(error.to_string());
                return self.preflight_unknown(UnknownReason::Incomplete);
            }
        };
        self.executor.bind_native_query_assumptions(&assumption_ids);
        self.record_native_replay_event(NativeReplayEventKind::CheckSatAssuming {
            assumptions: assumption_ids.clone(),
        });
        if let Some(rejected) = self.reject_native_array_ext_witness_capture(assumptions) {
            return rejected;
        }
        self.dump_query_if_requested(assumptions);
        if let Some(rejected) = self.reject_mixed_soft_ownership() {
            return rejected;
        }

        let controls =
            self.native_publication_controls_for_roots_at(Instant::now(), &assumption_ids);
        if let Some(early) = self.preflight_check(&controls) {
            return early;
        }

        let deadline_scope = self.install_solve_controls(&controls);

        self.last_assumptions = Some(
            assumption_ids
                .iter()
                .copied()
                .zip(assumptions.iter().copied())
                .collect(),
        );

        // User-facing entry: named assertions are assumption-tracked when
        // `:produce-unsat-cores` is on, so `try_get_unsat_core` after an
        // assumption-bearing UNSAT includes named participants
        // (#unsat-core-assumptions). Internal solver probes bypass this.
        let exec_result = self
            .executor
            .check_sat_assuming_with_named_cores(&assumption_ids);

        let result = match exec_result {
            Ok(r) => r,
            Err(e) => {
                self.record_executor_failure_unknown(&e);
                SolveResult::Unknown
            }
        };

        let result = self
            .executor
            .certify_unsat_for_publication(result, &assumption_ids);
        if result == SolveResult::Unknown && self.last_unknown_reason.is_none() {
            self.classify_unknown_reason(&controls);
        }
        let verified = self.finish_verified_result(result);
        self.restore_solve_controls(&controls, deadline_scope);
        verified
    }
}

#[cfg(test)]
#[path = "check/fp_namespace_tests.rs"]
mod fp_namespace_tests;

#[cfg(test)]
mod finish_verified_result_tests {
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;

    use super::*;
    use crate::api::Logic;
    use crate::UnknownOrigin;

    #[test]
    fn missing_reused_sat_capability_publishes_registered_unknown_and_revokes_model() {
        let mut solver = Solver::new(Logic::QfLia);
        let x = solver.declare_const("x", crate::api::Sort::Int);
        let five = solver.int_const(5);
        let constraint = solver.eq(x, five);
        solver.assert_term(constraint);
        let first = solver.check_sat();
        assert!(first.is_sat());
        assert!(solver.model().is_some());

        let replayed_definite = first.result().clone();
        let rejected = solver.finish_verified_result(replayed_definite);

        assert!(rejected.is_unknown());
        assert_eq!(
            solver.unknown_reason(),
            Some(UnknownReason::SelfCheckRejected)
        );
        assert_eq!(
            solver.executor.unknown_origin(),
            Some(UnknownOrigin::VerdictCertification)
        );
        assert!(solver.executor.last_result_is_unknown());
        assert!(solver.model().is_none());
        assert!(solver.executor.take_sat_certificate().is_none());
        assert!(solver.executor.take_unsat_certificate().is_none());
    }

    #[test]
    fn control_lifetime_late_interrupt_revokes_sat_before_native_token_admission() {
        let mut solver = Solver::new(Logic::QfUf);
        solver.clear_last_solve_state(true, false);
        solver.executor.bind_unsat_query_assumptions(&[]);
        let proposed = solver
            .executor
            .check_sat()
            .expect("empty authored query must solve");
        assert_eq!(proposed, SolveResult::Sat);
        assert!(solver.executor.was_model_validated());

        solver
            .executor
            .set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);
        let rejected = solver.finish_verified_result(proposed);

        assert!(rejected.is_unknown());
        assert_eq!(solver.unknown_reason(), Some(UnknownReason::Interrupted));
        assert_eq!(
            solver.executor.unknown_origin(),
            Some(UnknownOrigin::InterruptFlag)
        );
        assert!(solver.executor.take_sat_certificate().is_none());
        assert!(solver.executor.take_unsat_certificate().is_none());
        assert!(solver.model().is_none());
        solver.executor.clear_solve_controls();
    }

    #[test]
    fn control_lifetime_native_rss_limit_is_forwarded_to_executor() {
        let mut solver = Solver::new(Logic::QfUf);
        solver.set_memory_limit(Some(1));

        let controls = solver.native_publication_controls();
        let deadline_scope = solver.install_solve_controls(&controls);

        assert_eq!(solver.executor.memory_limit(), Some(1));
        solver.restore_solve_controls(&controls, deadline_scope);
        assert_eq!(solver.executor.memory_limit(), None);
        solver.set_memory_limit(None);
    }

    /// Model an already-elapsed nominal phase with a fixed command origin,
    /// avoiding a machine-speed-sensitive "sleep during search" fixture.
    #[test]
    fn backstop_envelope_native_publication_survives_the_elapsed_nominal_phase() {
        for (script, expected) in [
            (
                "(declare-fun f (Int) Int)
                 (assert (forall ((x Int)) (> (f x) x)))
                 (assert (not (= (f 3) 4)))",
                SolveResult::Sat,
            ),
            (
                "(declare-fun p (Int) Bool)
                 (assert (forall ((x Int)) (p x)))
                 (assert (not (p 0)))",
                SolveResult::unsat(),
            ),
        ] {
            let mut solver = Solver::new(Logic::All);
            solver.parse_smtlib2(script).expect("consumer-shaped query");
            solver.set_timeout(Some(Duration::from_secs(30)));
            solver.set_quantifier_deadline_backstop(true);
            solver.clear_last_solve_state(true, false);
            solver.executor.bind_unsat_query_assumptions(&[]);
            let origin = Instant::now()
                .checked_sub(Duration::from_secs(60))
                .expect("a prior command origin");
            let controls = solver.native_publication_controls_at(origin);
            assert!(
                controls.deadline.is_some_and(|wall| wall > Instant::now()),
                "the explicit backstop must remain live after nominal time elapsed"
            );
            assert!(solver.preflight_check(&controls).is_none());
            let deadline_scope = solver.install_solve_controls(&controls);
            let proposed = solver.executor.check_sat().expect("search");
            assert_eq!(proposed, expected);
            assert_eq!(solver.executor.current_solve_deadline(), controls.deadline);
            let certified = solver.executor.certify_unsat_for_publication(proposed, &[]);
            let admitted = solver.finish_verified_result(certified);
            assert_eq!(admitted.result(), &expected);
            solver.restore_solve_controls(&controls, deadline_scope);
            assert_eq!(solver.executor.current_solve_deadline(), None);
        }
    }

    #[test]
    fn backstop_envelope_public_native_queries_keep_their_result_and_restore_controls() {
        for (script, sat) in [
            (
                "(declare-fun f (Int) Int)
                 (assert (forall ((x Int)) (> (f x) x)))
                 (assert (not (= (f 3) 4)))",
                true,
            ),
            (
                "(declare-fun p (Int) Bool)
                 (assert (forall ((x Int)) (p x)))
                 (assert (not (p 0)))",
                false,
            ),
        ] {
            let mut solver = Solver::new(Logic::All);
            solver.parse_smtlib2(script).expect("consumer-shaped query");
            solver.set_timeout(Some(Duration::from_secs(10)));
            solver.set_quantifier_deadline_backstop(true);
            for assumptions in [false, true] {
                let result = if assumptions {
                    solver.check_sat_assuming(&[])
                } else {
                    solver.check_sat()
                };
                assert_eq!(result.is_sat(), sat);
                assert_eq!(result.is_unsat(), !sat);
                assert_eq!(solver.executor.current_solve_deadline(), None);
            }
        }
    }

    /// Replay the captured consumer obligation with the same complete wall
    /// requested directly and through the explicit quantified backstop.
    #[test]
    #[ntest::timeout(300_000)]
    fn backstop_envelope_captured_deductive_checks_query_certifies_through_the_public_api() {
        let source = include_str!(
            "../../../tests/fixtures/deductive_checks_certification_envelope/refutation_loop_push_appends_entailed.smt2"
        );
        let (logic, body) = crate::api::split_leading_set_logic(source, Logic::All);
        for (seconds, backstop) in [(120, false), (30, true)] {
            let mut solver = Solver::new(logic);
            solver
                .parse_smtlib2(&body)
                .expect("captured deductive-checks query");
            solver.set_timeout(Some(Duration::from_secs(seconds)));
            solver.set_quantifier_deadline_backstop(backstop);
            let started = Instant::now();
            let result = solver.check_sat();
            assert!(
                result.is_unsat(),
                "backstop={backstop}: {result:?}, reason={:?}, elapsed={:?}",
                solver.unknown_reason(),
                started.elapsed()
            );
            assert_eq!(solver.executor.current_solve_deadline(), None);
        }
    }

    #[test]
    fn backstop_envelope_uses_the_tighter_relative_timeout_without_extending_getters() {
        let mut solver = Solver::new(Logic::All);
        solver
            .parse_smtlib2(
                "(set-option :timeout 1000)
             (declare-fun f (Int) Int)
             (assert (forall ((x Int)) (> (f x) x)))",
            )
            .expect("quantified query and parsed timeout");
        solver.set_timeout(Some(Duration::from_secs(10)));
        solver.set_quantifier_deadline_backstop(true);
        let now = Instant::now();
        assert_eq!(
            solver.native_publication_controls_at(now).deadline,
            now.checked_add(Duration::from_secs(4))
        );
        assert_eq!(
            solver.nominal_native_publication_controls_at(now).deadline,
            now.checked_add(Duration::from_secs(1))
        );
    }

    #[test]
    fn backstop_envelope_quantified_assumptions_use_one_complete_native_grant() {
        let mut solver = Solver::new(Logic::All);
        let assertions = solver
            .parse_smtlib2(
                "(declare-fun p (Int) Bool)
                 (assert (forall ((x Int)) (p x)))
                 (assert (not (p 0)))",
            )
            .expect("quantified assumption and ground contradiction");
        solver.try_reset_assertions().expect("retain declarations");
        solver.assert_term(assertions[1]);
        solver.set_timeout(Some(Duration::from_secs(10)));
        solver.set_quantifier_deadline_backstop(true);
        let now = Instant::now();
        assert_eq!(
            solver.native_publication_controls_at(now).deadline,
            Some(now + Duration::from_secs(10)),
            "the hard query is ground"
        );
        assert_eq!(
            solver
                .native_publication_controls_for_roots_at(now, &[assertions[0].id()])
                .deadline,
            Some(now + Duration::from_secs(40)),
            "the quantified assumption belongs to the decision envelope"
        );
        assert!(solver.check_sat_assuming(&[assertions[0]]).is_unsat());
        assert_eq!(solver.executor.current_solve_deadline(), None);
        assert!(solver.check_sat().is_sat(), "the assumption was temporary");
    }

    #[test]
    fn backstop_envelope_native_cleanup_restores_the_original_interrupt_handle() {
        let mut solver = Solver::new(Logic::All);
        solver
            .parse_smtlib2("(declare-fun p (Int) Bool) (assert (forall ((x Int)) (p x)))")
            .expect("quantified query");
        solver.set_timeout(Some(Duration::from_secs(10)));
        solver.set_quantifier_deadline_backstop(true);
        let original = Arc::new(AtomicBool::new(false));
        solver.executor.set_interrupt(original.clone());
        let controls = solver.native_publication_controls();
        let scope = solver.install_solve_controls(&controls);
        solver.restore_solve_controls(&controls, scope);
        let restored = solver
            .executor
            .current_solve_interrupt()
            .expect("original controller");
        assert!(Arc::ptr_eq(&original, &restored));
    }

    #[test]
    fn backstop_envelope_optimization_uses_only_the_formulas_it_solves() {
        let mut native = Solver::new(Logic::All);
        let quantified = native
            .parse_smtlib2("(declare-fun p (Int) Bool) (assert (forall ((x Int)) (p x)))")
            .expect("quantified soft formula")[0];
        native.try_reset_assertions().expect("retain declarations");
        native
            .assert_soft(quantified, 1, None)
            .expect("native soft");
        native.set_timeout(Some(Duration::from_secs(10)));
        native.set_quantifier_deadline_backstop(true);
        let now = Instant::now();
        assert_eq!(
            native.native_publication_controls_at(now).deadline,
            Some(now + Duration::from_secs(10))
        );
        assert_eq!(
            native.native_maxsmt_publication_controls_at(now).deadline,
            Some(now + Duration::from_secs(40))
        );
        assert_eq!(
            native
                .native_optimization_publication_controls_at(now)
                .deadline,
            Some(now + Duration::from_secs(40))
        );
        assert!(
            native.check_sat().is_sat(),
            "hard feasibility ignores the soft formula"
        );

        for formula in [
            "(assert-soft (forall ((x Int)) (p x)))",
            "(minimize (ite (forall ((x Int)) (p x)) 0 1))",
        ] {
            let mut parsed = Solver::new(Logic::All);
            parsed
                .parse_smtlib2(&format!("(declare-fun p (Int) Bool) {formula}"))
                .expect("parsed optimization formula");
            parsed.set_timeout(Some(Duration::from_secs(10)));
            parsed.set_quantifier_deadline_backstop(true);
            assert_eq!(
                parsed.native_publication_controls_at(now).deadline,
                Some(now + Duration::from_secs(10))
            );
            assert_eq!(
                parsed.native_maxsmt_publication_controls_at(now).deadline,
                Some(now + Duration::from_secs(10))
            );
            assert_eq!(
                parsed
                    .native_optimization_publication_controls_at(now)
                    .deadline,
                Some(now + Duration::from_secs(40))
            );
            parsed.set_quantifier_deadline_backstop(false);
            assert_eq!(
                parsed
                    .native_optimization_publication_controls_at(now)
                    .deadline,
                Some(now + Duration::from_secs(10))
            );
        }
    }

    #[test]
    fn backstop_envelope_interruptible_owner_lives_through_native_capability_consumption() {
        struct Owner(Arc<AtomicBool>);
        impl Owner {
            fn touch(&self) {}
        }
        impl Drop for Owner {
            fn drop(&mut self) {
                self.0.store(true, Ordering::Relaxed);
            }
        }
        let mut solver = Solver::new(Logic::QfUf);
        solver.clear_last_solve_state(true, false);
        solver.executor.bind_unsat_query_assumptions(&[]);
        let controls = solver.native_publication_controls();
        let scope = solver.install_solve_controls(&controls);
        let dropped = Arc::new(AtomicBool::new(false));
        let owner = Owner(dropped.clone());
        let result = crate::executor::with_interruptible_publication_context(
            &mut solver,
            |solver| &mut solver.executor,
            move || {
                owner.touch();
                false
            },
            |solver| {
                let proposed = solver.executor.check_sat().expect("search");
                assert!(!dropped.load(Ordering::Relaxed));
                let admitted = solver.finish_verified_result(proposed);
                assert!(admitted.is_sat());
                assert!(
                    !dropped.load(Ordering::Relaxed),
                    "the per-call owner must outlive native capability consumption"
                );
                admitted
            },
            Solver::finish_interruptible_publication,
        );
        assert!(result.is_sat());
        assert!(dropped.load(Ordering::Relaxed));
        solver.restore_solve_controls(&controls, scope);
    }

    #[test]
    fn backstop_envelope_interruptible_cleanup_cannot_escape_the_native_interrupt() {
        struct Owner(Arc<AtomicBool>);
        impl Owner {
            fn touch(&self) {}
        }
        impl Drop for Owner {
            fn drop(&mut self) {
                self.0.store(true, Ordering::Relaxed);
            }
        }
        let mut solver = Solver::new(Logic::QfUf);
        let owner = Owner(solver.interrupt_handle());
        let result = solver.check_sat_interruptible(move || {
            owner.touch();
            false
        });
        assert!(result.is_unknown());
        assert_eq!(solver.unknown_reason(), Some(UnknownReason::Interrupted));
        assert!(solver.model().is_none());
        solver.clear_interrupt();
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn backstop_envelope_interruptible_initial_callback_unwind_restores_native_controls() {
        let mut solver = Solver::new(Logic::QfUf);
        let original = Arc::new(AtomicBool::new(false));
        let deadline = Instant::now() + Duration::from_secs(30);
        solver
            .executor
            .set_solve_controls(Some(original.clone()), Some(deadline));
        solver.executor.set_memory_limit(Some(usize::MAX));
        solver.set_timeout(Some(Duration::from_secs(10)));
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = solver.check_sat_interruptible(|| panic!("initial caller callback"));
        }));
        assert!(outcome.is_err());
        assert_eq!(solver.executor.current_solve_deadline(), Some(deadline));
        assert_eq!(solver.executor.memory_limit(), Some(usize::MAX));
        assert!(Arc::ptr_eq(
            &solver
                .executor
                .current_solve_interrupt()
                .expect("original interrupt"),
            &original
        ));
    }

    #[test]
    fn backstop_envelope_late_cancellation_revokes_publication_without_leaking_a_deadline() {
        let mut solver = Solver::new(Logic::All);
        solver
            .parse_smtlib2(
                "(declare-fun f (Int) Int)
             (assert (forall ((x Int)) (> (f x) x)))
             (assert (not (= (f 3) 4)))",
            )
            .expect("consumer-shaped SAT query");
        solver.set_timeout(Some(Duration::from_secs(10)));
        solver.set_quantifier_deadline_backstop(true);
        solver.clear_last_solve_state(true, false);
        solver.executor.bind_unsat_query_assumptions(&[]);
        let controls = solver.native_publication_controls();
        let scope = solver.install_solve_controls(&controls);
        let proposed = solver.executor.check_sat().expect("search");
        assert_eq!(proposed, SolveResult::Sat);
        solver.interrupt();
        assert!(solver.finish_verified_result(proposed).is_unknown());
        assert_eq!(solver.unknown_reason(), Some(UnknownReason::Interrupted));
        solver.restore_solve_controls(&controls, scope);
        assert_eq!(solver.executor.current_solve_deadline(), None);
        solver.clear_interrupt();
        assert!(solver.check_sat().is_sat());
    }

    #[test]
    fn control_lifetime_native_term_limit_is_forwarded_to_executor() {
        let mut solver = Solver::new(Logic::QfUf);
        solver.set_term_memory_limit(Some(1));

        let controls = solver.native_publication_controls();
        let deadline_scope = solver.install_solve_controls(&controls);

        assert_eq!(solver.executor.term_memory_limit(), Some(1));
        solver.restore_solve_controls(&controls, deadline_scope);
        assert_eq!(solver.executor.term_memory_limit(), None);
        solver.set_term_memory_limit(None);
    }

    #[test]
    fn control_lifetime_native_deadline_uses_earliest_timeout_from_one_origin() {
        let mut solver = Solver::new(Logic::QfUf);
        solver
            .parse_smtlib2("(set-option :timeout 7)")
            .expect("parsed timeout");
        solver.set_timeout(Some(Duration::from_secs(30)));

        let now = Instant::now();
        let controls = solver.native_publication_controls_at(now);
        assert_eq!(controls.deadline, now.checked_add(Duration::from_millis(7)));
        assert_eq!(solver.executor.timeout(), Some(Duration::from_millis(7)));

        let deadline_scope = solver.install_solve_controls(&controls);
        assert_eq!(solver.executor.current_solve_deadline(), controls.deadline);
        solver.restore_solve_controls(&controls, deadline_scope);
        assert_eq!(solver.executor.current_solve_deadline(), None);
        assert_eq!(
            solver.executor.timeout(),
            Some(Duration::from_millis(7)),
            "native cleanup must not consume or renew parsed timeout configuration"
        );

        solver
            .parse_smtlib2("(set-option :timeout 7000)")
            .expect("replace parsed timeout");
        solver.set_timeout(Some(Duration::from_millis(3)));
        let now = Instant::now();
        let controls = solver.native_publication_controls_at(now);
        assert_eq!(
            controls.deadline,
            now.checked_add(Duration::from_millis(3)),
            "the API timeout must win when it is tighter"
        );
    }

    #[test]
    fn control_lifetime_native_rss_uses_tighter_parsed_or_api_limit_and_restores_it() {
        const MIB: usize = 1024 * 1024;
        let mut solver = Solver::new(Logic::QfUf);
        solver
            .parse_smtlib2("(set-option :max-memory 64)")
            .expect("parsed memory limit");

        solver.set_memory_limit(Some(128 * MIB));
        let controls = solver.native_publication_controls();
        assert_eq!(controls.effective_memory_limit, Some(64 * MIB));
        let deadline_scope = solver.install_solve_controls(&controls);
        assert_eq!(solver.executor.memory_limit(), Some(64 * MIB));
        solver.restore_solve_controls(&controls, deadline_scope);
        assert_eq!(solver.executor.memory_limit(), Some(64 * MIB));

        solver.set_memory_limit(Some(32 * MIB));
        let controls = solver.native_publication_controls();
        assert_eq!(controls.effective_memory_limit, Some(32 * MIB));
        let deadline_scope = solver.install_solve_controls(&controls);
        assert_eq!(solver.executor.memory_limit(), Some(32 * MIB));
        solver.restore_solve_controls(&controls, deadline_scope);
        assert_eq!(
            solver.executor.memory_limit(),
            Some(64 * MIB),
            "native cleanup must restore the parsed executor ceiling"
        );
    }

    #[test]
    fn control_lifetime_parsed_deadline_survives_solve_and_revokes_unsat_certification() {
        let mut solver = Solver::new(Logic::QfUf);
        solver
            .parse_smtlib2("(set-option :timeout 60000) (assert false)")
            .expect("parsed timeout and contradiction");
        solver.clear_last_solve_state(true, false);
        solver.executor.bind_unsat_query_assumptions(&[]);

        let controls = solver.native_publication_controls();
        let deadline_scope = solver.install_solve_controls(&controls);
        let proposed = solver
            .executor
            .check_sat()
            .expect("false must solve before the publication deadline expires");
        assert!(proposed.is_unsat());
        assert_eq!(
            solver.executor.current_solve_deadline(),
            controls.deadline,
            "the executor's nested relative-timeout scope must restore the one publication deadline"
        );

        // Deterministically model the same absolute deadline expiring after
        // search but before strict UNSAT certification.
        solver.executor.set_deadline(Some(Instant::now()));
        let rejected = solver.executor.certify_unsat_for_publication(proposed, &[]);
        assert!(rejected.is_unknown());
        assert_eq!(
            solver.executor.unknown_reason(),
            Some(UnknownReason::Timeout)
        );

        let verified = solver.finish_verified_result(rejected);
        assert!(verified.is_unknown());
        solver.restore_solve_controls(&controls, deadline_scope);
        assert_eq!(solver.executor.current_solve_deadline(), None);
        assert_eq!(solver.executor.timeout(), Some(Duration::from_mins(1)));
    }

    #[test]
    fn control_lifetime_late_term_memory_stop_revokes_native_sat() {
        let mut solver = Solver::new(Logic::QfUf);
        solver.clear_last_solve_state(true, false);
        solver.executor.bind_unsat_query_assumptions(&[]);
        let proposed = solver
            .executor
            .check_sat()
            .expect("empty authored query must solve");
        assert_eq!(proposed, SolveResult::Sat);
        assert!(solver.executor.was_model_validated());

        solver.set_term_memory_limit(Some(0));
        assert!(solver.terms().instance_memory_exceeded(0));
        let rejected = solver.finish_verified_result(proposed);

        assert!(rejected.is_unknown());
        assert_eq!(solver.unknown_reason(), Some(UnknownReason::MemoryLimit));
        assert_eq!(
            solver.executor.unknown_origin(),
            Some(UnknownOrigin::MemoryBudget)
        );
        assert!(solver.executor.take_sat_certificate().is_none());
        assert!(solver.executor.take_unsat_certificate().is_none());
        assert!(solver.model().is_none());
    }

    #[test]
    fn control_lifetime_exact_term_census_revokes_native_sat_inside_cache_window() {
        let mut solver = Solver::new(Logic::QfUf);
        solver.clear_last_solve_state(true, false);
        solver.executor.bind_unsat_query_assumptions(&[]);
        let proposed = solver
            .executor
            .check_sat()
            .expect("empty authored query must solve");
        assert_eq!(proposed, SolveResult::Sat);

        let exact_limit = solver.terms().true_memory_bytes();
        assert!(!solver.terms().instance_memory_exceeded(exact_limit));
        let incremental_before = solver.terms().instance_term_bytes();
        for index in 0..512 {
            let _ = solver.executor.ctx.terms.mk_var(
                format!("exact_landing_padding_{index}"),
                crate::api::Sort::Bool,
            );
            if solver.terms().true_memory_bytes() > exact_limit {
                break;
            }
        }
        assert!(solver.terms().true_memory_bytes() > exact_limit);
        assert!(
            solver
                .terms()
                .instance_term_bytes()
                .saturating_sub(incremental_before)
                < 64 * 1024,
            "fixture must stay inside the cached counter's refresh window"
        );
        assert!(
            !solver.terms().instance_memory_exceeded(exact_limit),
            "cached hot-loop check must remain stale so this pins the exact landing census"
        );

        solver.set_term_memory_limit(Some(exact_limit));
        let rejected = solver.finish_verified_result(proposed);
        assert!(rejected.is_unknown());
        assert_eq!(solver.unknown_reason(), Some(UnknownReason::MemoryLimit));
    }

    #[test]
    fn missing_reused_unsat_capability_publishes_registered_unknown_and_revokes_proof() {
        let mut solver = Solver::new(Logic::QfLia);
        solver.set_produce_proofs(true);
        let contradiction = solver.bool_const(false);
        solver.assert_term(contradiction);
        let first = solver.check_sat();
        assert!(first.is_unsat());
        assert!(solver.last_proof().is_some());

        let replayed_definite = first.result().clone();
        let rejected = solver.finish_verified_result(replayed_definite);

        assert!(rejected.is_unknown());
        assert_eq!(
            solver.unknown_reason(),
            Some(UnknownReason::SelfCheckRejected)
        );
        assert_eq!(
            solver.executor.unknown_origin(),
            Some(UnknownOrigin::VerdictCertification)
        );
        assert!(solver.executor.last_result_is_unknown());
        assert!(solver.last_proof().is_none());
        assert!(solver.try_get_unsat_core().is_err());
        assert!(solver.executor.take_sat_certificate().is_none());
        assert!(solver.executor.take_unsat_certificate().is_none());
    }
}

#[cfg(test)]
mod authority_tests {
    use crate::api::{Logic, Solver};

    #[test]
    fn native_authored_and_internal_entrypoints_have_distinct_authority() {
        let mut solver = Solver::new(Logic::QfUf);
        let truth = solver.bool_const(true);
        solver.assert_term(truth);

        let _ = solver.check_sat();
        assert!(solver.executor.last_check_saw_authored_query_authority());

        let _ = solver.check_sat_internal_query();
        assert!(
            !solver.executor.last_check_saw_authored_query_authority(),
            "a composite/native internal probe cannot inherit public-method authority"
        );

        let _ = solver.check_sat_interruptible(|| false);
        assert!(
            solver.executor.last_check_saw_authored_query_authority(),
            "caller-authored interruptible check-sat must retain authored authority"
        );

        let _ = solver.check_sat_interruptible_internal_query(|| false);
        assert!(
            !solver.executor.last_check_saw_authored_query_authority(),
            "an interruptible internal probe cannot inherit public-method authority"
        );

        let _ = solver.check_sat_assuming(&[]);
        assert!(
            !solver.executor.last_check_saw_authored_query_authority(),
            "empty check-sat-assuming remains a distinct query kind"
        );
    }

    #[test]
    fn api_owned_soft_constraint_blocks_plain_hard_permit() {
        let mut solver = Solver::new(Logic::QfUf);
        let truth = solver.bool_const(true);
        solver.assert_term(truth);
        solver
            .assert_soft(truth, 7, Some("native"))
            .expect("well-sorted native soft");

        let _ = solver.check_sat();

        assert!(
            !solver.executor.last_check_saw_authored_query_authority(),
            "API-owned softs are outside the frontend Context and must be bound explicitly"
        );
    }

    #[test]
    fn composite_optimization_entrypoints_cannot_inherit_plain_authority() {
        let mut optimize = Solver::new(Logic::QfUf);
        let truth = optimize.bool_const(true);
        optimize.assert_term(truth);
        let _ = optimize.optimize_check();
        assert!(
            !optimize.executor.last_check_saw_authored_query_authority(),
            "optimize_check remains a composite query even without objectives"
        );

        let mut maxsmt = Solver::new(Logic::QfUf);
        let truth = maxsmt.bool_const(true);
        maxsmt.assert_term(truth);
        let _ = maxsmt
            .check_sat_max()
            .expect("zero-soft MaxSMT delegates to an internal feasibility check");
        assert!(
            !maxsmt.executor.last_check_saw_authored_query_authority(),
            "check_sat_max remains a composite query even without soft constraints"
        );
    }
}
