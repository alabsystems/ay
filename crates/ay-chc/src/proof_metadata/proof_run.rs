// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Solver-owned CHC proof runs and their problem-bound evidence surfaces.

use super::*;

/// Shared problem storage whose final owner always uses iterative teardown.
pub(super) struct IterativeDropProblem(ChcProblem);

impl IterativeDropProblem {
    fn new(problem: ChcProblem) -> Self {
        Self(problem)
    }

    fn get(&self) -> &ChcProblem {
        &self.0
    }
}

impl Drop for IterativeDropProblem {
    fn drop(&mut self) {
        std::mem::take(&mut self.0).iterative_drop();
    }
}

impl std::fmt::Debug for ChcPdrProofRun {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ChcPdrProofRun")
            .field("problem", &self.metadata.normalized_input_sha256())
            .field("result", &self.result)
            .field("metadata", &self.metadata)
            .finish()
    }
}

/// Immutable access to a problem-bound CHC proof run.
///
/// Construction stays inside `ay-chc`, so external code cannot bind a result
/// to a different problem after solving:
///
/// ```compile_fail
/// use ay_chc::{ChcPdrProofRun, ChcProblem, VerifiedChcResult};
///
/// fn rebind(problem: ChcProblem, result: VerifiedChcResult) -> ChcPdrProofRun {
///     ChcPdrProofRun::new(problem, result, "caller-selected-engine")
/// }
/// ```
///
/// The bound result is likewise read-only:
///
/// ```compile_fail
/// use ay_chc::{ChcPdrProofRun, VerifiedChcResult};
///
/// fn replace_result(run: &mut ChcPdrProofRun, result: VerifiedChcResult) {
///     run.result = result;
/// }
/// ```
impl ChcPdrProofRun {
    pub(crate) fn new(
        problem: ChcProblem,
        result: VerifiedChcResult,
        engine: impl Into<String>,
    ) -> Self {
        let metadata = result.proof_transcript_metadata(&problem, engine);
        Self {
            problem: std::sync::Arc::new(IterativeDropProblem::new(problem)),
            result,
            metadata,
        }
    }

    pub(super) fn with_metadata(&self, metadata: ChcProofTranscriptMetadata) -> Self {
        Self {
            problem: self.problem.clone(),
            result: self.result.clone(),
            metadata,
        }
    }

    /// Return the exact normalized problem this run solved and verified.
    pub fn problem(&self) -> &ChcProblem {
        self.problem.get()
    }

    /// Return the sealed verified result.
    pub fn result(&self) -> &VerifiedChcResult {
        &self.result
    }

    /// Return deterministic proof/transcript metadata bound to [`Self::problem`].
    pub fn metadata(&self) -> &ChcProofTranscriptMetadata {
        &self.metadata
    }

    /// Returns true only for proof-grade Safe/Unsafe evidence.
    pub fn accepted_as_proof(&self) -> bool {
        matches!(
            self.result,
            VerifiedChcResult::Safe(_) | VerifiedChcResult::Unsafe(_)
        )
    }

    /// Build typed consumer evidence bound to [`Self::problem`].
    pub fn consumer_evidence(&self) -> ChcProofTranscriptConsumerEvidence {
        ChcProofTranscriptConsumerEvidence::for_run(self)
    }

    /// Emit the model/counterexample artifact bound to [`Self::problem`].
    pub fn model_artifact(&self) -> ChcProofRunArtifact {
        let bytes = serde_json::json!({
            "schema": CHC_PROOF_RUN_MODEL_ARTIFACT_SCHEMA,
            "schema_version": 1,
            "role": CHC_PROOF_RUN_MODEL_ARTIFACT_ROLE,
            "producer": "ay-chc",
            "consumer_evidence": self.consumer_evidence().to_json_value(),
        })
        .to_string()
        .into_bytes();
        ChcProofRunArtifact::new(
            CHC_PROOF_RUN_MODEL_ARTIFACT_SCHEMA,
            CHC_PROOF_RUN_MODEL_ARTIFACT_ROLE,
            bytes,
        )
    }

    /// Emit replay transcript metadata bound to [`Self::problem`].
    pub fn replay_transcript_artifact(&self) -> ChcProofRunArtifact {
        let bytes = serde_json::json!({
            "schema": CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_SCHEMA,
            "schema_version": 1,
            "role": CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_ROLE,
            "producer": "ay-chc",
            "transcript_metadata": self.metadata.to_json_value(),
        })
        .to_string()
        .into_bytes();
        ChcProofRunArtifact::new(
            CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_SCHEMA,
            CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_ROLE,
            bytes,
        )
    }

    /// Emit both first-class artifacts required by native proof handoff.
    pub fn proof_run_artifacts(&self) -> ChcProofRunArtifacts {
        ChcProofRunArtifacts {
            model: self.model_artifact(),
            quantifier_free_invariant_model: self.quantifier_free_invariant_model_artifact().ok(),
            replay_transcript: self.replay_transcript_artifact(),
        }
    }

    /// Validate supplied model artifact bytes against this run.
    pub fn validate_model_artifact_bytes(
        &self,
        bytes: &[u8],
    ) -> Result<ChcProofRunArtifact, ChcProofRunArtifactValidationError> {
        validate_artifact_bytes(self.model_artifact(), bytes)
    }

    /// Validate supplied transcript artifact bytes against this run.
    pub fn validate_replay_transcript_artifact_bytes(
        &self,
        bytes: &[u8],
    ) -> Result<ChcProofRunArtifact, ChcProofRunArtifactValidationError> {
        validate_artifact_bytes(self.replay_transcript_artifact(), bytes)
    }

    /// Validate the complete model/replay artifact pair.
    pub fn validate_model_replay_artifact_bytes(
        &self,
        model_bytes: Option<&[u8]>,
        replay_bytes: Option<&[u8]>,
    ) -> Result<ChcProofRunArtifacts, ChcProofRunArtifactBundleValidationError> {
        let model_bytes = model_bytes.ok_or_else(|| {
            ChcProofRunArtifactBundleValidationError::new(
                ChcProofRunArtifactBundleValidationErrorReason::MissingModelArtifactBytes,
                None,
            )
        })?;
        let replay_bytes = replay_bytes.ok_or_else(|| {
            ChcProofRunArtifactBundleValidationError::new(
                ChcProofRunArtifactBundleValidationErrorReason::MissingReplayTranscriptArtifactBytes,
                None,
            )
        })?;
        let model = self
            .validate_model_artifact_bytes(model_bytes)
            .map_err(|error| {
                ChcProofRunArtifactBundleValidationError::new(
                    ChcProofRunArtifactBundleValidationErrorReason::ModelArtifactMismatch,
                    Some(error),
                )
            })?;
        let replay_transcript = self
            .validate_replay_transcript_artifact_bytes(replay_bytes)
            .map_err(|error| {
                ChcProofRunArtifactBundleValidationError::new(
                    ChcProofRunArtifactBundleValidationErrorReason::ReplayTranscriptArtifactMismatch,
                    Some(error),
                )
            })?;
        Ok(ChcProofRunArtifacts {
            model,
            quantifier_free_invariant_model: self.quantifier_free_invariant_model_artifact().ok(),
            replay_transcript,
        })
    }

    /// Build an evidence manifest bound to [`Self::problem`].
    pub fn evidence_manifest(
        &self,
        options: ChcProofEvidenceOptions,
        solver: ChcProofSolverIdentity,
        obligation_id: impl Into<String>,
    ) -> ChcProofEvidenceManifest {
        ChcProofEvidenceManifest::for_run(self, options, solver, obligation_id)
    }

    /// Build a manifest with concrete replay artifacts bound to this run.
    pub fn evidence_manifest_with_replay_evidence(
        &self,
        options: ChcProofEvidenceOptions,
        solver: ChcProofSolverIdentity,
        obligation_id: impl Into<String>,
        replay_evidence: ChcReplayEvidence,
    ) -> ChcProofEvidenceManifest {
        ChcProofEvidenceManifest::for_run_with_replay_evidence(
            self,
            options,
            solver,
            obligation_id,
            Some(replay_evidence),
        )
    }
}

impl crate::AdaptivePortfolio {
    /// Solve and atomically bind the verified result to this portfolio's problem.
    pub fn solve_proof_run(&self) -> ChcPdrProofRun {
        let result = self.solve();
        ChcPdrProofRun::new(self.problem.clone(), result, "portfolio")
    }

    /// Solve once and atomically return problem-bound evidence together with
    /// telemetry from that same authoritative invocation.
    pub fn solve_proof_run_with_budget_report(&self) -> ChcProofRunWithBudgetReport {
        // AdaptivePortfolio's reporting entry point deliberately invokes the
        // exact production `solve()` pipeline and publishes only telemetry it
        // can bind to that invocation. It does not run a second diagnostic
        // portfolio or select report-only prepasses.
        let (result, adaptive_report) = self.solve_with_adaptive_report();
        let (budget_report, adaptive_trace) = adaptive_report.into_parts();
        // This is a completion-boundary snapshot, not a causal claim: a token
        // can race with any observation. Definitive evidence takes precedence
        // below, and the public accessor names the snapshot semantics.
        let cancellation_requested_at_return = self.cancellation_token.is_cancelled();
        let configured_budget =
            (!self.config.time_budget.is_zero()).then_some(self.config.time_budget);
        let stop_reason = ChcProofRunWithBudgetReport::classify_stop_reason(
            &result,
            cancellation_requested_at_return,
            configured_budget,
            budget_report.total_elapsed,
        );
        ChcProofRunWithBudgetReport {
            proof_run: ChcPdrProofRun::new(self.problem.clone(), result, "portfolio"),
            budget_report,
            adaptive_trace,
            stop_reason,
            cancellation_requested_at_return,
        }
    }
}

impl ChcProofRunWithBudgetReport {
    pub(crate) fn from_direct_pdr(
        proof_run: ChcPdrProofRun,
        configured_budget: Option<std::time::Duration>,
        elapsed: std::time::Duration,
        cancellation_requested_at_return: bool,
    ) -> Self {
        let stop_reason = Self::classify_stop_reason(
            proof_run.result(),
            cancellation_requested_at_return,
            configured_budget,
            elapsed,
        );
        let adaptive_trace = crate::AdaptiveSolveTrace::direct_pdr_proof(
            configured_budget,
            elapsed,
            proof_run.result(),
        );
        let mut budget_report = crate::BudgetReport::new();
        budget_report.total_elapsed = elapsed;
        Self {
            proof_run,
            budget_report,
            adaptive_trace,
            stop_reason,
            cancellation_requested_at_return,
        }
    }

    fn classify_stop_reason(
        result: &VerifiedChcResult,
        cancellation_requested_at_return: bool,
        configured_budget: Option<std::time::Duration>,
        elapsed: std::time::Duration,
    ) -> ChcProofRunStopReason {
        if matches!(
            result,
            VerifiedChcResult::Safe(_) | VerifiedChcResult::Unsafe(_)
        ) {
            ChcProofRunStopReason::Definitive
        } else if cancellation_requested_at_return {
            ChcProofRunStopReason::ExternallyCancelled
        } else if configured_budget.is_some_and(|budget| elapsed >= budget) {
            ChcProofRunStopReason::BudgetExhausted
        } else {
            ChcProofRunStopReason::Inconclusive
        }
    }

    /// Exact problem-bound result and proof artifacts.
    pub fn proof_run(&self) -> &ChcPdrProofRun {
        &self.proof_run
    }

    /// Whole-run elapsed-time report from the same invocation.
    ///
    /// `entries` is empty because specialized adaptive lanes do not all map to
    /// concrete engine identities. Use [`adaptive_trace`](Self::adaptive_trace)
    /// for complete production-dispatch attribution.
    pub fn budget_report(&self) -> &crate::BudgetReport {
        &self.budget_report
    }

    /// Ordered strategy/lane observations from the same authoritative solve.
    pub fn adaptive_trace(&self) -> &crate::AdaptiveSolveTrace {
        &self.adaptive_trace
    }

    /// Whole-run structured stop reason.
    pub fn stop_reason(&self) -> ChcProofRunStopReason {
        self.stop_reason
    }

    /// Whether the embedding caller's cancellation token was set at the
    /// completion-boundary snapshot.
    ///
    /// This does not claim that cancellation caused the verdict: a caller may
    /// request it concurrently with completion. [`stop_reason`](Self::stop_reason)
    /// gives definitive evidence precedence over that race.
    pub fn cancellation_requested_at_return(&self) -> bool {
        self.cancellation_requested_at_return
    }

    /// Consume the bundle without discarding any telemetry fields.
    pub fn into_parts(
        self,
    ) -> (
        ChcPdrProofRun,
        crate::BudgetReport,
        crate::AdaptiveSolveTrace,
        ChcProofRunStopReason,
        bool,
    ) {
        (
            self.proof_run,
            self.budget_report,
            self.adaptive_trace,
            self.stop_reason,
            self.cancellation_requested_at_return,
        )
    }
}

fn validate_artifact_bytes(
    expected: ChcProofRunArtifact,
    bytes: &[u8],
) -> Result<ChcProofRunArtifact, ChcProofRunArtifactValidationError> {
    if expected.bytes() == bytes {
        Ok(expected)
    } else {
        Err(ChcProofRunArtifactValidationError::digest_mismatch(
            &expected, bytes,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine_result::ValidationEvidence;
    use crate::{ChcEngineResult, ChcParser, ChcVar, ClauseBody};

    fn parse_problem(query: &str) -> ChcProblem {
        ChcParser::parse(&format!(
            r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) {query}) false)))
(check-sat)
"#,
        ))
        .expect("authority fixture should parse")
    }

    fn deep_drop_problem(depth: usize) -> ChcProblem {
        let mut problem = ChcProblem::new();
        let predicate = problem.declare_predicate("Deep", vec![ChcSort::Int]);
        let variable = ChcVar::new("x", ChcSort::Int);
        let argument = ChcExpr::var(variable);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::Bool(true)),
            ClauseHead::Predicate(predicate, vec![ChcExpr::int(0)]),
        ));
        let mut deep = ChcExpr::Int(0);
        for _ in 0..depth {
            deep = ChcExpr::add(argument.clone(), deep);
        }
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(predicate, vec![argument])], Some(deep)),
            ClauseHead::False,
        ));
        problem
    }

    #[test]
    fn all_run_surfaces_use_the_owned_problem_authority() {
        let problem = parse_problem("(< x 0)");
        let other_problem = parse_problem("(<= x 0)");
        let expected_hash = problem.normalized_input_sha256();
        assert_ne!(expected_hash, other_problem.normalized_input_sha256());
        let result = VerifiedChcResult::from_validated(
            ChcEngineResult::Unknown,
            ValidationEvidence::FullVerification,
        );
        let run = ChcPdrProofRun::new(problem, result, "authority-test");

        assert_eq!(run.problem().normalized_input_sha256(), expected_hash);
        assert_eq!(run.metadata().normalized_input_sha256(), expected_hash);
        assert_eq!(
            run.consumer_evidence().normalized_input_sha256(),
            expected_hash
        );

        let model: serde_json::Value = serde_json::from_slice(run.model_artifact().bytes())
            .expect("model artifact should be JSON");
        assert_eq!(
            model["consumer_evidence"]["normalized_input_sha256"],
            expected_hash
        );

        let manifest = run.evidence_manifest(
            ChcProofEvidenceOptions::pdr(&PdrConfig::default()),
            ChcProofSolverIdentity::new("authority-test"),
            "authority-obligation",
        );
        assert_eq!(
            manifest.to_json_value()["problem"]["normalized_input_sha256"],
            expected_hash
        );
    }

    #[test]
    fn metadata_upgrade_retains_the_exact_problem_authority() {
        let problem = parse_problem("(< x 0)");
        let result = VerifiedChcResult::from_validated(
            ChcEngineResult::Unknown,
            ValidationEvidence::FullVerification,
        );
        let run = ChcPdrProofRun::new(problem, result, "authority-test");

        let upgraded = run.with_metadata(run.metadata().clone());

        assert!(std::ptr::eq(run.problem(), upgraded.problem()));
        assert_eq!(
            std::mem::discriminant(run.result()),
            std::mem::discriminant(upgraded.result())
        );
    }

    #[test]
    fn concurrent_run_clones_iteratively_drop_the_last_problem_owner() {
        const DEPTH: usize = 10_000;
        const THREADS: usize = 8;
        const STACK_BYTES: usize = 128 * 1024;
        let run = ChcPdrProofRun::new(
            deep_drop_problem(DEPTH),
            VerifiedChcResult::from_validated(
                ChcEngineResult::Unknown,
                ValidationEvidence::FullVerification,
            ),
            "drop-test",
        );
        let barrier = std::sync::Arc::new(std::sync::Barrier::new(THREADS));
        let handles = (0..THREADS)
            .map(|index| {
                let run = run.clone();
                let barrier = barrier.clone();
                std::thread::Builder::new()
                    .name(format!("proof-run-drop-{index}"))
                    .stack_size(STACK_BYTES)
                    .spawn(move || {
                        barrier.wait();
                        drop(run);
                    })
            })
            .collect::<Result<Vec<_>, _>>()
            .expect("small-stack drop threads should spawn");
        drop(run);
        for handle in handles {
            handle
                .join()
                .expect("concurrent proof-run drop should not overflow");
        }
    }

    #[test]
    fn artifact_bundle_rejects_cross_run_substitution() {
        let first = ChcPdrProofRun::new(
            parse_problem("(< x 0)"),
            VerifiedChcResult::from_validated(
                ChcEngineResult::Unknown,
                ValidationEvidence::FullVerification,
            ),
            "authority-test",
        );
        let second = ChcPdrProofRun::new(
            parse_problem("(<= x 0)"),
            VerifiedChcResult::from_validated(
                ChcEngineResult::Unknown,
                ValidationEvidence::FullVerification,
            ),
            "authority-test",
        );
        let first_artifacts = first.proof_run_artifacts();
        let second_artifacts = second.proof_run_artifacts();

        let model_error = first
            .validate_model_replay_artifact_bytes(
                Some(second_artifacts.model_bytes()),
                Some(first_artifacts.replay_transcript_bytes()),
            )
            .expect_err("a model artifact from another run must be rejected");
        assert_eq!(
            model_error.reason,
            ChcProofRunArtifactBundleValidationErrorReason::ModelArtifactMismatch
        );

        let replay_error = first
            .validate_model_replay_artifact_bytes(
                Some(first_artifacts.model_bytes()),
                Some(second_artifacts.replay_transcript_bytes()),
            )
            .expect_err("a replay artifact from another run must be rejected");
        assert_eq!(
            replay_error.reason,
            ChcProofRunArtifactBundleValidationErrorReason::ReplayTranscriptArtifactMismatch
        );
    }

    #[test]
    fn adaptive_portfolio_exposes_atomic_proof_run_api() {
        let _: fn(&crate::AdaptivePortfolio) -> ChcPdrProofRun =
            crate::AdaptivePortfolio::solve_proof_run;

        let portfolio = crate::AdaptivePortfolio::new(
            parse_problem("(< x 0)"),
            crate::AdaptiveConfig::test_default(),
        );
        let run = portfolio.solve_proof_run();
        assert_eq!(run.metadata().engine(), "portfolio");
        assert_eq!(run.consumer_evidence().backend_code(), "ay_chc_portfolio");
    }

    #[test]
    fn atomic_budget_report_is_bound_to_the_same_proof_run() {
        let portfolio = crate::AdaptivePortfolio::new(
            parse_problem("(< x 0)"),
            crate::AdaptiveConfig::test_default(),
        );
        let solved_hash = portfolio.problem().normalized_input_sha256();
        let report = portfolio.solve_proof_run_with_budget_report();

        assert_eq!(
            report.proof_run().problem().normalized_input_sha256(),
            solved_hash
        );
        assert_eq!(report.proof_run().metadata().engine(), "portfolio");
        assert_eq!(report.stop_reason(), ChcProofRunStopReason::Definitive);
        assert!(!report.cancellation_requested_at_return());
        assert_eq!(
            report
                .adaptive_trace()
                .observations()
                .last()
                .map(|observation| observation.stage),
            Some("authoritative_solve")
        );
    }

    #[test]
    fn atomic_budget_report_distinguishes_stop_reasons() {
        let parent = crate::CancellationToken::new();
        parent.cancel();
        let cancelled = crate::AdaptivePortfolio::new(
            parse_problem("(< x 0)"),
            crate::AdaptiveConfig::test_default()
                .with_execution_mode(crate::AdaptiveExecutionMode::DeterministicSequential),
        )
        .with_cancellation_parent(&parent)
        .solve_proof_run_with_budget_report();
        assert!(matches!(
            cancelled.proof_run().result(),
            VerifiedChcResult::Unknown(_)
        ));
        assert_eq!(
            cancelled.stop_reason(),
            ChcProofRunStopReason::ExternallyCancelled
        );
        assert!(cancelled.cancellation_requested_at_return());

        let exhausted = crate::AdaptivePortfolio::new(
            parse_problem("(< x 0)"),
            crate::AdaptiveConfig::test_default()
                .with_time_budget(Duration::from_nanos(1))
                .with_execution_mode(crate::AdaptiveExecutionMode::DeterministicSequential),
        )
        .solve_proof_run_with_budget_report();
        assert!(matches!(
            exhausted.proof_run().result(),
            VerifiedChcResult::Unknown(_)
        ));
        assert_eq!(
            exhausted.stop_reason(),
            ChcProofRunStopReason::BudgetExhausted
        );
        assert!(!exhausted.cancellation_requested_at_return());

        let inconclusive = crate::AdaptivePortfolio::new(
            parse_problem("(< x 0)"),
            crate::AdaptiveConfig::test_default()
                .with_max_engines(Some(0))
                .with_execution_mode(crate::AdaptiveExecutionMode::DeterministicSequential),
        )
        .solve_proof_run_with_budget_report();
        assert!(matches!(
            inconclusive.proof_run().result(),
            VerifiedChcResult::Unknown(_)
        ));
        assert_eq!(
            inconclusive.stop_reason(),
            ChcProofRunStopReason::Inconclusive
        );
        assert!(!inconclusive.cancellation_requested_at_return());
    }
}
