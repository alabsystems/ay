// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Constrained Horn Clause (CHC) solver built on PDR/IC3.
//!
//! Solves CHC systems with a portfolio of model-checking engines (bounded
//! model checking, PDR/IC3, CEGAR, and related strategies) layered on the
//! `ay-sat` and `ay-dpll` solving stack. Alongside sat/unsat verdicts the
//! crate produces proof artifacts and certificates so results can be checked
//! independently.

// Clippy 1.93.0 fires large_stack_arrays with a lost span (lib.rs:1:1) on
// monomorphised code visible only in test builds.  Fixed on nightly; suppress
// until stable catches up.
#![cfg_attr(test, allow(clippy::large_stack_arrays))]
// Missing-docs debt (#8838 follow-up): ay-chc is the only primary library crate without
// `#![warn(missing_docs)]` (ay, ay-core, and ay-sat all enforce it). Enabling
// it today would emit 40+ warnings across the effectively-public surface
// (e.g. the `ChcExpr` constructor methods in expr/methods/constructors.rs,
// pdr/model, quotient_certificate, plus undocumented public fields/variants),
// and the workspace must stay warning-clean. Document those items module by
// module, then uncomment:
// #![warn(missing_docs)]
// Crate-wide allow list (#8838 pre-req).
//
// Historical state: prior to #8838 this crate had a much larger crate-wide
// allow list covering dead_code, unused_variables, private_interfaces, etc.
// That list masked unknown amounts of dead code and blocked later cleanup
// work.
//
// Current state: the allow list has been pruned to the categories below.
// `unused_qualifications`, `deprecated`, and the clippy style lints are
// retained for practical reasons (see per-category notes). `dead_code`,
// `unused_variables`, and `private_interfaces` — the items actually masking
// unknown dead code — are NO LONGER allowed crate-wide. Per-module targeted
// allows surface the remaining inventory rather than a silent crate blanket.
//
// Follow-up: per-module dead-code cleanup is tracked in a separate issue filed
// as part of #8838 completion. Each targeted `#[allow(dead_code)]` below
// corresponds to a module audited and intentionally retained pending the
// next cleanup slice.
#![allow(
    // ~120 `unnecessary_qualification` warnings remain across the crate
    // (mostly `std::` / `crate::` prefixes in macro-generated sites).
    // Non-load-bearing; retained to keep the commit scoped.
    unused_qualifications,
    // 17 sites call the deprecated `api::terms::boolean::not()` method that
    // was renamed to `try_not()`. Mechanical rename deferred to follow-up.
    deprecated,
    // Style lints retained from the historical allow list. These are cosmetic
    // and do not mask bugs. Removing them is out of scope for #8838 pre-req.
    clippy::redundant_closure,
    clippy::redundant_closure_for_method_calls,
    clippy::redundant_clone,
    clippy::needless_lifetimes,
    clippy::elidable_lifetime_names,
    clippy::needless_return,
    clippy::suboptimal_flops,
    clippy::option_option,
    clippy::let_and_return,
    clippy::match_like_matches_macro,
    clippy::cast_lossless,
    clippy::question_mark,
    clippy::vec_init_then_push,
    clippy::filter_map_bool_then,
    clippy::unnecessary_lazy_evaluations,
    clippy::manual_contains,
    clippy::uninlined_format_args
)]

//! This crate implements an 11-engine adaptive portfolio for solving Constrained
//! Horn Clause (CHC) problems, used in program verification to find inductive
//! invariants or counterexamples. Engines: PDR/IC3 (primary), BMC, k-induction,
//! PDKind, TPA, TRL, Decomposition, LAWI, IMC, DAR, CEGAR.
//!
//! # Example
//!
//! ```rust,no_run
//! use ay_chc::{
//!     AdaptiveConfig, AdaptivePortfolio, ChcExpr, ChcProblem, ChcSort, ChcVar,
//!     ClauseBody, ClauseHead, HornClause,
//! };
//!
//! let mut problem = ChcProblem::new();
//! let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
//!
//! let x = ChcVar::new("x", ChcSort::Int);
//! problem.add_clause(HornClause::new(
//!     ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
//!     ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
//! ));
//!
//! problem.add_clause(HornClause::new(
//!     ClauseBody::new(
//!         vec![(inv, vec![ChcExpr::var(x.clone())])],
//!         Some(ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0))),
//!     ),
//!     ClauseHead::False,
//! ));
//!
//! let solver = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
//! let result = solver.solve();
//! assert!(result.is_safe());
//! ```
//!
//! # Example CHC Problem
//!
//! ```text
//! ; Find invariant Inv(x) such that:
//! ; 1. x = 0 => Inv(x)              (initial state)
//! ; 2. Inv(x) /\ x < 10 => Inv(x+1) (transition)
//! ; 3. Inv(x) /\ x >= 10 => false   (safety - should be unsat)
//! ```
//!
//! # Architecture
//!
//! - `Predicate`: Uninterpreted relation to synthesize interpretation for
//! - `HornClause`: Rule of form `body => head`
//! - `ChcProblem`: Collection of Horn clauses with a query
//! - `PdrSolver`: PDR algorithm implementation
//! - `PortfolioSolver`: Runs multiple engines (PDR/BMC/Kind/PDKind/TPA/TRL/Decomposition/LAWI/IMC/DAR/CEGAR)
//! - `BmcSolver`: Bounded model checking engine
//! - `PdkindSolver`: K-induction style engine
//! - `TpaSolver`: Transition Power Abstraction engine
//! - `TrlSolver`: Transitive relation learning engine

// Import safe_eprintln! from ay-core (non-panicking eprintln replacement)
#[macro_use]
extern crate ay_core;

// CHC debug channels (#8832): route through the unified CLI-aware
// `debug_channel_active()` resolver so `--debug prop,chc-smt,algebraic` on the
// command line actually enable these gates. The previous `cached_env_flag!`
// usage only consulted `AY_DEBUG_*` env vars, silently ignoring the CLI flags
// which populate `GLOBAL_DEBUG_CONFIG`. Env var fallback is preserved inside
// `debug_channel_active()` for library consumers (`bench_dimacs`, unit tests)
// that bypass the CLI.
#[inline]
pub(crate) fn debug_prop_enabled() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::Prop)
}
#[inline]
pub(crate) fn debug_chc_smt_enabled() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::ChcSmt)
}
#[inline]
pub(crate) fn debug_algebraic_enabled() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::Algebraic)
}

pub mod ab_switches;
pub(crate) mod acyclic_cert_cache;
mod adaptive;
mod adaptive_bv_dual_lane;
mod adaptive_bv_strategy;
mod adaptive_cata;
mod adaptive_decision_log;
mod adaptive_engines;
mod adaptive_houdini;
mod adaptive_multi_pred;
mod adaptive_multi_pred_complex;
mod adaptive_prestage_budget;
mod adaptive_validation;
mod adt_array_nullary;
pub(crate) mod algebraic_invariant;
mod blackboard;
mod bmc;
pub(crate) mod bv_util;
mod cancellation;
pub(crate) mod cegar;
// Prototype graph IR retained for the multi-edge merger pipeline, but not yet
// routed through the default solver portfolio.
#[allow(dead_code)]
pub(crate) mod chc_graph;
mod chc_statistics;
mod classifier;
mod clause;
mod convex_closure;
pub(crate) mod cvp;
mod dar;
pub(crate) mod decomposition;
mod engine_config;
pub(crate) mod engine_result;
mod engine_utils;
mod error;
pub(crate) mod expr;
mod expr_vars;
pub(crate) mod failure_analysis;
mod farkas;
mod farkas_decomposition;
mod generalize;
pub(crate) mod ground_derivation;
mod ic3;
/// Additive bit-level IC3 portfolio lane for single-predicate Boolean loop CHCs
/// (#8211 wiring). Candidate-only — results are re-validated by the trusted
/// word-level validator. See [`ic3_lane`].
pub mod ic3_lane;
mod imc;
mod interpolant_command;
mod interpolant_validation;
mod interpolation;
mod iuc_solver;
mod k_to_1_inductive;
mod kind;
mod lawi;
pub(crate) mod lemma_cache;
mod lemma_hints;
pub(crate) mod lemma_pool;
mod mbp;
mod parser;
mod pdkind;
mod pdr;
mod portfolio;
mod predicate;
mod problem;
pub mod progress;
mod proof_interpolation;
mod proof_metadata;
mod qf_invariant_artifact;
mod qual_mine;
mod qualifier;
pub mod quotient_certificate;
pub(crate) mod recurrence;
pub(crate) mod single_loop;
mod smt;
mod synthesis;
mod tarjan;
pub(crate) mod term_bridge;
pub(crate) mod tpa;
pub(crate) mod trace;
pub(crate) mod transform;
pub(crate) mod transition_system;
pub(crate) mod trl;
pub(crate) mod trp;

// Core data model — used in public API signatures (ChcParser::parse -> ChcProblem, etc.)
pub use clause::HornClause;
pub use expr::{ChcDtConstructor, ChcDtSelector, ChcExpr, ChcSort, ChcVar};
// (get-interpolant / compute-interpolant) Craig interpolation command support.
pub use interpolant_command::{compute_smt_interpolant, InterpolantError, SortResolver};
pub use predicate::Predicate;
pub use problem::ChcProblem;

// Core types used by integration tests for problem construction
pub use clause::{ActionId, ClauseBody, ClauseHead};
pub use expr::ChcOp;
pub use predicate::PredicateId;
pub use proof_metadata::{
    bmc_unsafe_trace_assignment_completeness, bmc_unsafe_trace_assignment_contract,
    normalized_chc_input, normalized_chc_input_sha256, ChcBmcUnsafeTraceAssignmentCompleteness,
    ChcBmcUnsafeTraceAssignmentCompletenessReason, ChcBmcUnsafeTraceAssignmentCompletenessStatus,
    ChcBmcUnsafeTraceAssignmentContract, ChcCheckedReplayArtifacts,
    ChcCheckedReplayManifestBinding, ChcCheckedReplayObligation, ChcCheckedReplayRun,
    ChcCheckedReplaySummary, ChcCheckedReplaySummaryError, ChcPdrProofRun, ChcProofArtifactDigest,
    ChcProofEvidenceManifest, ChcProofEvidenceOptions, ChcProofEvidenceParseError,
    ChcProofQueryAdmissionKey, ChcProofQueryCache, ChcProofQueryCacheAdmissionDecision,
    ChcProofQueryCacheAdmissionPolicy, ChcProofQueryCacheAdmissionStatus,
    ChcProofQueryCacheLookupKey, ChcProofQueryCacheLookupResult, ChcProofQueryCacheLookupStatus,
    ChcProofQueryCacheMetrics, ChcProofRunArtifact, ChcProofRunArtifactBundleValidationError,
    ChcProofRunArtifactBundleValidationErrorReason, ChcProofRunArtifactValidationError,
    ChcProofRunArtifactValidationErrorReason, ChcProofRunArtifacts, ChcProofSolverIdentity,
    ChcProofTranscriptConsumerEvidence, ChcProofTranscriptMetadata, ChcReplayCheckResult,
    ChcReplayCheckerIdentity, ChcReplayEvidence, ChcReplayObligationArtifact,
    ChcTraceAssignmentEvidence, ChcTraceStepEvidence, ChcUnsafeTraceEvidence,
    CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_COMPLETENESS_SCHEMA,
    CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_CONTRACT_SCHEMA, CHC_CHECKED_REPLAY_MANIFEST_BINDING_SCHEMA,
    CHC_CHECKED_REPLAY_SUMMARY_SCHEMA, CHC_EVIDENCE_MANIFEST_SCHEMA,
    CHC_IN_PROCESS_REPLAY_CHECKER_NAME, CHC_PROOF_ARTIFACT_DIGEST_SCHEMA,
    CHC_PROOF_QUERY_ADMISSION_KEY_SCHEMA, CHC_PROOF_QUERY_CACHE_ADMISSION_DECISION_SCHEMA,
    CHC_PROOF_QUERY_CACHE_ADMISSION_POLICY_SCHEMA, CHC_PROOF_QUERY_CACHE_LOOKUP_KEY_SCHEMA,
    CHC_PROOF_QUERY_CACHE_LOOKUP_RESULT_SCHEMA, CHC_PROOF_QUERY_CACHE_METRICS_SCHEMA,
    CHC_PROOF_QUERY_CACHE_SCHEMA, CHC_PROOF_RUN_MODEL_ARTIFACT_ROLE,
    CHC_PROOF_RUN_MODEL_ARTIFACT_SCHEMA, CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_ROLE,
    CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_SCHEMA, CHC_PROOF_TRANSCRIPT_CONSUMER_EVIDENCE_SCHEMA,
    CHC_PROOF_TRANSCRIPT_SCHEMA, CHC_REPLAY_EVIDENCE_SCHEMA, NORMALIZED_CHC_INPUT_SCHEMA,
};
pub use qf_invariant_artifact::{
    parse_qf_invariant_model_artifact, ChcQfInvariantModelArtifactError,
    ChcQfInvariantModelArtifactErrorReason, CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_BYTES,
    CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_MODEL_BYTES,
    CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_NESTING_DEPTH,
    CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_PARAMETERS, CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_PREDICATES,
    CHC_QF_INVARIANT_MODEL_ARTIFACT_MODEL_FORMAT, CHC_QF_INVARIANT_MODEL_ARTIFACT_ROLE,
    CHC_QF_INVARIANT_MODEL_ARTIFACT_SCHEMA,
};

// Public engine API — consumed by ay binary, fuzz targets, examples, integration tests
pub use adaptive::{AdaptiveConfig, AdaptivePortfolio};
pub use bmc::{BmcConfig, BmcSolver};
pub use cancellation::{CancellationGuard, CancellationToken};
pub use chc_statistics::ChcStatistics;
pub use engine_result::{
    ChcEngineResult, VerifiedChcResult, VerifiedCounterexample, VerifiedInvariant,
    VerifiedUnknownMarker, VerifiedUnknownReason,
};
pub use kind::{KindConfig, KindResult, KindSolver};
pub use lemma_hints::{
    canonical_var_for_pred_arg, canonical_var_name, canonical_vars_for_pred, HintProviders,
    HintRequest, HintStage, LemmaHint, LemmaHintProvider,
};
pub use mbp::Mbp;
pub use parser::ChcParser;
pub use pdkind::{IncrementalMode, PdkindConfig, PdkindResult, PdkindSolver};
pub use pdr::{CexVerificationResult, PredicateInterpretation};
pub use pdr::{
    ChcReplayObligation, ChcReplayObligationKind, Counterexample, CounterexampleStep,
    InvariantModel,
};
pub use pdr::{PdrConfig, PdrResult, PdrSolver};
pub use portfolio::{
    BudgetPolicy, BudgetReport, EngineBudgetEntry, EngineConfig, EngineStopReason, EngineType,
    PortfolioConfig, PortfolioResult, PortfolioSolver,
};
pub use progress::{ChcProgressReport, ChcProgressSnapshot};
pub use smt::{InterpolationResult, SmtContext, SmtResult, SmtValue, UnsatCoreDiagnostics};

/// Stable public API for constructing individual CHC engines.
///
/// For most use cases, [`AdaptivePortfolio`] is recommended — it runs multiple
/// engines and verifies results automatically. Use the functions in this module
/// when you need direct control over a specific engine (e.g., PDR-only solving
/// or custom portfolio configurations).
///
/// # Examples
///
/// ```rust,no_run
/// use ay_chc::{engines, ChcProblem, PdrConfig, PortfolioConfig};
///
/// let problem = ChcProblem::new();
///
/// // Direct PDR solving
/// let mut solver = engines::new_pdr_solver(problem.clone(), PdrConfig::default());
///
/// // Custom portfolio
/// let solver = engines::new_portfolio_solver(problem, PortfolioConfig::default());
/// ```
pub mod engines {
    use super::*;
    use crate::classifier::ProblemClassifier;
    use crate::engine_config::ChcEngineConfig;
    use crate::engine_result::ValidationEvidence;
    use std::panic::AssertUnwindSafe;
    use std::time::Duration;

    const BMC_PROOF_ENGINE_NAME: &str = "bmc";
    const PDR_PROOF_ENGINE_NAME: &str = "pdr";
    const PDR_PROOF_VALIDATION_TIMEOUT: Duration = Duration::from_secs(30);
    const PDR_PROOF_PER_RULE_BUDGET: Duration = Duration::from_secs(2);

    /// Construct a [`PdrSolver`] with the given configuration.
    ///
    /// PDR (Property-Directed Reachability) is the primary invariant discovery
    /// engine. Use this when you need direct access to PDR results, model
    /// verification, or counterexample analysis.
    pub fn new_pdr_solver(problem: ChcProblem, config: PdrConfig) -> PdrSolver {
        PdrSolver::new(problem, config)
    }

    /// Construct a [`PortfolioSolver`] with the given configuration.
    ///
    /// The portfolio solver runs multiple engines (PDR, BMC, PDKIND, TPA, etc.)
    /// and returns the first result. Use this when you want multi-engine coverage
    /// with explicit control over which engines to enable.
    pub fn new_portfolio_solver(problem: ChcProblem, config: PortfolioConfig) -> PortfolioSolver {
        PortfolioSolver::new(problem, config)
    }

    /// Run PDR/IC3 as a proof-grade CHC solver and return verified evidence.
    ///
    /// This is the library entrypoint for consumers such as model-checker-consumer/VerifierConsumer that
    /// need unbounded CHC/PDR proof evidence rather than bounded BMC evidence.
    /// It runs a single PDR solver, forces strict proof validation, re-checks
    /// any Safe/Unsafe result in a fresh verifier, and returns deterministic
    /// proof/transcript metadata bound to the normalized CHC input hash.
    ///
    /// Fail-closed behavior:
    /// - parse/IO/internal ay panics are returned as [`ChcError`];
    /// - inconclusive PDR search, cancellation, or failed re-validation becomes
    ///   `VerifiedChcResult::Unknown`;
    /// - `Unknown` metadata is always `accepted_as_proof == false`.
    pub fn solve_pdr_proof(problem: ChcProblem, config: PdrConfig) -> ChcResult<ChcPdrProofRun> {
        // Install a thread-wide solve deadline so EVERY check_sat on this thread
        // (main PDR context, startup discovery, the fresh re-validation verifier,
        // and any portfolio engine) is bounded by solve_timeout — closing the gap
        // where a fresh context never received a per-context deadline and a query
        // handed `timeout = None` could spin past the deadline (the integer-modulo
        // hang). Restored on drop.
        let _solve_deadline = crate::smt::ScopedSolveDeadline::new(
            config
                .solve_timeout
                .map(|timeout| ay_core::time::Instant::now() + timeout),
        );
        ay_core::catch_ay_panics(
            AssertUnwindSafe(|| Ok(solve_pdr_proof_unchecked(problem, config))),
            |reason| Err(ChcError::Internal(reason)),
        )
    }

    /// Run proof-grade PDR/IC3 and then attempt a budget-capped CHECKED replay
    /// pass on any Safe/Unsafe result (wishlist: model-checker-consumer native-proof
    /// admission).
    ///
    /// On replay success the returned run carries `replayable` transcript
    /// metadata with transcript/replay/checked-report SHA-256 digests and
    /// `trust_full_verifier_admissible() == true`. On ANY replay failure —
    /// budget exhaustion, an obligation not discharging, an internal panic —
    /// the run is returned exactly as [`solve_pdr_proof`] would have returned
    /// it (metadata-only, non-admissible), so opting in can never change a
    /// solve verdict or over-claim replayability.
    pub fn solve_pdr_proof_with_checked_replay(
        problem: ChcProblem,
        config: PdrConfig,
        replay_budget: Duration,
    ) -> ChcResult<ChcPdrProofRun> {
        let run = solve_pdr_proof(problem, config)?;
        Ok(attach_checked_replay(run, replay_budget))
    }

    /// Fail-closed helper: swap in checked-replay metadata when the pass
    /// succeeds, otherwise return the metadata-only run unchanged.
    fn attach_checked_replay(run: ChcPdrProofRun, replay_budget: Duration) -> ChcPdrProofRun {
        if !run.accepted_as_proof() {
            return run;
        }
        let checked = ay_core::catch_ay_panics(
            AssertUnwindSafe(|| run.run_checked_replay(replay_budget)),
            |reason| Err(ChcError::Internal(reason)),
        );
        match checked {
            Ok(checked) => checked.into_proof_run(),
            Err(_) => run,
        }
    }

    /// Parse a CHC problem from SMT-LIB and run proof-grade PDR/IC3.
    ///
    /// Unlike diagnostic/cross-check helpers, parse failures are not converted
    /// to proof-shaped results. Callers must treat `Err` as a release blocker
    /// if this API is on a required full-verification path.
    pub fn solve_pdr_proof_from_str(input: &str, config: PdrConfig) -> ChcResult<ChcPdrProofRun> {
        ay_core::catch_ay_panics(
            AssertUnwindSafe(|| {
                let problem = ChcParser::parse(input)?;
                Ok(solve_pdr_proof_unchecked(problem, config))
            }),
            |reason| Err(ChcError::Internal(reason)),
        )
    }

    /// Read a CHC SMT-LIB file and run proof-grade PDR/IC3.
    pub fn solve_pdr_proof_from_file(
        path: impl AsRef<std::path::Path>,
        config: PdrConfig,
    ) -> ChcResult<ChcPdrProofRun> {
        ay_core::catch_ay_panics(
            AssertUnwindSafe(|| {
                let input = std::fs::read_to_string(path)?;
                let problem = ChcParser::parse(&input)?;
                Ok(solve_pdr_proof_unchecked(problem, config))
            }),
            |reason| Err(ChcError::Internal(reason)),
        )
    }

    fn solve_pdr_proof_unchecked(problem: ChcProblem, mut config: PdrConfig) -> ChcPdrProofRun {
        config.strict_proofs = true;
        // Proof-grade solving must construct an invariant for the exact
        // caller-supplied clauses. The ordinary solve-time nullary-fail
        // expansion is equisatisfiable, but it erases predicates such as
        // `error` from the model surface and has no model backtranslation.
        // Keeping the original clauses here also makes the solving,
        // validation, and checked-replay boundaries agree.
        config.preserve_original_clauses = true;

        // Exact acyclic BMC certificate prepass.
        //
        // Scalar/acyclic/BV multi-predicate problems are decided *completely* by
        // exact acyclic path expansion: every error-reachability branch is
        // checked UNSAT in the original theory (see
        // `bmc::BmcSolver::solve_acyclic_safe_first_once`, which trusts only
        // UNSAT as a safety proof). Pure PDR/IC3 can return Inconclusive on
        // these problems even though they are trivially safe, so try the exact
        // certificate first. Only a `Safe` certificate is accepted as proof;
        // any other outcome falls through to the PDR search below.
        if let Some((true, depth)) = run_scalar_acyclic_bmc_certificate(&problem, &config) {
            let result = VerifiedChcResult::from_validated(
                ChcEngineResult::Safe(InvariantModel::default()),
                ValidationEvidence::ScalarAcyclicBmcExhaustive { max_depth: depth },
            );
            return ChcPdrProofRun::new(problem, result, PDR_PROOF_ENGINE_NAME);
        }

        let raw = PdrSolver::solve_problem(&problem, config.clone());
        let result = validate_pdr_proof_result(&problem, raw, &config);
        ChcPdrProofRun::new(problem, result, PDR_PROOF_ENGINE_NAME)
    }

    fn validation_config(base: &PdrConfig) -> PdrConfig {
        PdrConfig {
            verbose: base.verbose,
            strict_proofs: true,
            cancellation_token: base.cancellation_token.clone(),
            solve_timeout: Some(PDR_PROOF_VALIDATION_TIMEOUT),
            disable_array_scalarization: true,
            // Proof validation is a consumer of the candidate model for the
            // exact caller-supplied problem. Re-running solve-time nullary-fail
            // expansion here can erase `fail => false` and validate a model
            // that interprets the erased nullary query predicate as `true`.
            preserve_original_clauses: true,
            ..PdrConfig::default()
        }
    }

    fn external_model_validation_config(base: &PdrConfig) -> PdrConfig {
        PdrConfig {
            verbose: base.verbose,
            strict_proofs: true,
            cancellation_token: base.cancellation_token.clone(),
            solve_timeout: base.solve_timeout.or(Some(PDR_PROOF_VALIDATION_TIMEOUT)),
            disable_array_scalarization: true,
            // External models are bound to the original predicate signatures
            // and clauses. In particular, do not erase nullary fail/query
            // predicates before checking their interpretations.
            preserve_original_clauses: true,
            ..PdrConfig::default()
        }
    }

    /// Validate a caller-provided invariant model against a CHC problem.
    ///
    /// This is the consumer-facing verification path for models that were
    /// produced outside the fresh verifier or back-translated to the original
    /// predicate signatures. Unlike [`new_pdr_solver`], the verifier preserves
    /// Array-sorted predicate arguments and does not run PDR's solving-time
    /// array scalarization pass. That matters when `model` is expressed over
    /// the original CHC relation signatures.
    ///
    /// Returns `Ok(true)` only when full PDR clause verification succeeds, or
    /// when the caller-provided empty model is independently validated as a
    /// scalar acyclic exhaustive BMC certificate.
    /// Panics from the internal verifier are converted to [`ChcError::Internal`].
    pub fn validate_external_invariant_model(
        problem: &ChcProblem,
        model: &InvariantModel,
        config: &PdrConfig,
    ) -> ChcResult<bool> {
        ay_core::catch_ay_panics(
            AssertUnwindSafe(|| {
                let validation_config = external_model_validation_config(config);
                // FORALL-ARR ghost-pair certificates (agenda #16): the model's
                // quantifier-free interpretations are intentionally empty; the
                // sealed certificate denotes the quantified invariant. Validate
                // by re-running the full per-rule quantified discharge on the
                // ORIGINAL clauses (fail-closed on any undischarged clause).
                if let Some(certificate) = model.ghost_pair_certificate() {
                    return Ok(crate::transform::recheck_ghost_pair_certificate(
                        problem,
                        certificate,
                        validation_config.solve_timeout,
                        false,
                    ));
                }
                if model.is_empty() {
                    if let Some(result) =
                        validate_empty_scalar_acyclic_bmc_certificate(problem, &validation_config)
                    {
                        return result;
                    }
                }

                let validation_budget = validation_config.solve_timeout;
                let mut verifier = PdrSolver::new(problem.clone(), validation_config);
                match validation_budget {
                    Some(budget) if budget.is_zero() => Ok(false),
                    Some(budget) => {
                        verifier.set_validation_deadline(budget);
                        Ok(verifier.verify_model_with_budget(model, budget))
                    }
                    None => verifier.try_verify_model(model),
                }
            }),
            |reason| Err(ChcError::Internal(reason)),
        )
    }

    /// Re-validate an externally-produced candidate invariant `model` and, on
    /// success, emit an ACCEPTED proof-grade run.
    ///
    /// This is the public proof-emission entry that lets an out-of-crate driver
    /// (e.g. model-checker-consumer's IC3 loop lane) turn a *candidate* invariant — one
    /// back-translated by [`crate::ic3_lane::try_prove_chc_loop`] and therefore
    /// explicitly NOT trusted (see that module's contract) — into accepted
    /// [`ChcPdrProofRun`] evidence WITHOUT crossing the soundness boundary. The
    /// only way to reach the accepting `Safe` wrap below is through the full
    /// re-validation performed here; `VerifiedChcResult::from_validated` and the
    /// `ValidationEvidence` it demands are `pub(crate)`, so this emission point
    /// must live inside `ay-chc`.
    ///
    /// Fail-closed (belt-and-suspenders):
    /// - `model` is FIRST re-validated with
    ///   [`validate_external_invariant_model`], which runs the FULL init +
    ///   transition + query clause check in a fresh verifier (array
    ///   scalarization disabled so the model is checked against the *original*
    ///   predicate signatures). An internal verifier panic surfaces as `Err`.
    /// - If re-validation returns `Ok(false)` (the candidate is rejected) the run
    ///   is emitted as `VerifiedChcResult::Unknown` — `accepted_as_proof()`
    ///   is `false` — so an unvalidated candidate can NEVER yield an accepting
    ///   proof. An `Err` likewise never yields an accepting proof.
    /// - Only on `Ok(true)` is the model wrapped as proof-grade `Safe` with
    ///   [`ValidationEvidence::FullVerification`], which honestly records that the
    ///   full clause check ran (NOT an acyclic/empty-model shortcut, which would
    ///   be unsound for a cyclic loop model).
    pub fn prove_external_invariant_model(
        problem: ChcProblem,
        model: InvariantModel,
        config: PdrConfig,
    ) -> ChcResult<ChcPdrProofRun> {
        // Mandatory re-validation gate. This is the entire soundness story: the
        // candidate is not trusted until the full clause check confirms it.
        // `?` propagates a verifier panic as `Err` (also non-accepting).
        if !validate_external_invariant_model(&problem, &model, &config)? {
            // Candidate rejected — emit a NON-accepted run. Mirrors the Unknown
            // arm of `validate_pdr_proof_result`: the full clause check ran and
            // did not confirm the model, so no proof-grade Safe is emitted.
            let result = VerifiedChcResult::from_validated(
                ChcEngineResult::Unknown,
                ValidationEvidence::FullVerification,
            );
            return Ok(ChcPdrProofRun::new(problem, result, PDR_PROOF_ENGINE_NAME));
        }

        // Re-validated: the full init + transition + query clause check passed
        // in a fresh verifier, so promoting to proof-grade Safe with
        // FullVerification evidence is honest.
        let result = VerifiedChcResult::from_validated(
            ChcEngineResult::Safe(model),
            ValidationEvidence::FullVerification,
        );
        Ok(ChcPdrProofRun::new(problem, result, PDR_PROOF_ENGINE_NAME))
    }

    fn validate_empty_scalar_acyclic_bmc_certificate(
        problem: &ChcProblem,
        config: &PdrConfig,
    ) -> Option<ChcResult<bool>> {
        run_scalar_acyclic_bmc_certificate(problem, config).map(|(is_safe, _depth)| Ok(is_safe))
    }

    /// Soundness gate: does `model` EXCLUDE the error state, i.e. does it satisfy
    /// every query/safety clause (`inv-body => false`)?
    ///
    /// Returns `Ok(true)` only when no safety clause is violated. This is the
    /// minimal, definitive check for a false-SAFE: if the model permits the bad
    /// state, the candidate "SAFE" verdict is provably wrong and must be demoted
    /// to `unknown`. Unlike [`validate_external_invariant_model`] (which re-runs
    /// FULL inductiveness verification and can spuriously fail to re-verify a
    /// genuinely-safe model whose transition checks are merely inconclusive in
    /// this back-translated path), this only checks the safety/query clauses, so
    /// it never demotes a real SAFE while still catching error-permitting models.
    pub fn external_invariant_model_excludes_error(
        problem: &ChcProblem,
        model: &InvariantModel,
        config: &PdrConfig,
    ) -> ChcResult<bool> {
        ay_core::catch_ay_panics(
            AssertUnwindSafe(|| {
                let validation_config = external_model_validation_config(config);
                // FORALL-ARR ghost-pair certificates (agenda #16): discharge
                // the query/safety clauses under the quantified semantics —
                // the quantifier-free `verify_model_query_only` path cannot
                // represent the certificate's `forall` invariant. Fail-closed:
                // only a positive per-query discharge returns true.
                if let Some(certificate) = model.ghost_pair_certificate() {
                    return Ok(crate::transform::recheck_ghost_pair_certificate(
                        problem,
                        certificate,
                        validation_config.solve_timeout,
                        true,
                    ));
                }
                if model.is_empty() {
                    if let Some(result) =
                        validate_empty_scalar_acyclic_bmc_certificate(problem, &validation_config)
                    {
                        return result;
                    }
                }
                let budget = validation_config.solve_timeout;
                let mut verifier = PdrSolver::new(problem.clone(), validation_config);
                if let Some(b) = budget {
                    verifier.set_validation_deadline(b);
                }
                Ok(verifier.verify_model_query_only(model))
            }),
            |reason| Err(ChcError::Internal(reason)),
        )
    }

    /// Replay obligations for a verified-SAFE result, aware of the
    /// acyclic-exhaustive (empty-model) and ghost-pair-certificate proof
    /// classes.
    ///
    /// A Safe carried by a sealed FORALL-ARR ghost-pair certificate (agenda
    /// #16) also has an empty per-predicate map; its replay set is the
    /// certificate's own per-clause quantified discharge queries
    /// (`ghost_pair_replay_obligations`), each of which must be UNSAT — see
    /// the branch below.
    ///
    /// An empty-model Safe from the acyclic BMC lane
    /// (`ValidationEvidence::ScalarAcyclicBmcExhaustive`) is a COMPLETE
    /// bounded-search proof, not an inductive-invariant model — it has no
    /// per-predicate interpretations, so the standard invariant-replay
    /// exporter necessarily fails with "missing invariant interpretation"
    /// on the first multi-predicate clause (task: multi-pred replay
    /// exporter). That hard error previously aborted certificate emission
    /// and demoted genuinely-proved SAFEs to unknown.
    ///
    /// For exactly that shape, the sound validation artifact is the
    /// deterministic exhaustive re-run — the SAME check the discharge gate
    /// (`external_invariant_model_excludes_error`) already applies to
    /// empty models via `validate_empty_scalar_acyclic_bmc_certificate`:
    /// complete for acyclic scalar/finite-ADT DAGs, fail-closed on
    /// SMT-unknowns, arrays/reals/recursive datatypes excluded. When that
    /// re-run confirms Safe, there are no invariant obligations to replay
    /// and this returns an empty set (the certificate stands on the
    /// re-validated exhaustive search). In every other case — non-empty
    /// models, non-eligible problems, or a re-run that does not confirm —
    /// this defers to the standard exporter unchanged, preserving its
    /// fail-closed missing-interpretation error. Nothing is fabricated:
    /// this branch can only ever REMOVE the obligation step for proofs the
    /// validator independently re-establishes.
    pub fn chc_safe_replay_obligations(
        problem: &ChcProblem,
        model: &InvariantModel,
    ) -> ChcResult<Vec<ChcReplayObligation>> {
        // FORALL-ARR ghost-pair certificates (agenda #16): the Safe model is
        // an empty per-predicate map carrying a sealed quantified certificate,
        // so the standard invariant exporter has nothing to instantiate. The
        // sound replay set is the certificate's own per-clause quantified
        // discharge queries (each must be UNSAT), which sealing already
        // discharged in-process.
        if let Some(certificate) = model.ghost_pair_certificate() {
            return crate::transform::ghost_pair_replay_obligations(problem, certificate);
        }
        if model.is_empty() {
            let config = PdrConfig::default().with_strict_proofs(true);
            let validation_config = external_model_validation_config(&config);
            if let Some(Ok(true)) =
                validate_empty_scalar_acyclic_bmc_certificate(problem, &validation_config)
            {
                return Ok(Vec::new());
            }
            // Not eligible or not re-confirmed: fall through so the standard
            // exporter reports the precise fail-closed error.
        }
        model.replay_obligations(problem)
    }

    /// Cata-aware query-only safety gate for COMPOSED catamorphism models
    /// (CHC-COMP agenda #7).
    ///
    /// A model produced by the catamorphism-abstraction lane interprets ADT
    /// predicate arguments through reserved recursive-function symbols
    /// (`cata_<kind>@<sort>`). The generic
    /// [`external_invariant_model_excludes_error`] cannot evaluate those
    /// symbols (they are uninterpreted to it), so it conservatively fails on
    /// every cata model. This gate discharges the SAME per-query-clause
    /// obligations — `interpretations ∧ body-constraint` UNSAT — on a fresh
    /// executor with the catamorphisms' true facts instantiated (defining
    /// recurrences, min facts, one-level unfolding case splits). It answers
    /// `true` ONLY when every query clause discharges `unsat`; every other
    /// outcome is `false` (fail-closed). Because the added facts are all true
    /// of the real catamorphisms, a `true` answer soundly certifies that the
    /// model excludes the error states of the ORIGINAL clauses.
    pub fn cata_composed_model_excludes_error(
        problem: &ChcProblem,
        model: &InvariantModel,
        per_query_budget: std::time::Duration,
        deadline: Option<ay_core::time::Instant>,
    ) -> bool {
        ay_core::catch_ay_panics(
            AssertUnwindSafe(|| {
                Ok(crate::transform::cata_abstract::cata_model_excludes_error(
                    problem,
                    model,
                    per_query_budget,
                    deadline,
                ))
            }),
            |_| Err(()),
        )
        .unwrap_or(false)
    }

    /// Run the exact acyclic BMC certificate for a scalar/acyclic/BV
    /// multi-predicate problem.
    ///
    /// Returns `None` when the problem is not eligible (has predicates, no
    /// arrays, has BV sorts, no cycles, more than one predicate). When
    /// eligible, returns `Some((is_safe, depth))` where `is_safe` is `true`
    /// only if the exact acyclic path expansion discharged every
    /// error-reachability branch as UNSAT in the original theory, and `depth`
    /// is the exhaustive DAG depth used (admissible evidence metadata). A zero
    /// budget yields `Some((false, depth))`.
    fn run_scalar_acyclic_bmc_certificate(
        problem: &ChcProblem,
        config: &PdrConfig,
    ) -> Option<(bool, usize)> {
        // Dead-end-cycle parity (ay#8578): the SOLVE lane
        // (`AdaptivePortfolio::new`) strips provably-dead-end cycle predicates
        // (a self-loop with no path to any query) so an acyclic-modulo-dead-end
        // CHC routes to the fast bounded-BMC lane, and then ships an EMPTY
        // acyclic-BMC certificate for the now-acyclic DAG. The CLI discharges
        // that certificate against `solver.problem()` (already stripped), but an
        // out-of-crate re-validation caller (e.g. model-checker-consumer's native CHC path)
        // hands us the ORIGINAL, un-stripped problem, whose lone dead-end
        // self-loop makes `has_cycles()` true and would spuriously reject the
        // honest empty certificate below — demoting a genuinely-proved Safe to
        // UNKNOWN. Apply the SAME verdict-preserving strip here so validation
        // classifies and re-checks the identical acyclic-modulo-dead-end problem
        // the solve lane proved. `strip_dead_end_cycle_predicates` is a strict
        // no-op (byte-identical) for every problem outside that class, so this
        // only recovers the lost decision and cannot change any other verdict.
        let stripped_owned;
        let problem = if problem.has_cycles() {
            let mut p = problem.clone();
            p.strip_dead_end_cycle_predicates();
            stripped_owned = p;
            &stripped_owned
        } else {
            problem
        };

        // Accept scalar acyclic DAGs over any combination of Bool/Int/BV — NOT just BV.
        // The production path emits these acyclic-BMC Safe certificates for pure Bool/Int
        // scalar DAGs (source_exact_bool_int_dag, adaptive_multi_pred.rs:397), but this
        // validator previously required BV (`!has_bv_sorts()` -> bail), so pure-LIA proofs
        // were emitted then rejected and the genuinely-proved Safe was demoted to unknown.
        // SOUND: this validator re-runs EXHAUSTIVE acyclic BMC below (finalize_bounded_search
        // returns Safe only with no SMT-unknown AND every depth <= dag_depth.max(num_preds)
        // discharged UNSAT in the original theory) — complete for acyclic DAGs over scalar
        // theories AND over FINITE (non-recursive) datatypes. Arrays/reals stay excluded (not
        // complete under bounded unroll). Datatypes: admit NON-recursive ADTs (a struct of
        // bitvectors, `Option<bv64>`, an enum of scalar variants, `CoroutineState`, `Pin<bv64>`)
        // — their value space is finite, so bounded acyclic unrolling is complete for them.
        // RECURSIVE datatypes (unbounded value space) stay excluded: bounded unrolling is not
        // complete for them, so admitting their acyclic-BMC Safe would be a false proof.
        if problem.predicates().is_empty()
            || problem.has_array_sorts()
            || problem.has_real_sorts()
            || problem.has_recursive_datatype_sorts()
        {
            return None;
        }

        let features = ProblemClassifier::classify(problem);
        if features.has_cycles || features.uses_arrays || features.num_predicates <= 1 {
            return None;
        }

        let depth = features.dag_depth.max(features.num_predicates).max(1);
        let budget = config.solve_timeout.or(Some(PDR_PROOF_VALIDATION_TIMEOUT));
        if budget.is_some_and(|budget| budget.is_zero())
            || config
                .cancellation_token
                .as_ref()
                .is_some_and(CancellationToken::is_cancelled)
        {
            return Some((false, depth));
        }

        // Reuse the solve lane's already-computed acyclic-BMC safety proof
        // instead of recomputing the identical exhaustive BMC (the whole point
        // of this optimization; count_zero/loop_with_old: ~8.5 s proved twice →
        // once). This is reached ONLY after the eligibility, zero-budget, and
        // pre-cancellation gates above, so a hit can only ever stand in for the
        // `BmcSolver::solve()` run below — never bypass a gate. The memo records
        // `problem` (the same dead-end-stripped problem classified here) ONLY
        // immediately after complete acyclic BMC genuinely proved it safe.
        // The key is the full structural identity, and the cached bound must
        // cover the freshly recomputed exhaustive depth, so a hit is exactly
        // equivalent to re-running: it yields `Some((true, depth))`, the same
        // Safe verdict the re-run would establish. On any miss (the problem
        // was not proved this session, is not structurally identical, or was
        // proved only to a shallower bound) we fall through to the
        // correct-but-slower re-run. See `crate::acyclic_cert_cache`.
        if crate::acyclic_cert_cache::lookup_acyclic_bmc_safe(problem)
            .is_some_and(|cached_depth| cached_depth >= depth)
        {
            return Some((true, depth));
        }

        let bmc_config = BmcConfig {
            base: ChcEngineConfig {
                verbose: config.verbose,
                cancellation_token: config.cancellation_token.clone(),
            },
            max_depth: depth,
            acyclic_safe: true,
            prefer_exact_acyclic_first: true,
            per_depth_timeout: None,
            time_budget: budget,
            enable_k_induction: false,
            enable_adaptive_stepping: false,
            proof_cross_check: false,
            ts_probe_clamp: None,
            sweep_past_spurious_sat: true,
        };

        let result = BmcSolver::new(problem.clone(), bmc_config.clone()).solve();
        match result {
            PortfolioResult::Safe(_) => Some((true, depth)),
            // A definite Unsafe is a hard reject — never fall back to another engine.
            PortfolioResult::Unsafe(_) => Some((false, depth)),
            // The streaming exact-acyclic engine (prefer_exact_acyclic_first: true) fails
            // CLOSED to Unknown on a single per-branch SMT-unknown (e.g. intro1/intro2's
            // symbolic-LIA query expansion). Retry once with the EXHAUSTIVE engine
            // (prefer_exact_acyclic_first: false -> solve_acyclic_exhaustive_once), the same
            // complete decision procedure the production probe used to PROVE these Safe: it
            // builds the full level encoding as one combined check-sat. SOUND — still only
            // Safe on a full UNSAT unroll, and this arm is never reached on a definite Unsafe.
            PortfolioResult::Unknown | PortfolioResult::NotApplicable => {
                let exhaustive_config = BmcConfig {
                    prefer_exact_acyclic_first: false,
                    ..bmc_config
                };
                let exhaustive = BmcSolver::new(problem.clone(), exhaustive_config).solve();
                Some((matches!(exhaustive, PortfolioResult::Safe(_)), depth))
            }
        }
    }

    fn validate_pdr_proof_result(
        problem: &ChcProblem,
        result: PdrResult,
        base_config: &PdrConfig,
    ) -> VerifiedChcResult {
        match result {
            PdrResult::Safe(model) => {
                let mut verifier = PdrSolver::new(problem.clone(), validation_config(base_config));
                if verifier.verify_model_per_rule(&model, PDR_PROOF_PER_RULE_BUDGET) {
                    VerifiedChcResult::from_validated(
                        ChcEngineResult::Safe(model),
                        ValidationEvidence::FullVerification,
                    )
                } else {
                    VerifiedChcResult::from_validated(
                        ChcEngineResult::Unknown,
                        ValidationEvidence::FullVerification,
                    )
                }
            }
            PdrResult::Unsafe(cex) => {
                let mut verifier = PdrSolver::new(problem.clone(), validation_config(base_config));
                if matches!(
                    verifier.verify_counterexample(&cex),
                    CexVerificationResult::Valid
                ) {
                    VerifiedChcResult::from_validated(
                        ChcEngineResult::Unsafe(cex),
                        ValidationEvidence::CounterexampleVerification,
                    )
                } else {
                    VerifiedChcResult::from_validated(
                        ChcEngineResult::Unknown,
                        ValidationEvidence::CounterexampleVerification,
                    )
                }
            }
            PdrResult::Unknown => VerifiedChcResult::from_validated(
                ChcEngineResult::Unknown,
                ValidationEvidence::FullVerification,
            ),
            PdrResult::NotApplicable => VerifiedChcResult::from_validated(
                ChcEngineResult::NotApplicable,
                ValidationEvidence::FullVerification,
            ),
        }
    }

    /// Run BMC-only on a CHC problem for proof cross-checking.
    ///
    /// Creates an [`AdaptivePortfolio`] and runs only the BMC engine (no PDR,
    /// no k-induction, no TPA). Returns a [`VerifiedChcResult`]:
    ///
    /// - `Unsafe(cex)`: counterexample found within `max_depth` steps.
    /// - `Unknown`: max depth exhausted without counterexample.
    ///   Inspect [`VerifiedChcResult::unknown_reason`] to distinguish
    ///   bounded-search exhaustion from a BMC budget stop.
    /// - `Safe`: only if `acyclic_safe` is set AND max depth exhausted.
    ///
    /// Designed for cross-checking PDR proofs: if BMC finds `Unsafe`, the
    /// proof is likely spurious. Part of #8412.
    ///
    /// # Example
    ///
    /// ```rust,no_run
    /// use ay_chc::{engines, BmcConfig, ChcProblem};
    /// use std::time::Duration;
    ///
    /// let problem = ChcProblem::new();
    /// let result = engines::solve_bmc_only(
    ///     problem,
    ///     BmcConfig::default()
    ///         .with_max_depth(100)
    ///         .with_time_budget(Duration::from_secs(30)),
    /// );
    /// if result.is_unsafe() {
    ///     // PDR proof is contradicted by BMC counterexample
    /// } else if let Some(ay_chc::VerifiedUnknownReason::BmcExhaustedSearch) =
    ///     result.unknown_reason()
    /// {
    ///     // BMC searched the requested bound without finding a contradiction
    /// }
    /// ```
    pub fn solve_bmc_only(problem: ChcProblem, bmc_config: BmcConfig) -> VerifiedChcResult {
        // A body-position `forall` was stripped, which WEAKENS the antecedent
        // (see `ChcProblem::has_stripped_body_forall`). Proofs survive an
        // over-approximation a fortiori, but a counterexample may have been
        // fabricated by the weakened guard, so `Unsafe` must not be published.
        let overapproximated = problem.has_stripped_body_forall();
        let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::default());
        let result = adaptive.solve_bmc_only(bmc_config);
        downgrade_unsafe_if_overapproximated(result, overapproximated)
    }

    /// Map `Unsafe` -> `Unknown` when the problem was over-approximated by
    /// body-`forall` stripping. `Safe` and `Unknown` pass through untouched:
    /// the ONLY legal transition here is `Unsafe -> Unknown`, so this can never
    /// gain or lose a proof.
    fn downgrade_unsafe_if_overapproximated(
        result: VerifiedChcResult,
        overapproximated: bool,
    ) -> VerifiedChcResult {
        match result {
            VerifiedChcResult::Unsafe(_) if overapproximated => {
                VerifiedChcResult::Unknown(crate::engine_result::VerifiedUnknownMarker::new())
            }
            other => other,
        }
    }

    /// Parse a CHC problem from an SMT-LIB string and run BMC-only.
    ///
    /// Convenience wrapper that combines [`ChcParser::parse`] with
    /// [`solve_bmc_only`]. Returns a [`ChcResult`] wrapping the BMC result.
    ///
    /// Designed for consumers like model-checker-consumer that currently shell out to
    /// `z3 fp.engine=bmc <file.smt2>` and want a native Rust replacement.
    /// Part of #8412.
    ///
    /// # Cross-Check Workflow (model-checker-consumer use case)
    ///
    /// After PDR/IC3 claims a CHC problem is Safe, run BMC independently
    /// to search for counterexamples that would contradict the proof:
    ///
    /// ```rust,no_run
    /// use ay_chc::{engines, BmcConfig, CancellationToken};
    ///
    /// fn cross_check_proof(smt2: &str) -> bool {
    ///     let token = CancellationToken::new();
    ///     let config = BmcConfig::cross_check()
    ///         .with_cancellation(token);
    ///     match engines::solve_bmc_only_from_str(smt2, config) {
    ///         Ok(result) => {
    ///             if result.is_unsafe() {
    ///                 false // BMC found counterexample — proof contradicted
    ///             } else {
    ///                 true  // No counterexample found — proof not contradicted
    ///             }
    ///         }
    ///         Err(_) => true, // Parse error — skip cross-check
    ///     }
    /// }
    /// ```
    pub fn solve_bmc_only_from_str(
        input: &str,
        bmc_config: BmcConfig,
    ) -> ChcResult<VerifiedChcResult> {
        let problem = ChcParser::parse(input).map_err(|e| ChcError::Parse(e.to_string()))?;
        Ok(solve_bmc_only(problem, bmc_config))
    }

    /// Run BMC-only and return the typed proof-run wrapper used by evidence consumers.
    ///
    /// This is the BMC counterpart to [`solve_pdr_proof`]. It keeps the
    /// solver-owned validation boundary in AY and gives downstream callers a
    /// [`ChcPdrProofRun`] they can feed directly to
    /// [`ChcPdrProofRun::consumer_evidence`]. In particular, MCC/hardware
    /// consumers should prefer this over solving separately and attempting to
    /// construct proof metadata outside the sealed run.
    pub fn solve_bmc_proof(
        problem: ChcProblem,
        bmc_config: BmcConfig,
    ) -> ChcResult<ChcPdrProofRun> {
        ay_core::catch_ay_panics(
            AssertUnwindSafe(|| Ok(solve_bmc_proof_unchecked(problem, bmc_config))),
            |reason| Err(ChcError::Internal(reason)),
        )
    }

    /// Run BMC-only evidence mode and then attempt a budget-capped CHECKED
    /// replay pass on any Safe/Unsafe result.
    ///
    /// The BMC counterpart to [`solve_pdr_proof_with_checked_replay`]. For
    /// empty-model acyclic-exhaustion SAFE certificates the replay pass
    /// synthesizes one Safety obligation per query clause encoding the
    /// depth-exhaustion UNSAT check. Fail-closed exactly like the PDR variant.
    pub fn solve_bmc_proof_with_checked_replay(
        problem: ChcProblem,
        bmc_config: BmcConfig,
        replay_budget: Duration,
    ) -> ChcResult<ChcPdrProofRun> {
        let run = solve_bmc_proof(problem, bmc_config)?;
        Ok(attach_checked_replay(run, replay_budget))
    }

    /// Parse a CHC problem from an SMT-LIB string and run BMC-only evidence mode.
    pub fn solve_bmc_proof_from_str(
        input: &str,
        bmc_config: BmcConfig,
    ) -> ChcResult<ChcPdrProofRun> {
        let problem = ChcParser::parse(input).map_err(|e| ChcError::Parse(e.to_string()))?;
        solve_bmc_proof(problem, bmc_config)
    }

    fn solve_bmc_proof_unchecked(problem: ChcProblem, bmc_config: BmcConfig) -> ChcPdrProofRun {
        let adaptive = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::default());
        let result = adaptive.solve_bmc_only(bmc_config);
        ChcPdrProofRun::new(problem, result, BMC_PROOF_ENGINE_NAME)
    }
}

/// Test support: factory functions for constructing individual CHC engines.
///
/// This module provides access to all engine constructors for integration tests.
/// For production use, prefer [`engines`] (stable public API) or
/// [`AdaptivePortfolio`] (recommended default).
#[doc(hidden)]
pub mod testing;

// Error types — public so consumers can match on structured errors from try_solve()
pub use error::{ChcError, ChcResult};
pub(crate) use proof_interpolation::{
    compute_interpolant_from_lia_farkas, compute_interpolant_from_smt_farkas_history,
};
pub(crate) use qualifier::QualifierSet;
pub(crate) use smt::{InterpolatingResult, InterpolatingSmtContext};

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
