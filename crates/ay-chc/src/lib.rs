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

/// Largest bit-vector width accepted by the public CHC API and SMT-LIB parser.
///
/// Bit-vector widths directly size bit-blasting state and exact literal/model
/// reconstruction. Keeping one shared bound prevents typed frontends from
/// bypassing the parser's resource limit with a programmatically-built literal.
pub const MAX_BITVECTOR_WIDTH: u32 = 1 << 20;

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
mod adaptive_array_refutation;
mod adaptive_bv_dual_lane;
mod adaptive_bv_strategy;
mod adaptive_cata;
mod adaptive_collapse_first;
mod adaptive_decision_log;
mod adaptive_engines;
mod adaptive_houdini;
mod adaptive_ladder_race;
mod adaptive_multi_pred;
mod adaptive_multi_pred_complex;
mod adaptive_prestage_budget;
mod adaptive_query_flag_race;
mod adaptive_route_admission;
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
mod compact_datatype_route;
mod convex_closure;
pub(crate) mod cvp;
mod dar;
pub(crate) mod decomposition;
mod empty_acyclic_safe_check;
mod engine_config;
pub(crate) mod engine_result;
mod engine_utils;
mod error;
pub(crate) mod expr;
mod expr_vars;
pub(crate) mod failure_analysis;
mod farkas;
mod farkas_decomposition;
pub mod fp_adapter;
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
pub mod quantified;
pub mod quotient_certificate;
pub(crate) mod recurrence;
mod run_meter;
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
pub use expr::{
    ChcDtConstructor, ChcDtConstructors, ChcDtId, ChcDtSelector, ChcExpr, ChcSort, ChcVar,
};
pub use ground_derivation::compact_artifact::{
    validate_chc_compact_ground_derivation_artifact,
    validate_chc_compact_ground_derivation_artifact_with_progress, ChcCompactGroundStepView,
    ChcCompactValueId, ChcCompactValueView, ChcValidatedCompactGroundDerivation,
    CHC_COMPACT_GROUND_DERIVATION_ROLE, CHC_COMPACT_GROUND_DERIVATION_SCHEMA,
};
pub use ground_derivation::{
    validate_chc_ground_derivation_artifact, validate_chc_ground_derivation_artifact_v2,
    validate_chc_ground_derivation_artifact_v2_with_progress,
    validate_chc_ground_derivation_artifact_with_progress, ChcGroundDerivationArtifactError,
    ChcGroundDerivationArtifactErrorReason, ChcGroundDerivationStepView,
    ChcValidatedGroundDerivation, CHC_GROUND_DERIVATION_ARTIFACT_MAX_BINDINGS,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES, CHC_GROUND_DERIVATION_ARTIFACT_MAX_CLAUSES,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_NESTING_DEPTH,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREDICATES,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREMISE_EDGES, CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_UF_OBSERVATIONS,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_VALUE_NODES, CHC_GROUND_DERIVATION_ARTIFACT_ROLE,
    CHC_GROUND_DERIVATION_ARTIFACT_SCHEMA, CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE,
    CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA, CHC_GROUND_DERIVATION_MAX_SOURCE_WORK,
};
// (get-interpolant / compute-interpolant) Craig interpolation command support.
pub use interpolant_command::{compute_smt_interpolant, InterpolantError, SortResolver};
pub use predicate::Predicate;
pub use problem::ChcPrunedQueryObligationId;
pub use problem::{ChcProblem, ChcQueryObligation, ChcQueryObligationId};
pub use problem::{ChcQueryPlayback, ChcQueryPlaybackControl, ChcQueryPlaybackError};
// Core types used by integration tests for problem construction
pub use adaptive_decision_log::{
    AdaptiveSolveReport, AdaptiveSolveTrace, AdaptiveStrategyObservation, AdaptiveStrategyOutcome,
};
pub use clause::{ActionId, ClauseBody, ClauseHead};
pub use expr::ChcOp;
pub use predicate::PredicateId;
pub use proof_metadata::{
    bmc_unsafe_trace_assignment_completeness, bmc_unsafe_trace_assignment_contract,
    normalized_chc_input, normalized_chc_input_schema, normalized_chc_input_schema_of,
    normalized_chc_input_sha256, prepare_normalized_chc_input_with_work,
    ChcBmcUnsafeTraceAssignmentCompleteness, ChcBmcUnsafeTraceAssignmentCompletenessReason,
    ChcBmcUnsafeTraceAssignmentCompletenessStatus, ChcBmcUnsafeTraceAssignmentContract,
    ChcCheckedReplayArtifacts, ChcCheckedReplayManifestBinding, ChcCheckedReplayObligation,
    ChcCheckedReplayObligationPayload, ChcCheckedReplayRun, ChcCheckedReplaySummary,
    ChcCheckedReplaySummaryError, ChcObligationStrictCert, ChcPdrProofRun, ChcProofArtifactDigest,
    ChcProofEvidenceManifest, ChcProofEvidenceOptions, ChcProofEvidenceParseError,
    ChcProofQueryAdmissionKey, ChcProofQueryCache, ChcProofQueryCacheAdmissionDecision,
    ChcProofQueryCacheAdmissionPolicy, ChcProofQueryCacheAdmissionStatus,
    ChcProofQueryCacheLookupKey, ChcProofQueryCacheLookupResult, ChcProofQueryCacheLookupStatus,
    ChcProofQueryCacheMetrics, ChcProofRunArtifact, ChcProofRunArtifactBundleValidationError,
    ChcProofRunArtifactBundleValidationErrorReason, ChcProofRunArtifactValidationError,
    ChcProofRunArtifactValidationErrorReason, ChcProofRunArtifacts, ChcProofRunStopReason,
    ChcProofRunWithBudgetReport, ChcProofSolverIdentity, ChcProofTranscriptConsumerEvidence,
    ChcProofTranscriptMetadata, ChcReplayCheckResult, ChcReplayCheckerIdentity, ChcReplayEvidence,
    ChcReplayObligationArtifact, ChcReplayPayloadFormat, ChcTraceAssignmentEvidence,
    ChcTraceStepEvidence, ChcUnsafeTraceEvidence, PreparedNormalizedChcInput,
    CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_COMPLETENESS_SCHEMA,
    CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_CONTRACT_SCHEMA, CHC_CHECKED_REPLAY_MANIFEST_BINDING_SCHEMA,
    CHC_CHECKED_REPLAY_SUMMARY_SCHEMA, CHC_CHECKED_REPLAY_SUMMARY_SCHEMA_V2,
    CHC_CHECKED_REPLAY_SUMMARY_SCHEMA_V3, CHC_CHECKED_REPLAY_SUMMARY_SCHEMA_V4,
    CHC_EVIDENCE_MANIFEST_SCHEMA, CHC_IN_PROCESS_REPLAY_CHECKER_NAME,
    CHC_PROOF_ARTIFACT_DIGEST_SCHEMA, CHC_PROOF_QUERY_ADMISSION_KEY_SCHEMA,
    CHC_PROOF_QUERY_CACHE_ADMISSION_DECISION_SCHEMA, CHC_PROOF_QUERY_CACHE_ADMISSION_POLICY_SCHEMA,
    CHC_PROOF_QUERY_CACHE_LOOKUP_KEY_SCHEMA, CHC_PROOF_QUERY_CACHE_LOOKUP_RESULT_SCHEMA,
    CHC_PROOF_QUERY_CACHE_METRICS_SCHEMA, CHC_PROOF_QUERY_CACHE_SCHEMA,
    CHC_PROOF_RUN_MODEL_ARTIFACT_ROLE, CHC_PROOF_RUN_MODEL_ARTIFACT_SCHEMA,
    CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_ROLE, CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_SCHEMA,
    CHC_PROOF_TRANSCRIPT_CONSUMER_EVIDENCE_SCHEMA, CHC_PROOF_TRANSCRIPT_SCHEMA,
    CHC_REPLAY_EVIDENCE_SCHEMA, NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA,
    NORMALIZED_CHC_INPUT_SCHEMA,
};
pub use qf_invariant_artifact::{
    parse_qf_invariant_model_artifact, prepare_qf_invariant_envelope_with_work,
    ChcQfInvariantModelArtifactError, ChcQfInvariantModelArtifactErrorReason,
    PreparedQfInvariantEnvelope, QfEnvelopePreparationError, QfInvariantEnvelopeView,
    CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_BYTES, CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_MODEL_BYTES,
    CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_NESTING_DEPTH,
    CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_PARAMETERS, CHC_QF_INVARIANT_MODEL_ARTIFACT_MAX_PREDICATES,
    CHC_QF_INVARIANT_MODEL_ARTIFACT_MODEL_FORMAT, CHC_QF_INVARIANT_MODEL_ARTIFACT_ROLE,
    CHC_QF_INVARIANT_MODEL_ARTIFACT_SCHEMA,
};

// Public engine API — consumed by ay binary, fuzz targets, examples, integration tests
pub use adaptive::{AdaptiveConfig, AdaptiveExecutionMode, AdaptivePortfolio};
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
pub use pdr::{DropOrder, OracleBackend, PdrConfig, PdrResult, PdrSolver, SpacerLane};
pub use portfolio::{
    BudgetPolicy, BudgetReport, EngineBudgetEntry, EngineConfig, EngineStopReason, EngineType,
    PortfolioConfig, PortfolioResult, PortfolioSolver,
};
pub use progress::{ChcProgressReport, ChcProgressSnapshot};
pub use run_meter::ChcRunWork;
pub use smt::{
    InterpolationResult, SmtContext, SmtLane, SmtResult, SmtValue, UnsatCoreDiagnostics,
};

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

    /// The process-wide `HornSmt` session counters as one line (#horn-smt-session
    /// Rung 1 board, design §10.4), or `None` when no query was ever routed —
    /// i.e. the session is off. The CLI prints it to stderr at the end of a
    /// CHC run when `--chc-session-stats` is set.
    pub fn horn_session_totals_report() -> Option<String> {
        crate::smt::lane::totals_report()
    }

    /// The Rung-4 coverage census lines (`--chc-session-coverage`; empty
    /// otherwise).
    pub fn horn_session_coverage_report() -> Vec<String> {
        crate::smt::lane::census::coverage_report()
    }

    /// `true` when `--chc-session-stats` asked for the session report.
    pub fn horn_session_stats_requested() -> bool {
        crate::smt::lane::session_stats_enabled()
    }

    const BMC_PROOF_ENGINE_NAME: &str = "bmc";
    const PDR_PROOF_ENGINE_NAME: &str = "pdr";
    const PDR_PROOF_VALIDATION_TIMEOUT: Duration = Duration::from_secs(30);

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
        let solve_deadline = deadline::for_config(&config);
        // Install a thread-wide solve deadline so EVERY check_sat on this thread
        // (main PDR context, startup discovery, the fresh re-validation verifier,
        // and any portfolio engine) is bounded by solve_timeout — closing the gap
        // where a fresh context never received a per-context deadline and a query
        // handed `timeout = None` could spin past the deadline (the integer-modulo
        // hang). Restored on drop.
        let _solve_deadline = crate::smt::ScopedSolveDeadline::new(solve_deadline);
        ay_core::catch_ay_panics(
            AssertUnwindSafe(|| Ok(solve_pdr_proof_unchecked(problem, config, solve_deadline))),
            |reason| Err(ChcError::Internal(reason)),
        )
    }

    /// Run the exact proof-grade PDR entry point and atomically bind whole-run
    /// timing, stop classification, and a direct-PDR strategy observation to
    /// its problem-bound result.
    ///
    /// This is the reporting counterpart of [`solve_pdr_proof`]; it does not
    /// substitute the adaptive portfolio or perform a diagnostic re-run.
    pub fn solve_pdr_proof_with_budget_report(
        problem: ChcProblem,
        config: PdrConfig,
    ) -> ChcResult<ChcProofRunWithBudgetReport> {
        let configured_budget = config.solve_timeout;
        let cancellation = config.cancellation_token.clone();
        let started = ay_core::time::Instant::now();
        let proof_run = solve_pdr_proof(problem, config)?;
        let elapsed = started.elapsed();
        let cancellation_requested_at_return =
            cancellation.is_some_and(|token| token.is_cancelled());
        Ok(ChcProofRunWithBudgetReport::from_direct_pdr(
            proof_run,
            configured_budget,
            elapsed,
            cancellation_requested_at_return,
        ))
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
    /// Both configured cancellation channels reach replay's cooperative polls
    /// and active SMT work. Rendering, offline checking and teardown remain opaque;
    /// this does not promise a hard cancellation deadline. The final poll
    /// admits attachment; disposal of the original run can still follow it.
    pub fn solve_pdr_proof_with_checked_replay(
        problem: ChcProblem,
        config: PdrConfig,
        replay_budget: Duration,
    ) -> ChcResult<ChcPdrProofRun> {
        let cancellation = config.effective_cancellation_token();
        let run = solve_pdr_proof(problem, config)?;
        Ok(attach_checked_replay_with_cancellation(
            run,
            replay_budget,
            cancellation.as_ref(),
        ))
    }

    fn attach_checked_replay_with_cancellation(
        run: ChcPdrProofRun,
        replay_budget: Duration,
        cancellation: Option<&CancellationToken>,
    ) -> ChcPdrProofRun {
        match cancellation {
            Some(token) => {
                attach_checked_replay_with_controls(run, replay_budget, &mut || true, Some(token))
            }
            None => attach_checked_replay_with_progress(run, replay_budget, &mut || true),
        }
    }

    /// Fail-closed helper: swap in checked-replay metadata when the pass
    /// succeeds, otherwise return the metadata-only run unchanged.
    fn attach_checked_replay_with_progress(
        run: ChcPdrProofRun,
        replay_budget: Duration,
        progress: &mut dyn FnMut() -> bool,
    ) -> ChcPdrProofRun {
        attach_checked_replay_with_controls(run, replay_budget, progress, None)
    }

    fn attach_checked_replay_with_controls(
        run: ChcPdrProofRun,
        replay_budget: Duration,
        progress: &mut dyn FnMut() -> bool,
        parent: Option<&CancellationToken>,
    ) -> ChcPdrProofRun {
        if !run.accepted_as_proof() {
            return run;
        }
        let started = ay_core::time::Instant::now();
        let cancellation = parent.map(crate::smt::executor_adapter::ReplayCancellation::new);
        let mut stopped = false;
        let mut poll = || {
            if !stopped {
                stopped = started.elapsed() >= replay_budget
                    || cancellation
                        .as_ref()
                        .is_some_and(|token| token.is_cancelled())
                    || !progress()
                    || cancellation
                        .as_ref()
                        .is_some_and(|token| token.is_cancelled())
                    || started.elapsed() >= replay_budget;
            }
            !stopped
        };
        let checked = ay_core::catch_ay_panics(
            AssertUnwindSafe(|| {
                let checked = run.run_checked_replay_with_controls_started_at(
                    started,
                    replay_budget,
                    &mut poll,
                    parent,
                )?;
                let attached = checked.into_proof_run();
                if !poll() {
                    return Err(ChcError::Verification(
                        "checked replay attachment interrupted; retaining original evidence"
                            .to_owned(),
                    ));
                }
                Ok(attached)
            }),
            |reason| Err(ChcError::Internal(reason)),
        );
        match checked {
            Ok(checked) => checked,
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
                // Parsing consumes the same caller clock, even though the
                // parser's opaque work is not a hard-latency guarantee.
                let solve_deadline = deadline::for_config(&config);
                let _solve_deadline = crate::smt::ScopedSolveDeadline::new(solve_deadline);
                let problem = ChcParser::parse(input)?;
                Ok(solve_pdr_proof_unchecked(problem, config, solve_deadline))
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
                // Do not mint a fresh budget after IO and parsing finish.
                let solve_deadline = deadline::for_config(&config);
                let _solve_deadline = crate::smt::ScopedSolveDeadline::new(solve_deadline);
                let input = std::fs::read_to_string(path)?;
                let problem = ChcParser::parse(&input)?;
                Ok(solve_pdr_proof_unchecked(problem, config, solve_deadline))
            }),
            |reason| Err(ChcError::Internal(reason)),
        )
    }

    /// Run `run` on a metered GuardTree node and attach its work: with no
    /// effort observation only, the count decides nothing (P4a slice 7,
    /// guard-tree.md §13), and below a node that counts no node is opened and
    /// the work is `None`; with an effort the node is allotted it, its own
    /// deadline is the run's `backstop`, and its count is the run's stop
    /// (slice 8, §14). A run that ends without a verdict is settled first, so
    /// its work names a backstop that ended it (`cancelled`: the run's token).
    fn metered(
        effort: Option<u64>,
        backstop: Option<ay_core::time::Instant>,
        cancelled: impl FnOnce() -> bool,
        run: impl FnOnce() -> ChcPdrProofRun,
    ) -> ChcPdrProofRun {
        let meter = crate::run_meter::RunMeter::open(effort, backstop);
        let run = run();
        if run.result().is_unknown() {
            meter.settle(cancelled());
        }
        run.with_work(meter.close())
    }

    /// Whether the run's own cancellation token is set (`metered`'s settle).
    fn run_cancelled(config: &PdrConfig) -> bool {
        config
            .effective_cancellation_token()
            .is_some_and(|token| token.is_cancelled())
    }

    fn solve_pdr_proof_unchecked(
        problem: ChcProblem,
        config: PdrConfig,
        solve_deadline: Option<ay_core::time::Instant>,
    ) -> ChcPdrProofRun {
        let effort = config.effort;
        let token = config.effective_cancellation_token();
        metered(
            effort,
            solve_deadline,
            || token.is_some_and(|token| token.is_cancelled()),
            || solve_pdr_proof_unmetered(problem, config, solve_deadline),
        )
    }

    fn solve_pdr_proof_unmetered(
        problem: ChcProblem,
        mut config: PdrConfig,
        solve_deadline: Option<ay_core::time::Instant>,
    ) -> ChcPdrProofRun {
        config.strict_proofs = true;
        // Proof-grade solving must construct an invariant for the exact
        // caller-supplied clauses. The ordinary solve-time nullary-fail
        // expansion is equisatisfiable, but it erases predicates such as
        // `error` from the model surface and has no model backtranslation.
        // Keeping the original clauses here also makes the solving,
        // validation, and checked-replay boundaries agree.
        config.preserve_original_clauses = true;
        // Under an effort the run's count is its stop: no count cap beside it
        // (P4a slice 8, DR-37).
        if config.effort.is_some() {
            config.disarm_count_caps();
        }

        // Complete compact values avoid datatype tree expansion in PDR setup.
        // This candidate-only route replays every original clause and keeps
        // the original owner for subsequent checked export/publication.
        let cancellation = config.effective_cancellation_token();
        if let Some(result) = crate::compact_datatype_route::acceptance::run(
            &problem,
            solve_deadline,
            cancellation.as_ref(),
            config.memory_budget,
        ) {
            let result = VerifiedChcResult::from_validated(
                result,
                ValidationEvidence::CounterexampleVerification,
            );
            let result =
                downgrade_unsafe_if_overapproximated(result, problem.has_stripped_body_forall());
            let result = enforce_pdr_proof_return_boundary(result, &config, solve_deadline);
            return ChcPdrProofRun::new(problem, result, PDR_PROOF_ENGINE_NAME);
        }

        // Keep a propositional refutation's original-clause ground witness.
        // The helper retains validation/body-forall/publication gates. Only
        // missing evidence falls through; observed interruption is terminal.
        if let Some(result) = propositional::run(&problem, &config, solve_deadline) {
            return ChcPdrProofRun::new(problem, result, PDR_PROOF_ENGINE_NAME);
        }

        // Exact acyclic BMC certificate prepass.
        //
        // Scalar/acyclic/BV multi-predicate problems are decided *completely* by
        // exact acyclic path expansion: every error-reachability branch is
        // checked UNSAT in the original theory (see
        // `bmc::BmcSolver::solve_acyclic_safe_first_once`, which trusts only
        // UNSAT as a safety proof). Pure PDR/IC3 can return Inconclusive on
        // these problems even though they are trivially safe, so try the exact
        // certificate first. Only a `Safe` certificate that the independent
        // empty-model check (`crate::empty_acyclic_safe_check`) confirms is
        // accepted as proof; any other outcome falls through to the PDR search.
        // Under an effort the prepass is closed, and the PDR search decides
        // (`BmcSolver::closed_under_effort`, P4a slice 8).
        if let Some(result) = confirmed_acyclic_bmc_certificate(&problem, &config, solve_deadline) {
            return ChcPdrProofRun::new(problem, result, PDR_PROOF_ENGINE_NAME);
        }

        // Finite observed cells can expose a scalar candidate invariant. The
        // candidate must lift to complete original signatures and pass every
        // original clause; reduced Unsafe has no refutation authority.
        if let Some(result) = array_observation::run(&problem, &config, solve_deadline) {
            return ChcPdrProofRun::new(problem, result, PDR_PROOF_ENGINE_NAME);
        }

        // Array columns can obscure an otherwise scalar invariant. This
        // bounded attempt only supplies a lifted candidate: admission still
        // checks the unchanged original clauses, and projected Unsafe never
        // stands in for an original counterexample.
        if let Some(result) = array_projection::run(&problem, &config, solve_deadline) {
            return ChcPdrProofRun::new(problem, result, PDR_PROOF_ENGINE_NAME);
        }

        // A cyclic PDR search can miss even shallow original reachability.
        // Only a fresh original-clause BMC witness, independently revalidated
        // through the ordinary strict boundary, may end this bounded attempt.
        if let Some(result) = original_unsafe::run(&problem, &config, solve_deadline) {
            return ChcPdrProofRun::new(problem, result, PDR_PROOF_ENGINE_NAME);
        }

        let raw = PdrSolver::solve_problem(&problem, config.clone());
        let result = validate_pdr_proof_result(&problem, raw, &config, solve_deadline);
        // Refutations do not survive body-`forall` over-approximation.
        let result =
            downgrade_unsafe_if_overapproximated(result, problem.has_stripped_body_forall());
        let result = enforce_pdr_proof_return_boundary(result, &config, solve_deadline);
        ChcPdrProofRun::new(problem, result, PDR_PROOF_ENGINE_NAME)
    }

    /// The exact acyclic BMC certificate prepass of
    /// `solve_pdr_proof_unmetered`: a `Safe` certificate the independent
    /// empty-model check confirms, at the proof return boundary; `None`
    /// otherwise, so the PDR search decides.
    fn confirmed_acyclic_bmc_certificate(
        problem: &ChcProblem,
        config: &PdrConfig,
        solve_deadline: Option<ay_core::time::Instant>,
    ) -> Option<VerifiedChcResult> {
        let (true, depth) = run_scalar_acyclic_bmc_certificate(problem, config)? else {
            return None;
        };
        let recheck_budget = solve_deadline.map_or(PDR_PROOF_VALIDATION_TIMEOUT, |deadline| {
            deadline.saturating_duration_since(ay_core::time::Instant::now())
        });
        let cancellation = config.cancellation_token.as_ref();
        if !crate::empty_acyclic_safe_check::confirmed(problem, recheck_budget, cancellation) {
            return None;
        }
        let result = VerifiedChcResult::from_validated(
            ChcEngineResult::Safe(InvariantModel::default()),
            ValidationEvidence::ScalarAcyclicBmcExhaustive { max_depth: depth },
        );
        Some(enforce_pdr_proof_return_boundary(
            result,
            config,
            solve_deadline,
        ))
    }

    fn enforce_pdr_proof_return_boundary(
        result: VerifiedChcResult,
        config: &PdrConfig,
        solve_deadline: Option<ay_core::time::Instant>,
    ) -> VerifiedChcResult {
        // Under an effort a result the run decided is the count's: the solve
        // deadline is a backstop that stops a search, never a reason to
        // discard what was decided within B, and a cancel that came after the
        // decision did not stop it (P4a slice 8). A stopped search publishes
        // `unknown` before it reaches here.
        if config.effort.is_some() {
            return result;
        }
        let cancelled = config
            .cancellation_token
            .as_ref()
            .is_some_and(CancellationToken::is_cancelled);
        let deadline_expired =
            solve_deadline.is_some_and(|deadline| ay_core::time::Instant::now() >= deadline);
        let compact_stopped = match &result {
            VerifiedChcResult::Unsafe(cex) => cex
                .counterexample()
                .compact_evidence()
                .is_some_and(|evidence| evidence.owner().poll().is_err()),
            _ => false,
        };
        if (cancelled || deadline_expired || compact_stopped)
            && matches!(
                &result,
                VerifiedChcResult::Safe(_) | VerifiedChcResult::Unsafe(_)
            )
        {
            VerifiedChcResult::from_validated(
                ChcEngineResult::Unknown,
                ValidationEvidence::FullVerification,
            )
        } else {
            result
        }
    }

    fn validation_config(base: &PdrConfig) -> PdrConfig {
        PdrConfig {
            verbose: base.verbose,
            strict_proofs: true,
            cancellation_token: base.cancellation_token.clone(),
            solve_timeout: Some(PDR_PROOF_VALIDATION_TIMEOUT),
            memory_budget: base.memory_budget,
            disable_array_scalarization: true,
            // Validators never run the Spacer lane (Workstream B, S10).
            spacer: SpacerLane::OFF,
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
            memory_budget: base.memory_budget,
            disable_array_scalarization: true,
            // Validators never run the Spacer lane (Workstream B, S10).
            spacer: SpacerLane::OFF,
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
    /// when the caller-provided empty model of an acyclic certificate-class
    /// problem is confirmed both by exhaustive acyclic BMC and by
    /// `crate::empty_acyclic_safe_check`, which decides the original clauses
    /// without any CHC engine.
    /// Panics from the internal verifier are converted to [`ChcError::Internal`].
    /// For a rejection/stop reason use [`validate_external_invariant_model_typed`];
    /// false alone is NOT evidence of a refuted model.
    pub fn validate_external_invariant_model(
        problem: &ChcProblem,
        model: &InvariantModel,
        config: &PdrConfig,
    ) -> ChcResult<bool> {
        validate_external_invariant_model_typed(problem, model, config)
            .map(|result| result == ExternalInvariantValidation::Valid)
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
        // The validation's backstop: its budget, the solve timeout, runs from
        // here (`external_model_validation_config`).
        let backstop = config
            .solve_timeout
            .and_then(|timeout| ay_core::time::Instant::now().checked_add(timeout));
        let meter = crate::run_meter::RunMeter::open(config.effort, backstop);
        // Mandatory re-validation gate. This is the entire soundness story: the
        // candidate is not trusted until the full clause check confirms it.
        // `?` propagates a verifier panic as `Err` (also non-accepting).
        if !validate_external_invariant_model(&problem, &model, &config)? {
            // Candidate rejected — emit a NON-accepted run. Mirrors the Unknown
            // arm of `validate_pdr_proof_result`: the full clause check ran and
            // did not confirm the model, so no proof-grade Safe is emitted.
            let result = VerifiedChcResult::unknown_candidate_not_admitted();
            meter.settle(run_cancelled(&config));
            return Ok(ChcPdrProofRun::new(problem, result, PDR_PROOF_ENGINE_NAME)
                .with_work(meter.close()));
        }

        // Re-validated: the full init + transition + query clause check passed
        // in a fresh verifier, so promoting to proof-grade Safe with
        // FullVerification evidence is honest.
        let result = VerifiedChcResult::from_validated(
            ChcEngineResult::Safe(model),
            ValidationEvidence::FullVerification,
        );
        Ok(ChcPdrProofRun::new(problem, result, PDR_PROOF_ENGINE_NAME).with_work(meter.close()))
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
        // INV-S2 (#horn-smt-session §7.2): the excludes-error Safe gate.
        let _verification_pin = crate::smt::lane::ScopedVerificationMode::install();
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
    /// empty-model validation — the SAME validation the discharge gate
    /// (`external_invariant_model_excludes_error`) already applies to
    /// empty models via `validate_empty_scalar_acyclic_bmc_certificate`
    /// (exhaustive acyclic BMC AND the engine-free
    /// `crate::empty_acyclic_safe_check`): complete for acyclic
    /// scalar/finite-ADT DAGs, fail-closed on SMT-unknowns,
    /// arrays/reals/recursive datatypes excluded. When both confirm Safe,
    /// there are no invariant obligations to replay and this returns an
    /// empty set (the certificate stands on the re-validated exhaustive
    /// search). In every other case — non-empty models, non-eligible
    /// problems, or a validation that does not confirm —
    /// this defers to the standard exporter unchanged, preserving its
    /// fail-closed missing-interpretation error. Nothing is fabricated:
    /// this branch can only ever REMOVE the obligation step for proofs the
    /// validator independently re-establishes.
    pub fn chc_safe_replay_obligations(
        problem: &ChcProblem,
        model: &InvariantModel,
    ) -> ChcResult<Vec<ChcReplayObligation>> {
        // INV-S2 (#horn-smt-session §7.2): replay obligations are certificate
        // material; the re-proof they may run stays off the session.
        let _verification_pin = crate::smt::lane::ScopedVerificationMode::install();
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
            let config = PdrConfig::default()
                .with_strict_proofs(true)
                .with_spacer(SpacerLane::OFF);
            // Checked replay installs its ORIGINAL wall and linked sticky
            // caller token before rendering. Legacy callers without a scope
            // retain the existing finite validation allowance.
            let config = PdrConfig {
                cancellation_token: crate::smt::deadline::current_lane_token(),
                solve_timeout: Some(
                    crate::smt::deadline::smt_deadline_remaining()
                        .unwrap_or(PDR_PROOF_VALIDATION_TIMEOUT)
                        .min(PDR_PROOF_VALIDATION_TIMEOUT),
                ),
                ..config
            };
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

    fn validate_pdr_proof_result(
        problem: &ChcProblem,
        result: PdrResult,
        base_config: &PdrConfig,
        solve_deadline: Option<ay_core::time::Instant>,
    ) -> VerifiedChcResult {
        // INV-S2 (#horn-smt-session §7.2): the proof-run validator.
        let _verification_pin = crate::smt::lane::ScopedVerificationMode::install();
        match result {
            PdrResult::Safe(model) => {
                let mut verifier = PdrSolver::new(problem.clone(), validation_config(base_config));
                if verifier.verify_model_at_safe_boundary(&model, solve_deadline) {
                    VerifiedChcResult::from_validated(
                        ChcEngineResult::Safe(model),
                        ValidationEvidence::FullVerification,
                    )
                } else {
                    VerifiedChcResult::unknown_candidate_not_admitted()
                }
            }
            PdrResult::Unsafe(cex) => {
                if cex.compact_evidence().is_some() {
                    let cancellation = base_config.effective_cancellation_token();
                    return match crate::compact_datatype_route::acceptance::confirm(
                        problem,
                        &cex,
                        solve_deadline,
                        cancellation.as_ref(),
                        base_config.memory_budget,
                    ) {
                        Some(confirmed) => VerifiedChcResult::from_validated(
                            ChcEngineResult::Unsafe(confirmed),
                            ValidationEvidence::CounterexampleVerification,
                        ),
                        None => VerifiedChcResult::unknown_candidate_not_admitted(),
                    };
                }
                let mut verifier = PdrSolver::new(problem.clone(), validation_config(base_config));
                // Wrap what passed: the bounded replay's own trace when only the
                // replay decided, or the trace of `cex`'s validated ground derivation
                // when its steps claimed another one (see `confirm_counterexample`).
                if let Ok(confirmed) = verifier.confirm_counterexample(cex) {
                    VerifiedChcResult::from_validated(
                        ChcEngineResult::Unsafe(confirmed),
                        ValidationEvidence::CounterexampleVerification,
                    )
                } else {
                    VerifiedChcResult::unknown_candidate_not_admitted()
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
    pub fn solve_bmc_only(problem: ChcProblem, mut bmc_config: BmcConfig) -> VerifiedChcResult {
        let attempt = direct_bmc::Attempt::capture(&mut bmc_config);
        attempt.solve(|| problem, bmc_config)
    }

    /// Map `Unsafe` -> `Unknown` when the problem was over-approximated by
    /// body-`forall` stripping. `Safe` and `Unknown` pass through untouched:
    /// the ONLY legal transition here is `Unsafe -> Unknown`, so this can never
    /// gain or lose a proof.
    pub(crate) fn downgrade_unsafe_if_overapproximated(
        result: VerifiedChcResult,
        overapproximated: bool,
    ) -> VerifiedChcResult {
        match result {
            VerifiedChcResult::Unsafe(_) if overapproximated => VerifiedChcResult::Unknown(
                crate::engine_result::VerifiedUnknownMarker::overapproximated_refutation(),
            ),
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
        let memory = crate::bmc::memory::Budget::capture(bmc_config.memory_budget, None);
        if !memory.open() {
            return Ok(VerifiedChcResult::Unknown(
                crate::engine_result::VerifiedUnknownMarker::new(),
            ));
        }
        let _memory = memory.install();
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
        mut bmc_config: BmcConfig,
    ) -> ChcResult<ChcPdrProofRun> {
        let attempt = direct_bmc::Attempt::capture(&mut bmc_config);
        ay_core::catch_ay_panics(
            AssertUnwindSafe(|| Ok(solve_bmc_proof_unchecked(problem, bmc_config, &attempt))),
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
    /// The configured cancellation token also reaches replay's cooperative
    /// polls and active SMT work, with the same limitations as the PDR variant.
    pub fn solve_bmc_proof_with_checked_replay(
        problem: ChcProblem,
        mut bmc_config: BmcConfig,
        replay_budget: Duration,
    ) -> ChcResult<ChcPdrProofRun> {
        let attempt = direct_bmc::Attempt::capture(&mut bmc_config);
        let memory = attempt.memory;
        let _memory = memory.install();
        let cancellation = bmc_config.base.cancellation_token.clone();
        let run = ay_core::catch_ay_panics(
            AssertUnwindSafe(|| Ok(solve_bmc_proof_unchecked(problem, bmc_config, &attempt))),
            |reason| Err(ChcError::Internal(reason)),
        )?;
        Ok(attach_checked_replay_with_controls(
            run,
            replay_budget,
            &mut || memory.open(),
            cancellation.as_ref(),
        ))
    }

    /// Parse a CHC problem from an SMT-LIB string and run BMC-only evidence mode.
    pub fn solve_bmc_proof_from_str(
        input: &str,
        bmc_config: BmcConfig,
    ) -> ChcResult<ChcPdrProofRun> {
        let memory = crate::bmc::memory::Budget::capture(bmc_config.memory_budget, None);
        if !memory.open() {
            return Err(ChcError::TermMemoryBudgetExhausted);
        }
        let _memory = memory.install();
        let problem = ChcParser::parse(input).map_err(|e| ChcError::Parse(e.to_string()))?;
        solve_bmc_proof(problem, bmc_config)
    }

    fn solve_bmc_proof_unchecked(
        problem: ChcProblem,
        bmc_config: BmcConfig,
        attempt: &direct_bmc::Attempt,
    ) -> ChcPdrProofRun {
        metered(
            None,
            None,
            || false,
            || {
                let result = attempt.solve(|| problem.clone(), bmc_config);
                ChcPdrProofRun::new(problem, result, BMC_PROOF_ENGINE_NAME)
            },
        )
    }

    mod acyclic_certificate;
    mod external_model_validation;
    pub use external_model_validation::{
        validate_external_invariant_model_typed, validate_external_invariant_model_with_owner,
        ExternalInvariantValidation, ExternalInvariantValidationOwner,
    };
    mod ambient_cancellation;
    mod array_observation;
    mod array_projection;
    mod deadline;
    mod direct_bmc;
    mod original_unsafe;
    mod propositional;
    use acyclic_certificate::{
        run_scalar_acyclic_bmc_certificate, validate_empty_scalar_acyclic_bmc_certificate,
    };

    #[cfg(test)]
    mod effort_tests;
    #[cfg(test)]
    mod replay_progress_tests;
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
