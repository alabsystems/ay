// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! AY DPLL(T) - Theory integration framework
//!
//! Integrates the SAT solver with theory solvers using the DPLL(T) architecture.
//!
//! # DPLL(T) Algorithm
//!
//! The DPLL(T) framework combines SAT solving with theory reasoning:
//!
//! 1. Parse SMT-LIB input and elaborate to internal representation
//! 2. Convert Boolean structure to CNF via Tseitin transformation
//! 3. Run CDCL SAT solver:
//!    - After each propagation, check theory consistency
//!    - If theory finds conflict, add theory lemma as clause
//!    - If theory propagates, add propagated literals
//! 4. When SAT solver finds SAT, verify full model with theory
//! 5. If theory rejects, add blocking clause and continue
//!
//! # Executor
//!
//! The [`Executor`] struct provides a high-level interface for executing SMT-LIB
//! commands with automatic theory selection based on the logic:
//!
//! ```
//! use ay_dpll::Executor;
//! use ay_frontend::parse;
//!
//! let input = r#"
//!     (set-logic QF_UF)
//!     (declare-const a Bool)
//!     (assert a)
//!     (check-sat)
//! "#;
//!
//! let commands = parse(input).unwrap();
//! let mut exec = Executor::new();
//! let outputs = exec.execute_all(&commands).unwrap();
//! assert_eq!(outputs, vec!["sat"]);
//! ```

#![warn(missing_docs)]
#![warn(clippy::all)]
#![allow(
    // Stylistic solver-code lints. This crate re-warns `clippy::all` above, which
    // overrides the workspace `[lints]` allows, so the same churn-only lints are
    // re-allowed here (see root Cargo.toml [workspace.lints.clippy] for rationale).
    clippy::collapsible_match,
    clippy::doc_lazy_continuation,
    clippy::extend_with_drain,
    clippy::manual_contains,
    clippy::op_ref,
    clippy::unnecessary_map_or,
    clippy::large_stack_frames,
    clippy::missing_fields_in_debug,
    clippy::option_option,
    clippy::result_large_err,
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::used_underscore_items
)]
#![cfg_attr(test, allow(clippy::large_stack_arrays))]

// Import safe_eprintln! from ay-core (non-panicking eprintln replacement)
#[macro_use]
extern crate ay_core;

#[allow(unused_macros, unused_macro_rules)]
mod pipeline_fns;

#[macro_use]
mod pipeline_setup_macros;
#[allow(unused_macros)]
#[macro_use]
mod pipeline_split_handler_macros;
#[macro_use]
mod pipeline_incremental_macros;
pub(crate) mod warm_theory_flag;
#[macro_use]
mod pipeline_incremental_split_lazy_shared_macros;
#[macro_use]
mod pipeline_incremental_split_lazy_macros;
#[macro_use]
mod pipeline_incremental_split_assume_macros;
#[macro_use]
mod pipeline_incremental_split_eager_shared_macros;
#[allow(unused_macro_rules)]
#[macro_use]
mod pipeline_incremental_split_eager_macros;
#[allow(unused_macro_rules)]
#[macro_use]
mod pipeline_incremental_split_eager_persistent_macros;
#[macro_use]
mod pipeline_incremental_split_macros;

pub mod api;

/// Semantic checker for theory-of-arrays (select/store) proof steps (Phase 6).
pub mod array_proof_check;

/// Semantic checker for bit-vector theory proof steps (Phase 6).
pub mod bv_proof_check;

/// Compile-time feature flag constants for downstream crate introspection.
pub mod feature_flags {
    /// Internal Alethe proof checker enabled. Always true: the former
    /// `proof-checker` feature flag was removed 2026-07-14 — the checker
    /// is the production soundness bar and is compiled unconditionally.
    /// The constant is retained so `ay --features` keeps reporting it.
    pub const PROOF_CHECKER: bool = true;
}

mod assume_step_result;
pub(crate) mod bound_refinement;
pub(crate) mod cegqi;
mod clause_application;
mod combined_solvers;
mod construction;
mod diagnostic_trace;
mod dpll_error;
mod dpll_solve;
mod dpll_support;
mod dpll_tracing;
pub(crate) mod ematching;
pub mod executor;
mod executor_format;
pub(crate) mod executor_types;
pub(crate) mod extension;
pub(crate) mod features;
mod incremental_proof_cache;
mod incremental_state;
mod logic_detection;
pub(crate) mod memory;
pub(crate) mod minimize;
pub(crate) mod preprocess;
pub(crate) mod proof_tracker;
pub mod qe;
pub(crate) mod quantifier_manager;
// Candidate-REJECTION diagnosis instrumentation (env-gated `AY_REJECT_INSTRUMENT`,
// verdict-neutral). Observes the depth-4 DT candidate-enumeration loop.
mod reject_instrument;
pub(crate) mod sat_proof_manager;
pub(crate) mod skolemize;
mod solve_common;
mod solve_loop;
mod solve_step;
mod solve_step_result;
mod term_helpers;
mod theory_check;
pub(crate) mod theory_debug_flags;
mod theory_dispatch;
pub(crate) mod theory_inference;
pub(crate) mod verification;

#[cfg(test)]
mod executor_tests;

pub use api::{
    all_sat_enumeration_symbolic_execution_contract,
    all_sat_enumeration_symbolic_execution_contract_key_value_pairs,
    incremental_assumptions_symbolic_execution_contract,
    incremental_assumptions_symbolic_execution_contract_key_value_pairs,
    model_blocking_symbolic_execution_contract,
    model_blocking_symbolic_execution_contract_key_value_pairs,
    raw_smt_solve_profile_summary_from_process, raw_smt_solve_profile_summary_from_typed_details,
    raw_smt_solve_profile_summary_from_typed_summary, solver_capability_descriptor,
    solver_capability_descriptor_json, solver_capability_descriptor_key_value_pairs,
    solver_capability_descriptor_manifest,
    symbolic_execution_all_supported_capability_route_readiness,
    symbolic_execution_all_supported_capability_route_readiness_for_decision,
    symbolic_execution_all_supported_capability_route_readiness_json,
    symbolic_execution_all_supported_capability_route_readiness_key_value_rows,
    symbolic_execution_all_supported_capability_route_readiness_text_lines,
    symbolic_execution_capability_route_readiness,
    symbolic_execution_capability_route_readiness_for_decision,
    symbolic_execution_capability_route_readiness_json,
    symbolic_execution_capability_route_readiness_key_value_rows,
    symbolic_execution_capability_route_readiness_text_lines, symbolic_execution_contract_manifest,
    symbolic_execution_contract_manifest_diagnostic_summary,
    symbolic_execution_contract_manifest_diagnostic_summary_for_round_trip,
    symbolic_execution_contract_manifest_diagnostic_summary_json,
    symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows,
    symbolic_execution_contract_manifest_diagnostic_summary_text_lines,
    symbolic_execution_contract_manifest_health_diagnostic_lines,
    symbolic_execution_contract_manifest_health_key_value_rows,
    symbolic_execution_contract_manifest_health_report, symbolic_execution_contract_manifest_json,
    symbolic_execution_contract_manifest_key_value_pairs,
    symbolic_execution_contract_manifest_round_trip_health_report,
    symbolic_execution_downstream_contract_bundle,
    symbolic_execution_downstream_contract_bundle_json,
    symbolic_execution_downstream_contract_bundle_key_value_rows,
    symbolic_execution_downstream_contract_bundle_text_lines,
    symbolic_execution_route_admission_decision,
    symbolic_execution_route_admission_decision_for_summary,
    symbolic_execution_route_admission_decision_json,
    symbolic_execution_route_admission_decision_key_value_rows,
    symbolic_execution_route_admission_decision_text_lines, validate_raw_smt_solve_profile_summary,
    validate_raw_smt_solve_profile_summary_key_value_rows,
    validate_raw_smt_solve_profile_summary_text_lines,
    validate_symbolic_execution_all_supported_capability_route_readiness,
    validate_symbolic_execution_all_supported_capability_route_readiness_key_value_rows,
    validate_symbolic_execution_all_supported_capability_route_readiness_text_lines,
    validate_symbolic_execution_capability_route_readiness,
    validate_symbolic_execution_capability_route_readiness_key_value_rows,
    validate_symbolic_execution_capability_route_readiness_text_lines,
    validate_symbolic_execution_contract_manifest,
    validate_symbolic_execution_contract_manifest_diagnostic_summary,
    validate_symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows,
    validate_symbolic_execution_contract_manifest_diagnostic_summary_text_lines,
    validate_symbolic_execution_contract_manifest_key_value_pairs,
    validate_symbolic_execution_contract_manifest_round_trip,
    validate_symbolic_execution_downstream_contract_bundle,
    validate_symbolic_execution_downstream_contract_bundle_key_value_rows,
    validate_symbolic_execution_downstream_contract_bundle_text_lines,
    validate_symbolic_execution_route_admission_decision,
    validate_symbolic_execution_route_admission_decision_key_value_rows,
    validate_symbolic_execution_route_admission_decision_text_lines, AssumptionSolveDetails,
    CoreConstraintExplanation, DatatypeConstructor, DatatypeField, DatatypeSort, ExplanationKind,
    ExplanationReport, FuncDecl, IncrementalCoreEvolution, LimitKind, Logic, Model,
    ModelAssignmentExplanation, ModelBlockingAssignment, ModelBlockingClause,
    ModelBlockingClauseEvidence, ModelValue, RawSmtProcessSolveProfileInput,
    RawSmtSolveProfileReason, RawSmtSolveProfileSource, RawSmtSolveProfileStatus,
    RawSmtSolveProfileSummary, RawSmtSolveProfileValidationIssue,
    RawSmtSolveProfileValidationReason, RawSmtSolveProfileValidationReport,
    RawSmtSolveProfileValidationStatus, ResourceUsage, SatExplanation, SolveDecision,
    SolveDecisionProfileModelConsumerDecision, SolveDecisionProfileModelConsumerReason,
    SolveDecisionProfileModelConsumerStatus, SolveDecisionProfileSummary, SolveDetails,
    SolveProfileSummary, SolveResult, SolveUnknownSummary, Solver as ApiSolver, SolverCapability,
    SolverCapabilityCode, SolverCapabilityContract, SolverCapabilityDescriptor,
    SolverCapabilityDescriptorManifest, SolverCapabilityReason, SolverCapabilityStatus,
    SolverError, Sort as ApiSort, SymbolicExecutionCapabilityRouteReadiness,
    SymbolicExecutionCapabilityRouteReadinessReason,
    SymbolicExecutionCapabilityRouteReadinessStatus, SymbolicExecutionContractManifest,
    SymbolicExecutionContractManifestDiagnosticSummary, SymbolicExecutionContractManifestEntry,
    SymbolicExecutionContractManifestHealthDiagnostic,
    SymbolicExecutionContractManifestHealthIssue, SymbolicExecutionContractManifestHealthReason,
    SymbolicExecutionContractManifestHealthReport, SymbolicExecutionContractManifestHealthStatus,
    SymbolicExecutionDownstreamContractBundle, SymbolicExecutionDownstreamContractBundleReason,
    SymbolicExecutionDownstreamContractBundleStatus, SymbolicExecutionRouteAdmissionDecision,
    SymbolicExecutionRouteAdmissionReason, SymbolicExecutionRouteAdmissionStatus, Term,
    UnknownDiagnostic, UnknownExplanation, UnsatCoreSource, UnsatExplanation, VerificationLevel,
    VerificationSummary, VerifiedModel, VerifiedSolveResult,
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_CAP_BOUND,
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_CHECK_OUTCOME,
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION,
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_FORWARD_AY_EVIDENCE,
    AY_ALL_SAT_ENUMERATION_CONSUMER_RESPONSIBILITY_PROJECTION_SCOPE,
    AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES,
    AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES,
    AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES,
    AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
    AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION,
    AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES,
    AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES,
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_ACCEPT_MODEL_BOUNDARY,
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_ATOMIC_DETAILS,
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_BOOLEAN_ASSUMPTIONS,
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION,
    AY_INCREMENTAL_ASSUMPTIONS_CONSUMER_RESPONSIBILITY_UNSAT_CORE_ON_UNSAT,
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES,
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES,
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES,
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION,
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES,
    AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_REASON,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_REASON,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_STATUS, AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA_VERSION, AY_MODEL_BLOCKING_CLAUSE_SCHEMA,
    AY_MODEL_BLOCKING_CLAUSE_SCHEMA_VERSION,
    AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_ACCEPTED_MODEL_BOUNDARY,
    AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_FAIL_CLOSED_REJECTION,
    AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_FORWARD_AY_EVIDENCE,
    AY_MODEL_BLOCKING_CONSUMER_RESPONSIBILITY_NON_EMPTY_PROJECTION,
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_ACCEPTED_REASON_CODES,
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_ACCEPTED_STATUS_CODES,
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONSUMER_RESPONSIBILITIES,
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA_VERSION,
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_REJECTED_REASON_CODES,
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES,
    AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_CURRENT_REVISION,
    AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_REQUIRED_FIELDS, AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA,
    AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA_VERSION, AY_SOLVER_CAPABILITIES,
    AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA,
    AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA_VERSION,
    AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA, AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA_VERSION,
    AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA,
    AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA_VERSION,
    AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA, AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA_VERSION,
    AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_HELPERS,
    AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA,
    AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA_VERSION,
    AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_VALIDATORS, AY_SYMBOLIC_EXECUTION_CONTRACTS,
    AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_HELPERS,
    AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA,
    AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA_VERSION,
    AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA,
    AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA_VERSION,
    AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA,
    AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA_VERSION,
    AY_SYMBOLIC_EXECUTION_CONTRACT_REQUIRED_CAPABILITIES,
    AY_SYMBOLIC_EXECUTION_CONTRACT_ROUND_TRIP_VALIDATORS,
    AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_HELPERS,
    AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA,
    AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA_VERSION,
    AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_VALIDATION_ROW_GROUPS,
    AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_VALIDATORS,
    AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_HELPERS, AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA,
    AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA_VERSION,
    AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_VALIDATORS,
    AY_SYMBOLIC_EXECUTION_ROUTE_CURRENT_REVISION_KIND,
    AY_SYMBOLIC_EXECUTION_ROUTE_REQUIRED_CONTRACT_REVISION,
    AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER, AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_CRATE,
    AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_PATH_KIND,
};
// Crate-internal re-exports (used within ay-dpll, not exposed externally)
pub(crate) use sat_proof_manager::SatProofManager;

// Public API re-exports (used by downstream crates)
pub use assume_step_result::AssumeStepResult;
pub use ay_core::Proof;
pub use dpll_error::DpllError;
pub use executor::Executor;
pub use executor_types::{
    ExecutorError, Result as ExecutorResult, StatValue, Statistics, UnknownReason,
};
pub use minimize::CounterexampleStyle;
pub use solve_step_result::SolveStepResult;

pub(crate) use dpll_support::{
    cnf_lit_to_sat, debug_dpll_enabled, debug_sync_enabled, iter_var_to_term_sorted,
    uflia_phase_round_debug, DpllConstructionTimings, DpllEagerStats, DpllSatState, DpllTimings,
    PhaseTimer, PropositionalTheory, SplitLoopTimingStats,
};
pub use dpll_support::{SatWarmState, SatWarmStateImportReport};
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
#[cfg(test)]
use ay_core::CnfLit;
#[cfg(test)]
use ay_core::TheoryPropagation;
#[cfg(test)]
use ay_core::TheoryResult;
use ay_core::{CnfClause, TermId, TermStore, TheorySolver};
pub(crate) use theory_dispatch::{FinalCheckResult, TheoryCheck, TheoryDispatch};

use ay_sat::{
    ClauseTrace, Literal, SatUnknownReason, Solver as SatSolver, TlaTraceWriter, Variable,
};

use crate::diagnostic_trace::DpllDiagnosticWriter;

/// DPLL(T) solver combining SAT and theory reasoning
pub struct DpllT<'a, T: TheorySolver> {
    /// The underlying SAT solver
    sat: SatSolver,
    /// The theory solver
    theory: T,
    /// Term store used for debug verification (e.g., Farkas checking).
    ///
    /// This is `None` when constructed via [`DpllT::new`], and `Some` when constructed
    /// via [`DpllT::from_tseitin`].
    terms: Option<&'a TermStore>,
    /// Mapping from CNF variables to term IDs (HashMap for O(1) lookup)
    var_to_term: HashMap<u32, TermId>,
    /// Mapping from term IDs to CNF variables (HashMap for O(1) lookup)
    term_to_var: HashMap<TermId, u32>,
    /// Theory atoms to communicate to theory solver (stable order + unique)
    theory_atoms: Vec<TermId>,
    /// Membership set for O(1) theory-atom dedup and lookup.
    theory_atom_set: HashSet<TermId>,
    /// Cached: `AY_DEBUG_DPLL` env var (checked once at construction)
    debug_dpll: bool,
    /// Cached: `AY_DEBUG_SYNC` env var (checked once at construction)
    debug_sync: bool,
    /// Count of theory conflicts encountered during solving (#4705).
    theory_conflict_count: u64,
    /// Count of theory propagation clauses added during solving (#4705).
    theory_propagation_count: u64,
    /// Count of partial clause events where `term_to_literal` dropped terms (#5000).
    partial_clause_count: u64,
    /// Count of theory Unknown returns (#8165).
    theory_unknown_count: u64,
    /// Maximum number of literals in any single theory conflict clause (#8165).
    conflict_max_literals: u64,
    /// Sum of literals across all theory conflict clauses (#8165).
    conflict_total_literals: u64,
    /// Number of literals removed by theory conflict minimization (#8424).
    theory_minimize_lits_removed: u64,
    /// Number of Farkas certificate verification failures (#8165).
    farkas_certificate_failures: u64,
    /// Number of Farkas certificate downgrades (conflict kept, cert dropped) (#8165).
    farkas_certificate_downgrades: u64,
    /// Number of semantic verifications skipped due to large term store budget (#8558).
    semantic_verify_budget_skips: u64,
    /// Monotonic counter for sampling-based verification on large formulas (#8558).
    /// Incremented on each verification opportunity; modular arithmetic selects
    /// which ones to actually verify.
    semantic_verify_sample_counter: u64,
    /// Whether the large-formula warning has been emitted for this solve (#8558).
    semantic_verify_warned: bool,
    /// Deterministic eager-extension counters for split-loop diagnostics (#6503).
    eager_stats: DpllEagerStats,
    /// Accumulated phase timing for DPLL(T) solve calls (#4802).
    timings: DpllTimings,
    /// Accumulated constructor timing for DPLL(T) setup work (#6364).
    construction_timings: DpllConstructionTimings,
    /// Optional DPLL(T) interaction diagnostic JSONL writer.
    diagnostic_trace: Option<DpllDiagnosticWriter>,
    /// Optional DPLL(T) TLA2 trace writer.
    dpll_tla_trace: Option<TlaTraceWriter>,
    /// Whether an internal model-scope `push()` is currently active on the theory solver.
    ///
    /// When `true`, the theory solver has an extra scope level from `sync_theory` that
    /// must be `pop()`-ed before returning from any solve method or mutating the
    /// scope stack via public `push()`/`pop()`/`reset_theory()`.
    ///
    /// This replaces the per-round `soft_reset()` approach: instead of clearing and
    /// re-asserting all theory atoms on every SAT model, we use `push/pop` to scope
    /// the model-level assertions, preserving learned theory state across rounds (#4520).
    model_scope_active: bool,
    /// Previous model's theory atom values, cached for identical-model skip optimization (#2138).
    ///
    /// When consecutive SAT models assign the same truth values to all theory atoms
    /// (only Tseitin encoding vars differ), we skip the expensive pop+push+re-assert
    /// cycle entirely since the theory solver already has the correct state.
    prev_theory_atom_values: Option<Vec<bool>>,
    /// Total number of theory atoms asserted via `sync_theory` across all solve rounds (#2138).
    sync_atoms_asserted: u64,
    /// Number of `sync_theory` calls skipped because theory atom values were identical (#2138).
    sync_skipped_identical: u64,
    /// Number of individual theory atoms whose value changed between consecutive models (#2138).
    sync_delta_changed: u64,
    /// Number of individual theory atoms whose value was unchanged between consecutive models (#2138).
    sync_delta_unchanged: u64,
    /// Datatype tautology literals for conflict re-verification (#8123).
    ///
    /// When solving a datatype-bearing problem, the executor pre-generates the
    /// constructor-disjointness and tester-evaluation tautologies (true in every
    /// model) and stashes them here. The semantic conflict verifier asserts these
    /// alongside the conflict so a fresh EUF solver can confirm genuine
    /// constructor-clash conflicts (`self = Ok(a) AND self = Err(b)`) instead of
    /// reporting them SAT (which previously degraded the solve to Unknown).
    /// Empty for non-datatype problems, making the verification path byte-identical
    /// to before.
    dt_verification_axioms: Vec<ay_core::TheoryLit>,
    /// Ground-instance support literals for conflict re-verification: each is a
    /// ground instance of an UNCONDITIONALLY-asserted Forall (a top-level
    /// conjunct), hence entailed by universal instantiation and true in every
    /// model of the problem. Threaded — combined with `dt_verification_axioms`
    /// at read time — into the fail-closed AUFLIA conflict-verification gate so
    /// a genuinely-UNSAT mixed conflict whose closure depended on e-matched
    /// Seq/prophecy instances is not re-solved Sat in the isolated combiner and
    /// spuriously degraded to Unknown. Kept SEPARATE from `dt_verification_axioms`
    /// (distinct provenance sources). Populated by the executor from
    /// `Executor::active_support_axioms`; empty for quantifier-free problems,
    /// making the verification path byte-identical to before.
    ematching_support_axioms: Vec<ay_core::TheoryLit>,
    /// Optional wall-clock deadline for the whole DPLL(T) solve, installed by
    /// the executor from its own solve controls (see [`DpllT::set_solve_controls`]).
    ///
    /// Before this existed, `solve_loop` drove the SAT solver through the
    /// non-interruptible extension entry (`should_stop = || false`), so the
    /// executor's `:timeout`/interrupt controls — installed by
    /// `Solver::check_sat` via `install_solve_controls` — never reached the
    /// extension CDCL loop. A non-converging theory-refinement solve was then
    /// unkillable from any outer layer (the compiler_consumer/large-workload divergence).
    solve_deadline: Option<ay_core::time::Instant>,
    /// Optional cooperative interrupt flag, installed together with
    /// [`Self::solve_deadline`] and also pushed into the underlying SAT
    /// solver's own interrupt handle so every CDCL loop top honors it.
    solve_interrupt: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
}

// Re-export the single source of truth for theory-atom routing from ay-core (#6881).
// Macros in pipeline_*_macros.rs use `$crate::is_theory_atom`, so this must be pub.
pub use ay_core::is_theory_atom;

impl<T: TheorySolver> DpllT<'_, T> {
    /// Safety bound for DPLL(T) theory refinement loops.
    ///
    /// If the SAT solver keeps producing models that the theory rejects
    /// (adding conflict clauses each time), the loop should eventually
    /// terminate because the finite set of theory lemmas is exhausted.
    /// This constant is a defensive upper bound: if we exceed it, something
    /// is diverging and we bail out with `Unknown` instead of hanging.
    const MAX_THEORY_REFINEMENTS: usize = 10_000;

    /// Create a new DPLL(T) solver with the given number of variables
    pub fn new(num_vars: usize, theory: T) -> Self {
        DpllT {
            sat: SatSolver::new(num_vars),
            theory,
            terms: None,
            var_to_term: HashMap::default(),
            term_to_var: HashMap::default(),
            theory_atoms: Vec::new(),
            theory_atom_set: HashSet::default(),
            debug_dpll: debug_dpll_enabled(),
            debug_sync: debug_sync_enabled(),
            theory_conflict_count: 0,
            theory_propagation_count: 0,
            partial_clause_count: 0,
            theory_unknown_count: 0,
            conflict_max_literals: 0,
            conflict_total_literals: 0,
            theory_minimize_lits_removed: 0,
            farkas_certificate_failures: 0,
            farkas_certificate_downgrades: 0,
            semantic_verify_budget_skips: 0,
            semantic_verify_sample_counter: 0,
            semantic_verify_warned: false,
            eager_stats: DpllEagerStats::default(),
            timings: DpllTimings::default(),
            construction_timings: DpllConstructionTimings::default(),
            diagnostic_trace: None,
            dpll_tla_trace: None,
            model_scope_active: false,
            prev_theory_atom_values: None,
            sync_atoms_asserted: 0,
            sync_skipped_identical: 0,
            sync_delta_changed: 0,
            sync_delta_unchanged: 0,
            dt_verification_axioms: Vec::new(),
            ematching_support_axioms: Vec::new(),
            solve_deadline: None,
            solve_interrupt: None,
        }
    }

    /// Install the executor's solve controls on this DPLL(T) instance.
    ///
    /// `interrupt` is additionally pushed into the underlying SAT solver's
    /// interrupt handle, so it is honored at every CDCL loop top (including
    /// the assumption loop, which takes no `should_stop` closure). `deadline`
    /// is polled by `solve_loop` at each round-trip and inside the extension
    /// CDCL loop via the interruptible entry's `should_stop` closure. Both
    /// only ever degrade the solve to `Unknown` — never a wrong verdict.
    pub fn set_solve_controls(
        &mut self,
        interrupt: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
        deadline: Option<ay_core::time::Instant>,
    ) {
        if let Some(flag) = &interrupt {
            self.sat.set_interrupt(flag.clone());
        }
        self.solve_interrupt = interrupt;
        self.solve_deadline = deadline;
    }

    /// Whether the installed solve controls request a stop right now.
    ///
    /// Cheap (one atomic load + one `Instant::now()` when a deadline is set).
    #[must_use]
    fn solve_controls_tripped(&self) -> bool {
        self.solve_interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
            || self
                .solve_deadline
                .is_some_and(|deadline| ay_core::time::Instant::now() >= deadline)
    }

    /// Set the datatype tautology literals used for conflict re-verification (#8123).
    ///
    /// Called by the executor right after construction on datatype-bearing solve
    /// paths. Each literal must be a datatype tautology (constructor disjointness
    /// or tester evaluation); see [`crate::verification::build_datatype_tautology_axioms`].
    pub fn set_dt_verification_axioms(&mut self, axioms: Vec<ay_core::TheoryLit>) {
        self.dt_verification_axioms = axioms;
    }

    /// Set the ground-instance support literals used for conflict re-verification
    /// (#AUFLIA-support). Each must be a ground instance of an
    /// unconditionally-asserted Forall (top-level conjunct) — see
    /// [`crate::ematching::collect_unconditional_foralls`]. Called by the
    /// executor right after construction alongside `set_dt_verification_axioms`.
    pub fn set_ematching_support_axioms(&mut self, axioms: Vec<ay_core::TheoryLit>) {
        self.ematching_support_axioms = axioms;
    }

    /// The combined support-axiom set (`dt_verification_axioms ++
    /// ematching_support_axioms`) asserted into the fail-closed conflict
    /// verifier. Both provenance sources are true in every model of the problem,
    /// so the union can only CONFIRM a genuine conflict, never launder a
    /// spurious one. Returns an owned `Vec` because the two fields are stored
    /// separately (distinct provenance) and combined only at read time.
    pub(crate) fn combined_support_axioms(&self) -> Vec<ay_core::TheoryLit> {
        if self.ematching_support_axioms.is_empty() {
            return self.dt_verification_axioms.clone();
        }
        if self.dt_verification_axioms.is_empty() {
            return self.ematching_support_axioms.clone();
        }
        let mut combined = Vec::with_capacity(
            self.dt_verification_axioms.len() + self.ematching_support_axioms.len(),
        );
        combined.extend_from_slice(&self.dt_verification_axioms);
        combined.extend_from_slice(&self.ematching_support_axioms);
        combined
    }

    /// Access the underlying SAT solver.
    pub fn sat_solver(&self) -> &SatSolver {
        &self.sat
    }

    /// Number of theory conflicts encountered during solving (#4705).
    #[must_use]
    pub fn num_theory_conflicts(&self) -> u64 {
        self.theory_conflict_count
    }

    /// Number of theory propagation clauses added during solving (#4705).
    #[must_use]
    pub fn num_theory_propagations(&self) -> u64 {
        self.theory_propagation_count
    }

    /// Number of partial clause events (#8165).
    #[must_use]
    pub fn num_partial_clauses(&self) -> u64 {
        self.partial_clause_count
    }

    /// Number of theory Unknown returns (#8165).
    #[must_use]
    pub fn num_theory_unknowns(&self) -> u64 {
        self.theory_unknown_count
    }

    /// Maximum number of literals in any theory conflict clause (#8165).
    #[must_use]
    pub fn conflict_max_literals(&self) -> u64 {
        self.conflict_max_literals
    }

    /// Sum of literals across all theory conflict clauses (#8165).
    #[must_use]
    pub fn conflict_total_literals(&self) -> u64 {
        self.conflict_total_literals
    }

    /// Number of literals removed by theory conflict minimization (#8424).
    /// Combines counts from both the DpllT path (theory_check, solve_common)
    /// and the eager extension path (propagate, check).
    #[must_use]
    pub fn theory_minimize_lits_removed(&self) -> u64 {
        self.theory_minimize_lits_removed + self.eager_stats.theory_minimize_lits_removed
    }

    /// Number of Farkas certificate verification failures (#8165).
    #[must_use]
    pub fn farkas_certificate_failures(&self) -> u64 {
        self.farkas_certificate_failures
    }

    /// Number of Farkas certificate downgrades (#8165).
    #[must_use]
    pub fn farkas_certificate_downgrades(&self) -> u64 {
        self.farkas_certificate_downgrades
    }

    /// Number of semantic verifications skipped due to large term store budget (#8558).
    /// Combines counts from both the DpllT path and the eager extension path.
    #[must_use]
    pub fn semantic_verify_budget_skips(&self) -> u64 {
        self.semantic_verify_budget_skips + self.eager_stats.semantic_verify_budget_skips
    }

    /// Total theory atoms asserted via `sync_theory` across all solve rounds (#2138).
    #[must_use]
    pub fn sync_atoms_asserted(&self) -> u64 {
        self.sync_atoms_asserted
    }

    /// Number of `sync_theory` calls skipped because theory atom values were identical (#2138).
    #[must_use]
    pub fn sync_skipped_identical(&self) -> u64 {
        self.sync_skipped_identical
    }

    /// Number of individual theory atoms whose value changed between consecutive models (#2138).
    #[must_use]
    pub fn sync_delta_changed(&self) -> u64 {
        self.sync_delta_changed
    }

    /// Number of individual theory atoms unchanged between consecutive models (#2138).
    #[must_use]
    pub fn sync_delta_unchanged(&self) -> u64 {
        self.sync_delta_unchanged
    }

    /// Last SAT-side `Unknown` reason reported by the underlying SAT solver.
    #[must_use]
    pub fn sat_unknown_reason(&self) -> Option<SatUnknownReason> {
        self.sat.last_unknown_reason()
    }

    /// Set the maximum learned clauses limit on the underlying SAT solver (#1609)
    pub fn set_max_learned_clauses(&mut self, limit: Option<usize>) {
        self.sat.set_max_learned_clauses(limit);
    }

    /// Set the maximum clause DB size limit (bytes) on the underlying SAT solver (#1609)
    pub fn set_max_clause_db_bytes(&mut self, limit: Option<usize>) {
        self.sat.set_max_clause_db_bytes(limit);
    }

    /// Set the SAT random seed used for tie-breaking in variable selection.
    pub fn set_random_seed(&mut self, seed: u64) {
        self.sat.set_random_seed(seed);
    }

    /// Enable periodic progress line emission on the underlying SAT solver.
    ///
    /// When enabled, the SAT solver emits a compact one-line status summary to
    /// stderr approximately every 5 seconds during CDCL solving.
    pub fn set_progress_enabled(&mut self, enabled: bool) {
        self.sat.set_progress_enabled(enabled);
    }

    /// Register a programmatic progress observer on the underlying SAT solver (#8155).
    ///
    /// The observer receives callbacks at conflict, restart, progress, and
    /// inprocessing events. When no observer is registered (the default),
    /// all callback sites are zero-cost (single branch that the predictor
    /// eliminates).
    ///
    /// AI consumers (model-checker-consumer, deductive-checks, verification-consumer) use this for stall detection
    /// and timeout decisions instead of parsing stderr progress lines.
    pub fn set_observer(&mut self, observer: Option<Box<dyn ay_sat::observer::SolveObserver>>) {
        self.sat.set_observer(observer);
    }

    /// Access the underlying SAT solver mutably
    pub fn sat_solver_mut(&mut self) -> &mut SatSolver {
        &mut self.sat
    }

    #[inline]
    fn freeze_var_if_needed(&mut self, var: Variable) {
        if !self.sat.is_frozen(var) {
            self.sat.freeze(var);
        }
    }

    fn internalize_registered_theory_atoms(&mut self) {
        let atoms = self.theory_atoms.clone();
        for atom in atoms {
            self.theory.internalize_atom(atom);
        }
    }

    /// Take the clause trace from the SAT solver (for SAT proof reconstruction)
    ///
    /// Returns the clause trace if one was being recorded, otherwise None.
    /// This consumes the trace from the SAT solver.
    pub fn take_clause_trace(&mut self) -> Option<ClauseTrace> {
        self.sat.take_clause_trace()
    }

    /// Set the deterministic search-time proof bookkeeping work budget
    /// (#A2b construction budget; `None` = unbudgeted). See
    /// `ay_sat::Solver::set_proof_bookkeeping_budget`.
    pub fn set_proof_bookkeeping_budget(&mut self, budget: Option<u64>) {
        self.sat.set_proof_bookkeeping_budget(budget);
    }

    /// Get a reference to the var_to_term mapping
    pub fn var_to_term(&self) -> &HashMap<u32, TermId> {
        &self.var_to_term
    }

    /// Clone a point-in-time var->term mapping snapshot.
    ///
    /// This is used by proof reconstruction paths that need an owned map after
    /// the DPLL wrapper is dropped.
    #[must_use]
    pub(crate) fn clone_var_to_term_snapshot(&self) -> HashMap<u32, TermId> {
        self.var_to_term.clone()
    }

    /// Access the underlying theory solver.
    pub fn theory_solver(&self) -> &T {
        &self.theory
    }

    /// Access the underlying theory solver mutably.
    pub fn theory_solver_mut(&mut self) -> &mut T {
        &mut self.theory
    }

    /// Add a clause to the solver
    pub fn add_clause(&mut self, literals: Vec<Literal>) {
        self.sat.add_clause(literals);
    }

    /// Add a CNF clause to the solver
    pub fn add_cnf_clause(&mut self, clause: &CnfClause) {
        let lits: Vec<Literal> = clause.0.iter().copied().map(Literal::from_dimacs).collect();
        self.sat.add_clause(lits);
    }

    /// Register a theory atom
    ///
    /// Theory atoms are terms that the theory solver needs to know about.
    /// When the SAT solver assigns a value to the corresponding variable,
    /// the theory solver is informed.
    pub fn register_theory_atom(&mut self, term: TermId, var: u32) {
        self.var_to_term.insert(var, term);
        self.term_to_var.insert(term, var);
        self.freeze_var_if_needed(Variable::new(var));
        // Keep theory atom order stable by appending only newly seen terms.
        // O(1)-amortized insertion avoids the O(n^2) Vec::insert pattern in
        // incremental LIA split registration (#4468).
        if self.theory_atom_set.insert(term) {
            self.theory_atoms.push(term);
            self.theory.internalize_atom(term);
        }
        // Boost VSIDS activity for theory atoms so the DPLL solver decides them
        // before pure Boolean encoding variables (#4919, #7982). Without this,
        // all variables start at activity 0 and the decision heuristic treats
        // Tseitin encoding vars and theory atoms equally. Theory atoms should
        // be decided first because: (1) they feed the theory solver which can
        // generate conflicts and propagations that prune the search space,
        // (2) Boolean encoding vars are determined by BCP once theory atoms
        // are assigned. Z3 does this via theory_var_init_value + mk_diseq.
        //
        self.sat.bump_variable_activity(Variable::new(var));
    }

    /// Get the term ID for a SAT variable, if it exists
    pub fn term_for_var(&self, var: Variable) -> Option<TermId> {
        self.var_to_term.get(&var.id()).copied()
    }

    /// Get the SAT variable for a term ID, if it exists
    pub fn var_for_term(&self, term: TermId) -> Option<Variable> {
        self.term_to_var.get(&term).map(|&v| Variable::new(v))
    }

    /// Convert a theory literal to a SAT literal
    fn term_to_literal(&self, term: TermId, value: bool) -> Option<Literal> {
        self.var_for_term(term).map(|var| {
            if value {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            }
        })
    }

    /// Convert a theory literal to a SAT literal, dynamically registering a
    /// new SAT variable if the term has no mapping yet (#6546).
    ///
    /// This is the mutable counterpart of [`term_to_literal`] for use in
    /// `check_theory_core` and other paths where `&mut self` is available.
    /// Array axiom terms generated during theory checking may not have been
    /// registered during formula preprocessing, so the lazy `step` solve
    /// mode must register them here to avoid dropping propagation clauses
    /// (the "partial clause" problem).
    pub(crate) fn term_to_literal_or_register(&mut self, term: TermId, value: bool) -> Literal {
        let var = if let Some(&var_idx) = self.term_to_var.get(&term) {
            Variable::new(var_idx)
        } else {
            let var = self.sat.new_var();
            self.register_theory_atom(term, var.id());
            var
        };
        if value {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        }
    }
}

#[cfg(test)]
mod dpll_tests;

#[cfg(kani)]
mod dpll_kani;
