// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! AY - A Rust constraint-solving toolkit
//!
//! This crate provides the public consumer API surface. Internal crates
//! (`ay_dpll`, `ay_core`, `ay_chc`, etc.) are implementation details and
//! should not be depended on directly by downstream consumers unless a crate
//! explicitly documents a narrow downstream surface such as `ay_dpll` capability
//! metadata and model-blocking primitives.
//!
//! # API Modules
//!
//! | Module | Stability | Purpose |
//! |--------|-----------|---------|
//! | Root (`ay::Solver`, etc.) | **Stable** | Core solver types, flat imports |
//! | [`api`] | **Stable** | Explicit single-module import path |
//! | [`prelude`] | **Stable** | Glob import for convenience |
//! | [`chc`] | **Stable** | CHC solver and library surface |
//! | [`executor`] | **Stable** | Text-driven SMT-LIB execution |
//! | [`allsat`] | **Stable** | Solution enumeration (ALL-SAT) |
//! | [`solution_visualization`] | Stable | ASCII/SVG rendering for recognized solution models |
//! | [`proof_emission`] | **Stable** | **Proof artifacts for supported UNSAT paths (Alethe / DRAT / LRAT / bit-blast) — start here for proofs** |
//! | [`proof_internals`] | Unstable | Deep proof reconstruction types |
//! | [`translate`] | Unstable | Formula translation framework |
//!
//! # Quick Start
//!
//! Use the re-exported API types for the native Rust API:
//!
//! ```no_run
//! use ay::{Logic, SolveResult, Sort, Solver, SolverConfig};
//! use std::time::Duration;
//!
//! // Create solver with a 5-second per-query timeout
//! let config = SolverConfig::default().with_timeout(Duration::from_millis(5000));
//! let mut solver = Solver::try_new_with_config(Logic::QfLia, config).unwrap();
//! let x = solver.declare_const("x", Sort::Int);
//! let zero = solver.int_const(0);
//! let x_gt_zero = solver.gt(x, zero);
//! solver.assert_term(x_gt_zero);
//!
//! let details = solver.check_sat_with_details();
//! match details.accept_for_consumer() {
//!     Ok(SolveResult::Sat) => {
//!         let model = solver
//!             .model()
//!             .expect("accepted SAT result has model")
//!             .into_inner();
//!         println!("x = {:?}", model.int_val("x"));
//!     }
//!     Ok(SolveResult::Unsat(_)) => println!("unsatisfiable"),
//!     Ok(SolveResult::Unknown) | Err(_) => {
//!         if let Some(reason) = details.unknown_reason {
//!             println!("unknown: {}", reason);
//!         }
//!     }
//!     Ok(_) => {}
//! }
//! ```

#![warn(missing_docs)]
#![warn(clippy::all)]

// Re-export the native API types as canonical
pub use ay_dpll::api::Solver;
pub use ay_dpll::api::SolverConfig;

pub use ay_dpll::api::{
    raw_smt_solve_profile_summary_from_process, raw_smt_solve_profile_summary_from_typed_details,
    raw_smt_solve_profile_summary_from_typed_summary, split_leading_set_logic,
    validate_raw_smt_solve_profile_summary, validate_raw_smt_solve_profile_summary_key_value_rows,
    validate_raw_smt_solve_profile_summary_text_lines, AssumptionSolveDetails,
    ConsumerAcceptanceError, FpSpecialKind, FuncDecl, Logic, Model, ModelBlockingAssignment,
    ModelBlockingClause, ModelBlockingClauseEvidence, ModelValue, NativeReplayArtifact,
    NativeReplayEvidenceManifest, NativeReplayMetadata, NativeReplaySolverIdentity,
    RawSmtProcessSolveProfileInput, RawSmtSolveProfileReason, RawSmtSolveProfileSource,
    RawSmtSolveProfileStatus, RawSmtSolveProfileSummary, RawSmtSolveProfileValidationIssue,
    RawSmtSolveProfileValidationReason, RawSmtSolveProfileValidationReport,
    RawSmtSolveProfileValidationStatus, SolveDecisionProfileModelConsumerDecision,
    SolveDecisionProfileModelConsumerReason, SolveDecisionProfileModelConsumerStatus,
    SolveDecisionProfileSummary, SolveDetails, SolveResult, SolverError, SolverScope, Sort, Term,
    TermId, TermKind, UnknownDiagnostic, VerificationLevel, VerificationSummary, VerifiedModel,
    VerifiedSolveResult, AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_REASON,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_REASON,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_STATUS, AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA,
    AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA_VERSION, AY_MODEL_BLOCKING_CLAUSE_SCHEMA,
    AY_MODEL_BLOCKING_CLAUSE_SCHEMA_VERSION, AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_CURRENT_REVISION,
    AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_REQUIRED_FIELDS, AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA,
    AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA_VERSION,
    AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA,
    AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA_VERSION,
    AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA, AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA_VERSION,
    NATIVE_REPLAY_EVIDENCE_MANIFEST_SCHEMA,
};
// Sort companion types — needed to construct Sort::BitVec, Sort::Array, Sort::Datatype
pub use ay_core::{ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort};
pub use ay_dpll::api::SortExt;
// Re-export structured types for API completeness
pub use ay_dpll::{CounterexampleStyle, StatValue, Statistics, UnknownReason};
// Re-export proof certificate types for UNSAT result consumers (#4521)
pub use ay_dpll::api::{
    FarkasCertificate, ProofAcceptanceError, ProofAcceptanceMode, ProofCheckError, ProofQuality,
    StrictProofVerdict, UnsatProofArtifact,
};
// Re-export the offline proof-bundle API (genuinely-external re-check).
pub use ay_dpll::api::{
    re_check_bundle_strict, render_term_canonical, BundleReCheck, SerializableProofBundle,
    PROOF_BUNDLE_SCHEMA,
};
pub use ay_proof::PartialProofCheck;
pub use capabilities::{
    all_sat_enumeration_symbolic_execution_contract,
    all_sat_enumeration_symbolic_execution_contract_key_value_pairs,
    incremental_assumptions_symbolic_execution_contract,
    incremental_assumptions_symbolic_execution_contract_key_value_pairs,
    model_blocking_symbolic_execution_contract,
    model_blocking_symbolic_execution_contract_key_value_pairs, solver_capability_descriptor,
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
    symbolic_execution_route_admission_decision_text_lines,
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
    validate_symbolic_execution_route_admission_decision_text_lines, SolverCapability,
    SolverCapabilityCode, SolverCapabilityContract, SolverCapabilityDescriptor,
    SolverCapabilityDescriptorManifest, SolverCapabilityReason, SolverCapabilityStatus,
    SymbolicExecutionCapabilityRouteReadiness, SymbolicExecutionCapabilityRouteReadinessReason,
    SymbolicExecutionCapabilityRouteReadinessStatus, SymbolicExecutionContractManifest,
    SymbolicExecutionContractManifestDiagnosticSummary, SymbolicExecutionContractManifestEntry,
    SymbolicExecutionContractManifestHealthDiagnostic,
    SymbolicExecutionContractManifestHealthIssue, SymbolicExecutionContractManifestHealthReason,
    SymbolicExecutionContractManifestHealthReport, SymbolicExecutionContractManifestHealthStatus,
    SymbolicExecutionDownstreamContractBundle, SymbolicExecutionDownstreamContractBundleReason,
    SymbolicExecutionDownstreamContractBundleStatus, SymbolicExecutionRouteAdmissionDecision,
    SymbolicExecutionRouteAdmissionReason, SymbolicExecutionRouteAdmissionStatus,
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
    AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES, AY_SOLVER_CAPABILITIES,
    AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA,
    AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA_VERSION,
    AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA, AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA_VERSION,
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
// Re-export Phase 5 explainability types (#8153) + Phase 6 incremental (#8154, #8306).
// [`Solver::unsat_core_with_farkas`](ay_dpll::api::Solver::unsat_core_with_farkas)
// is the dedicated entry point for consumers that need Farkas-annotated UNSAT
// cores (#8769); it returns the same
// [`AnnotatedUnsatCore`] re-exported here.
pub use ay_dpll::api::{
    AnnotatedCoreLiteral, AnnotatedUnsatCore, AssignmentReason, CongruenceReason, CongruenceStep,
    CoreConstraintExplanation, CoreEvolutionTracker, ExplanationKind, ExplanationReport,
    IncrementalCoreEvolution, ModelAssignmentExplanation, ModelProvenance, SatExplanation,
    SmtProofCertificate, TheoryAttribution, UnknownExplanation, UnsatCoreSource, UnsatExplanation,
    VariableProvenance,
};
// Re-export interpolation types (#8249)
pub use ay_dpll::api::{InterpolantResult, InterpolantStrength};

// Re-export frontend parsing for the common parse+solve path (#3039)
pub use ay_frontend::{parse, Command, Context, ParseError, ParsedConstant, ParsedSort};
// Re-export the reserved-symbol classifier so embedders can pre-screen symbol
// names BEFORE declaring them: a reserved builtin theory-operator name (e.g.
// `int2bv`, `bv2nat`) is rejected by the elaborator, and the panicking
// `declare_*` convenience wrappers turn that rejection into a crash inside the
// embedder's process. Embedders that
// build programs from untrusted/derived symbol vocabularies use this to fail
// closed (decline) instead.
pub use ay_frontend::is_reserved_symbol;
// Re-export SExpr for consumers that manipulate SMT-LIB ASTs (#5140).
pub use ay_frontend::SExpr;
// Re-export formula diagnostics for consumers that parse then analyze (#461)
pub use ay_frontend::{collect_formula_stats, FormulaStats};

/// Solution visualization helpers for recognized board-shaped models.
pub mod solution_visualization;
pub use solution_visualization::{render_solution_visualization, VisualizationFormat};

/// Low-level s-expression parsing for consumers that manipulate SMT-LIB
/// output at the AST level, including proof-rewriting integrations.
pub mod sexp {
    pub use ay_frontend::sexp::{parse_sexp, parse_sexps};
    pub use ay_frontend::SExpr;
}

/// AY version string (from Cargo.toml).
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

// Shared panic-boundary helpers for downstream consumers (#5140).
pub use ay_core::{catch_ay_panics, is_ay_panic_reason, panic_payload_to_string};

// Cached environment-flag helper macro for downstream consumers (#5140).
pub use ay_core::cached_env_flag;

// Re-export numeric types used in Model API return values (#5140).
// Without these, consumers must independently add num-rational and num-bigint.
pub use num_bigint::BigInt;
pub use num_rational::BigRational;

/// Unified error type for parse + solve operations.
///
/// Consumers that both parse SMT-LIB input and solve can use `ay::Error` as
/// a single error type covering both phases via `?` conversion:
///
/// ```no_run
/// fn run(input: &str) -> ay::Result<()> {
///     let _commands = ay::parse(input)?;
///     let mut solver = ay::Solver::try_new(ay::Logic::QfLia).unwrap();
///     // ... process commands ...
///     let details = solver.try_check_sat_with_details()?;
///     match details.accept_for_consumer() {
///         Ok(ay::SolveResult::Sat) => {
///             let _model = solver
///                 .model()
///                 .expect("accepted SAT result has model");
///         }
///         Ok(ay::SolveResult::Unsat(_)) => {}
///         Ok(ay::SolveResult::Unknown) | Err(_) => {}
///         Ok(_) => {}
///     }
///     Ok(())
/// }
/// ```
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    /// An error during SMT-LIB parsing.
    #[error(transparent)]
    Parse(#[from] ParseError),
    /// An error during solving.
    #[error(transparent)]
    Solve(#[from] SolverError),
}

/// Convenience alias for `std::result::Result<T, ay::Error>`.
pub type Result<T> = std::result::Result<T, Error>;

/// Canonical explicit-import Rust API for downstream consumers.
///
/// This module provides a single import path for all stable consumer-facing
/// types. Downstream crates should prefer `use ay::api::{...}` over reaching
/// into internal crates like `ay_dpll::api`.
///
/// # Example
///
/// ```no_run
/// use ay::api::{Logic, SolveResult, Solver, Sort};
///
/// let mut solver = Solver::try_new(Logic::QfLia).unwrap();
/// let x = solver.declare_const("x", Sort::Int);
/// let zero = solver.int_const(0);
/// let x_gt_zero = solver.gt(x, zero);
/// solver.assert_term(x_gt_zero);
/// assert!(solver.check_sat().is_sat());
/// ```
pub mod api {
    pub use crate::{
        raw_smt_solve_profile_summary_from_process,
        raw_smt_solve_profile_summary_from_typed_details,
        raw_smt_solve_profile_summary_from_typed_summary, split_leading_set_logic,
        validate_raw_smt_solve_profile_summary,
        validate_raw_smt_solve_profile_summary_key_value_rows,
        validate_raw_smt_solve_profile_summary_text_lines, AssumptionSolveDetails,
        ConsumerAcceptanceError, CounterexampleStyle, FpSpecialKind, FuncDecl, Logic, Model,
        ModelBlockingAssignment, ModelBlockingClause, ModelBlockingClauseEvidence, ModelValue,
        NativeReplayArtifact, NativeReplayEvidenceManifest, NativeReplayMetadata,
        NativeReplaySolverIdentity, RawSmtProcessSolveProfileInput, RawSmtSolveProfileReason,
        RawSmtSolveProfileSource, RawSmtSolveProfileStatus, RawSmtSolveProfileSummary,
        RawSmtSolveProfileValidationIssue, RawSmtSolveProfileValidationReason,
        RawSmtSolveProfileValidationReport, RawSmtSolveProfileValidationStatus,
        SolveDecisionProfileModelConsumerDecision, SolveDecisionProfileModelConsumerReason,
        SolveDecisionProfileModelConsumerStatus, SolveDecisionProfileSummary, SolveDetails,
        SolveResult, Solver, SolverConfig, SolverError, SolverScope, Sort, StatValue, Statistics,
        Term, TermId, TermKind, UnknownDiagnostic, UnknownReason, VerificationLevel,
        VerificationSummary, VerifiedModel, VerifiedSolveResult,
        AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_REASON,
        AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_ACCEPTED_STATUS,
        AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_REASON,
        AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_FAIL_CLOSED_STATUS,
        AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA, AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA_VERSION,
        AY_MODEL_BLOCKING_CLAUSE_SCHEMA, AY_MODEL_BLOCKING_CLAUSE_SCHEMA_VERSION,
        AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_CURRENT_REVISION,
        AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_REQUIRED_FIELDS, AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA,
        AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA_VERSION,
        AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA,
        AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA_VERSION,
        AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA, AY_SOLVE_DECISION_PROFILE_SUMMARY_SCHEMA_VERSION,
        NATIVE_REPLAY_EVIDENCE_MANIFEST_SCHEMA,
    };
    pub use ay_core::{ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort};
    pub use ay_dpll::api::SortExt;

    // Parser and error facade (#3039)
    pub use crate::{
        parse, Command, Context, Error, ParseError, ParsedConstant, ParsedSort, Result,
    };
    // Reserved-symbol pre-screen for embedders that build programs from
    // untrusted/derived symbol vocabularies (fail closed instead of crashing).
    pub use crate::is_reserved_symbol;
    // Offline proof-bundle API (genuinely-external re-check).
    pub use crate::{
        re_check_bundle_strict, render_term_canonical, BundleReCheck, SerializableProofBundle,
        PROOF_BUNDLE_SCHEMA,
    };

    // Numeric types from Model API return values (#5140)
    pub use crate::{BigInt, BigRational};

    // Proof certificate types for UNSAT consumers (#4521)
    pub use crate::{
        FarkasCertificate, PartialProofCheck, ProofAcceptanceError, ProofAcceptanceMode,
        ProofCheckError, ProofQuality, StrictProofVerdict, UnsatProofArtifact,
    };
    // Solver capability descriptor for downstream routing (#9701/#4445)
    pub use crate::{
        all_sat_enumeration_symbolic_execution_contract,
        all_sat_enumeration_symbolic_execution_contract_key_value_pairs,
        incremental_assumptions_symbolic_execution_contract,
        incremental_assumptions_symbolic_execution_contract_key_value_pairs,
        model_blocking_symbolic_execution_contract,
        model_blocking_symbolic_execution_contract_key_value_pairs, solver_capability_descriptor,
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
        symbolic_execution_capability_route_readiness_text_lines,
        symbolic_execution_contract_manifest,
        symbolic_execution_contract_manifest_diagnostic_summary,
        symbolic_execution_contract_manifest_diagnostic_summary_for_round_trip,
        symbolic_execution_contract_manifest_diagnostic_summary_json,
        symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows,
        symbolic_execution_contract_manifest_diagnostic_summary_text_lines,
        symbolic_execution_contract_manifest_health_diagnostic_lines,
        symbolic_execution_contract_manifest_health_key_value_rows,
        symbolic_execution_contract_manifest_health_report,
        symbolic_execution_contract_manifest_json,
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
        symbolic_execution_route_admission_decision_text_lines,
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
        validate_symbolic_execution_route_admission_decision_text_lines, SolverCapability,
        SolverCapabilityCode, SolverCapabilityContract, SolverCapabilityDescriptor,
        SolverCapabilityDescriptorManifest, SolverCapabilityReason, SolverCapabilityStatus,
        SymbolicExecutionCapabilityRouteReadiness, SymbolicExecutionCapabilityRouteReadinessReason,
        SymbolicExecutionCapabilityRouteReadinessStatus, SymbolicExecutionContractManifest,
        SymbolicExecutionContractManifestDiagnosticSummary, SymbolicExecutionContractManifestEntry,
        SymbolicExecutionContractManifestHealthDiagnostic,
        SymbolicExecutionContractManifestHealthIssue,
        SymbolicExecutionContractManifestHealthReason,
        SymbolicExecutionContractManifestHealthReport,
        SymbolicExecutionContractManifestHealthStatus, SymbolicExecutionDownstreamContractBundle,
        SymbolicExecutionDownstreamContractBundleReason,
        SymbolicExecutionDownstreamContractBundleStatus, SymbolicExecutionRouteAdmissionDecision,
        SymbolicExecutionRouteAdmissionReason, SymbolicExecutionRouteAdmissionStatus,
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
        AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_REJECTED_STATUS_CODES, AY_SOLVER_CAPABILITIES,
        AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA,
        AY_SOLVER_CAPABILITY_DESCRIPTOR_MANIFEST_SCHEMA_VERSION,
        AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA, AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA_VERSION,
        AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_HELPERS,
        AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA,
        AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_SCHEMA_VERSION,
        AY_SYMBOLIC_EXECUTION_CAPABILITY_ROUTE_READINESS_VALIDATORS,
        AY_SYMBOLIC_EXECUTION_CONTRACTS, AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_HELPERS,
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
        AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_HELPERS,
        AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA,
        AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA_VERSION,
        AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_VALIDATORS,
        AY_SYMBOLIC_EXECUTION_ROUTE_CURRENT_REVISION_KIND,
        AY_SYMBOLIC_EXECUTION_ROUTE_REQUIRED_CONTRACT_REVISION,
        AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER,
        AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_CRATE,
        AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_PATH_KIND,
    };
    // Phase 5 explainability types (#8153) + Phase 6 incremental (#8154, #8306)
    pub use crate::{
        AnnotatedCoreLiteral, AnnotatedUnsatCore, AssignmentReason, CongruenceReason,
        CongruenceStep, CoreConstraintExplanation, CoreEvolutionTracker, ExplanationKind,
        ExplanationReport, IncrementalCoreEvolution, ModelAssignmentExplanation, ModelProvenance,
        SatExplanation, SmtProofCertificate, TheoryAttribution, UnknownExplanation,
        UnsatCoreSource, UnsatExplanation, VariableProvenance,
    };
    // Farkas-annotated UNSAT core types (#8769)
    // Interpolation types (#8249)
    pub use crate::{InterpolantResult, InterpolantStrength};

    // Helper utilities for downstream consumers (#6589, #5140)
    pub use crate::cached_env_flag;
    pub use crate::{catch_ay_panics, is_ay_panic_reason, panic_payload_to_string, VERSION};

    // S-expression types for AST-level consumers (#5140)
    pub use crate::sexp::{parse_sexp, parse_sexps};
    pub use crate::SExpr;

    // Formula diagnostics for parse+analyze consumers (#461)
    pub use crate::{collect_formula_stats, FormulaStats};

    // Solution visualization helpers (#8702)
    pub use crate::{render_solution_visualization, VisualizationFormat};
}

/// Constrained Horn Clause (CHC) solver surface for downstream consumers.
///
/// This module exposes the consumer-facing CHC types from `ay_chc`. Callers
/// should prefer `use ay::chc::{...}` over reaching into `ay_chc` directly.
///
/// # Example
///
/// ```no_run
/// use ay::chc::{ChcProblem, PdrConfig, AdaptiveConfig, AdaptivePortfolio};
///
/// let problem = ChcProblem::new();
/// let config = AdaptiveConfig::default();
/// ```
///
/// # Type stability
///
/// Most types in this module are stable consumer types. However, `SmtContext`
/// and `SmtResult` are engine-internal types exposed for deep integrations
/// and may change between minor versions.
pub mod chc {

    pub use ay_chc::{
        // Core data model
        bmc_unsafe_trace_assignment_completeness,
        bmc_unsafe_trace_assignment_contract,
        // Lemma hint API
        canonical_var_for_pred_arg,
        canonical_var_name,
        canonical_vars_for_pred,
        engines,
        normalized_chc_input,
        normalized_chc_input_sha256,
        // Engine API
        AdaptiveConfig,
        AdaptivePortfolio,
        // BMC cross-check API (#8578)
        BmcConfig,
        BmcSolver,
        // Portfolio budget-control API (PortfolioConfig::engine_budget and friends)
        BudgetPolicy,
        BudgetReport,
        CancellationToken,
        CexVerificationResult,
        // Result types (verified envelope + inner types)
        ChcBmcUnsafeTraceAssignmentCompleteness,
        ChcBmcUnsafeTraceAssignmentCompletenessReason,
        ChcBmcUnsafeTraceAssignmentCompletenessStatus,
        ChcBmcUnsafeTraceAssignmentContract,
        ChcCheckedReplayArtifacts,
        ChcCheckedReplayManifestBinding,
        ChcCheckedReplayObligation,
        ChcCheckedReplaySummary,
        ChcCheckedReplaySummaryError,
        // DT problem construction
        ChcDtConstructor,
        ChcDtSelector,
        ChcEngineResult,
        ChcError,
        ChcExpr,
        ChcOp,
        ChcParser,
        ChcPdrProofRun,
        ChcProblem,
        // Progress reporting (#9000)
        ChcProgressReport,
        ChcProgressSnapshot,
        ChcProofArtifactDigest,
        ChcProofEvidenceManifest,
        ChcProofEvidenceOptions,
        ChcProofEvidenceParseError,
        ChcProofQueryAdmissionKey,
        ChcProofQueryCache,
        ChcProofQueryCacheAdmissionDecision,
        ChcProofQueryCacheAdmissionPolicy,
        ChcProofQueryCacheAdmissionStatus,
        ChcProofQueryCacheLookupKey,
        ChcProofQueryCacheLookupResult,
        ChcProofQueryCacheLookupStatus,
        ChcProofQueryCacheMetrics,
        ChcProofRunArtifact,
        ChcProofRunArtifactBundleValidationError,
        ChcProofRunArtifactBundleValidationErrorReason,
        ChcProofRunArtifactValidationError,
        ChcProofRunArtifactValidationErrorReason,
        ChcProofRunArtifacts,
        ChcProofSolverIdentity,
        ChcProofTranscriptConsumerEvidence,
        ChcProofTranscriptMetadata,
        ChcReplayCheckResult,
        ChcReplayCheckerIdentity,
        ChcReplayEvidence,
        ChcReplayObligation,
        ChcReplayObligationArtifact,
        ChcReplayObligationKind,
        ChcResult,
        ChcSort,
        ChcStatistics,
        ChcTraceAssignmentEvidence,
        ChcTraceStepEvidence,
        ChcUnsafeTraceEvidence,
        ChcVar,
        ClauseBody,
        ClauseHead,
        Counterexample,
        CounterexampleStep,
        EngineBudgetEntry,
        EngineConfig,
        EngineStopReason,
        EngineType,
        HintProviders,
        HintRequest,
        HintStage,
        HornClause,
        // Interpolation API (#8153)
        InterpolationResult,
        InvariantModel,
        LemmaHint,
        LemmaHintProvider,
        // MBP (model-based projection)
        Mbp,
        PdrConfig,
        PdrResult,
        PdrSolver,
        PortfolioConfig,
        PortfolioResult,
        PortfolioSolver,
        Predicate,
        PredicateId,
        PredicateInterpretation,
        // SMT context and model types
        SmtContext,
        SmtResult,
        SmtValue,
        UnsatCoreDiagnostics,
        VerifiedChcResult,
        VerifiedCounterexample,
        VerifiedInvariant,
        VerifiedUnknownMarker,
        VerifiedUnknownReason,
        CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_COMPLETENESS_SCHEMA,
        CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_CONTRACT_SCHEMA,
        CHC_EVIDENCE_MANIFEST_SCHEMA,
        CHC_PROOF_ARTIFACT_DIGEST_SCHEMA,
        CHC_PROOF_QUERY_ADMISSION_KEY_SCHEMA,
        CHC_PROOF_RUN_MODEL_ARTIFACT_ROLE,
        CHC_PROOF_RUN_MODEL_ARTIFACT_SCHEMA,
        CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_ROLE,
        CHC_PROOF_RUN_REPLAY_TRANSCRIPT_ARTIFACT_SCHEMA,
        CHC_PROOF_TRANSCRIPT_CONSUMER_EVIDENCE_SCHEMA,
        CHC_PROOF_TRANSCRIPT_SCHEMA,
        CHC_REPLAY_EVIDENCE_SCHEMA,
        NORMALIZED_CHC_INPUT_SCHEMA,
    };
}

/// Text-driven SMT-LIB executor surface.
///
/// `Executor` is the text-driven SMT-LIB path. It is a different abstraction
/// layer from `ay::api::Solver` (the typed solver-construction surface).
///
/// # Example
///
/// ```no_run
/// use ay::executor::Executor;
/// use ay::parse;
///
/// let commands = parse("(set-logic QF_LIA)\n(check-sat)").expect("valid input");
/// let mut exec = Executor::new();
/// let outputs = exec.execute_all(&commands).expect("execution succeeds");
/// ```
pub mod executor {
    pub use ay_core::{Proof, TermStore};
    pub use ay_dpll::{Executor, ExecutorError};
    pub use ay_frontend::Context;

    /// Convenience alias for `std::result::Result<T, ExecutorError>`.
    pub type Result<T> = std::result::Result<T, ExecutorError>;
}

/// Solution enumeration (ALL-SAT) surface for downstream consumers.
///
/// This module exposes the consumer-facing ALL-SAT types from `ay_allsat`.
/// Callers should prefer `use ay::allsat::{...}` over depending on `ay_allsat`
/// directly.
///
/// # Example
///
/// ```
/// use ay::allsat::{AllSatSolver, AllSatConfig};
///
/// let mut solver = AllSatSolver::new();
/// solver.add_clause(vec![1, 2]);
/// solver.add_clause(vec![-1, -2]);
/// let solutions: Vec<_> = solver.iter().collect();
/// assert_eq!(solutions.len(), 2);
/// ```
pub mod allsat {
    pub use ay_allsat::{
        AllSatConfig, AllSatIncomplete, AllSatInputError, AllSatIterator, AllSatOutcome,
        AllSatSolver, AllSatStats, EnumerationReport, Solution, SolutionIndexing,
        SolutionLiteralError,
    };
}

/// Stable public capability descriptor for downstream solver routing.
pub mod capabilities;

/// Proof internals for deep consumers that reconstruct or analyze proof certificates.
///
/// This module exposes the internal proof representation types from `ay_core`
/// and `ay_proof`. Proof reconstruction and translation callers should prefer
/// `use ay::proof_internals::{...}` over reaching into `ay_core` or `ay_proof`
/// directly.
///
/// # Stability
///
/// These types reflect internal proof representation and may change between
/// minor versions. Pin your ay dependency version if you use this module.
pub mod proof_internals {
    // Proof data structures from ay_core (#6742)
    pub use ay_core::{
        AletheRule, FarkasAnnotation, Proof, ProofId, ProofStep, Sort, TermData, TermId, TermStore,
        TheoryLemmaKind,
    };
    // Symbol formatting for proof output
    pub use ay_core::quote_symbol;
    // Proof checking and export from ay_proof.
    // #8821: `try_export_alethe` is the fallible variant; `AlethePrintError`
    // is the typed error it returns. Prefer these over the infallible
    // `export_alethe` when you need to refuse writing unverifiable proofs.
    pub use ay_proof::{
        check_proof_with_quality, export_alethe, export_alethe_with_problem_scope,
        try_export_alethe, try_export_alethe_with_problem_scope_and_overrides, AlethePrintError,
    };
}

/// **Proof emission — export surfaces for checking supported UNSAT paths.**
///
/// This is the landing point for AY's proof-producing paths. A successful
/// trust-free export lets a caller validate an UNSAT result with a separate
/// proof checker instead of relying solely on AY. Availability and checker
/// support depend on the selected solver path, theory, and format; an UNSAT
/// result is certified only when its artifact contains no trusted steps and
/// passes the intended checker.
///
/// ## What ay emits
///
/// | Layer | Format | Entry point |
/// |-------|--------|-------------|
/// | Supported SMT UNSAT paths | **Alethe** | [`emit_unsat_proof`](proof_emission::emit_unsat_proof) = [`ay_proof::try_export_alethe`] |
/// | Supported SMT UNSAT paths (problem-scoped declarations) | **Alethe** | [`ay_proof::try_export_alethe_with_problem_scope_and_overrides`] |
/// | Propositional UNSAT | **DRAT / LRAT** | emitted by the SAT engine; re-checkable via `ay check` |
/// | Bitvector refutation | **versioned bit-blast export** (`FORMAT_VERSION`) | [`ay_proof::export_bv_blast_proof`] |
/// | Lean rendering (BV) | **Lean** | [`ay_proof::render_bv_blast_proof_lean`] |
///
/// Runtime `--features` JSON reports the compiled proof-renderer inventory
/// under `proof_theories`; it is not a coverage claim. Treat a zero-`trust_count`
/// quality result, successful export, and the external checker verdict as the
/// authority for a particular run.
///
/// ## How a caller triggers it
///
/// - **CLI:** `ay solve --proof out.alethe FILE.smt2` (format inferred from
///   the extension, or forced with `--proof-format alethe|drat|lrat|lean4`).
///   For DIMACS CNF, a DRAT proof is written to `<input>.drat` by default on
///   UNSAT (opt out with `--no-proof`). `--strict-proofs` / `--self-check`
///   force internal proof production even without `--proof`.
/// - **SMT-LIB:** `(set-option :produce-proofs true)` then `(get-proof)`.
/// - **Library:** call [`emit_unsat_proof`](proof_emission::emit_unsat_proof)
///   (or the scoped/override variants) with the [`proof_internals::Proof`] and
///   [`proof_internals::TermStore`].
///
/// ## Failing closed on unrenderable steps
///
/// A step that cannot be rendered as a *checkable* Alethe rule is **not**
/// silently downgraded to `:rule trust`.
/// [`emit_unsat_proof`](proof_emission::emit_unsat_proof) returns a typed
/// [`AlethePrintError`](proof_emission::AlethePrintError); the infallible
/// [`ay_proof::export_alethe`] emits an explicit
/// `(error "UNVERIFIABLE PROOF: ...")` document rather than a certificate
/// (#8821). Callers must treat that document as an export failure. Proof
/// "quality" (residual `trust_count`) is reported by
/// [`ay_proof::check_proof_with_quality`], and `--strict-proofs` downgrades any
/// UNSAT whose empty-clause derivation rides a trust step to a sound `unknown`
/// (terminal-trust check, #8759). The low-level exporter preserves proof steps
/// that are explicitly marked `:rule trust`; export success alone is therefore
/// not a certification claim.
///
/// ## Why emit a proof artifact?
///
/// A caller can bind a trust-free artifact to the original problem, archive it,
/// and validate it with a checker that is separate from AY. That makes the
/// evidence portable and independently reviewable; it does not certify solver
/// paths that did not emit and pass such a check.
pub mod proof_emission {
    #[doc(inline)]
    pub use ay_proof::{
        check_proof_with_quality, export_alethe, export_alethe_with_problem_scope,
        export_bv_blast_proof, render_bv_blast_proof_lean, try_export_alethe,
        try_export_alethe_with_problem_scope_and_overrides, AlethePrintError, ProofQuality,
        BV_BLAST_FORMAT_VERSION,
    };

    /// Export an Alethe UNSAT proof, returning an error for steps that cannot be
    /// rendered.
    ///
    /// This is the canonical, clearly-named entry point for proof emission and
    /// is a thin alias for [`ay_proof::try_export_alethe`]. It returns the
    /// Alethe proof text on success, or a typed [`AlethePrintError`] when a
    /// step cannot be rendered. Explicitly marked `:rule trust` steps are
    /// preserved; use [`check_proof_with_quality`] or the CLI's
    /// `--strict-proofs` mode when a trust-free artifact is required.
    ///
    /// # Errors
    ///
    /// Returns [`AlethePrintError`] when any step cannot be rendered as a
    /// checkable Alethe rule.
    pub fn emit_unsat_proof(
        proof: &ay_core::Proof,
        terms: &ay_core::TermStore,
    ) -> Result<String, AlethePrintError> {
        try_export_alethe(proof, terms)
    }
}

/// Formula translation surface for consumers that transform ay terms into
/// external representations (Lean expressions, other solver formats, etc.).
///
/// This module exposes the translation framework from `ay_translate`.
/// Callers should prefer `use ay::translate::{...}` over depending on
/// `ay_translate` directly.
///
/// # Stability
///
/// These types reflect internal term representation and may change between
/// minor versions. Pin your ay dependency version if you use this module.
pub mod translate {
    pub use ay_translate::{
        SortTranslator, TermTranslator, TranslationContext, TranslationSession, TranslationState,
        TranslationTermHost,
    };
    /// Theory-specific operation translators.
    pub mod ops {
        pub use ay_translate::ops::*;
    }
}

/// Prelude module for convenient glob imports.
///
/// # Example
///
/// ```no_run
/// use ay::prelude::*;
///
/// let mut solver = Solver::try_new(Logic::QfLia).unwrap();
/// let x = solver.declare_const("x", Sort::Int);
/// let zero = solver.int_const(0);
/// let x_gt_zero = solver.gt(x, zero);
/// solver.assert_term(x_gt_zero);
/// assert!(solver.check_sat().is_sat());
/// ```
pub mod prelude {
    // Core solver types
    pub use crate::{
        all_sat_enumeration_symbolic_execution_contract,
        all_sat_enumeration_symbolic_execution_contract_key_value_pairs,
        incremental_assumptions_symbolic_execution_contract,
        incremental_assumptions_symbolic_execution_contract_key_value_pairs,
        model_blocking_symbolic_execution_contract,
        model_blocking_symbolic_execution_contract_key_value_pairs, solver_capability_descriptor,
        solver_capability_descriptor_key_value_pairs, solver_capability_descriptor_manifest,
        symbolic_execution_all_supported_capability_route_readiness,
        symbolic_execution_all_supported_capability_route_readiness_for_decision,
        symbolic_execution_all_supported_capability_route_readiness_key_value_rows,
        symbolic_execution_all_supported_capability_route_readiness_text_lines,
        symbolic_execution_capability_route_readiness,
        symbolic_execution_capability_route_readiness_for_decision,
        symbolic_execution_capability_route_readiness_key_value_rows,
        symbolic_execution_capability_route_readiness_text_lines,
        symbolic_execution_contract_manifest,
        symbolic_execution_contract_manifest_diagnostic_summary,
        symbolic_execution_contract_manifest_diagnostic_summary_for_round_trip,
        symbolic_execution_contract_manifest_diagnostic_summary_key_value_rows,
        symbolic_execution_contract_manifest_diagnostic_summary_text_lines,
        symbolic_execution_contract_manifest_health_diagnostic_lines,
        symbolic_execution_contract_manifest_health_key_value_rows,
        symbolic_execution_contract_manifest_health_report,
        symbolic_execution_contract_manifest_key_value_pairs,
        symbolic_execution_contract_manifest_round_trip_health_report,
        symbolic_execution_downstream_contract_bundle,
        symbolic_execution_downstream_contract_bundle_key_value_rows,
        symbolic_execution_downstream_contract_bundle_text_lines,
        symbolic_execution_route_admission_decision,
        symbolic_execution_route_admission_decision_for_summary,
        symbolic_execution_route_admission_decision_key_value_rows,
        symbolic_execution_route_admission_decision_text_lines,
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
        validate_symbolic_execution_route_admission_decision_text_lines, SolverCapability,
        SolverCapabilityCode, SolverCapabilityContract, SolverCapabilityDescriptor,
        SolverCapabilityDescriptorManifest, SolverCapabilityReason, SolverCapabilityStatus,
        SymbolicExecutionCapabilityRouteReadiness, SymbolicExecutionCapabilityRouteReadinessReason,
        SymbolicExecutionCapabilityRouteReadinessStatus, SymbolicExecutionContractManifest,
        SymbolicExecutionContractManifestDiagnosticSummary, SymbolicExecutionContractManifestEntry,
        SymbolicExecutionContractManifestHealthDiagnostic,
        SymbolicExecutionContractManifestHealthReport, SymbolicExecutionDownstreamContractBundle,
        SymbolicExecutionDownstreamContractBundleReason,
        SymbolicExecutionDownstreamContractBundleStatus, SymbolicExecutionRouteAdmissionDecision,
        SymbolicExecutionRouteAdmissionReason, SymbolicExecutionRouteAdmissionStatus,
        AY_ALL_SAT_ENUMERATION_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
        AY_INCREMENTAL_ASSUMPTIONS_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
        AY_MODEL_BLOCKING_SYMBOLIC_EXECUTION_CONTRACT_SCHEMA,
        AY_SYMBOLIC_EXECUTION_CONTRACT_DIAGNOSTIC_SUMMARY_SCHEMA,
        AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_HEALTH_SCHEMA,
        AY_SYMBOLIC_EXECUTION_CONTRACT_MANIFEST_SCHEMA,
        AY_SYMBOLIC_EXECUTION_DOWNSTREAM_CONTRACT_BUNDLE_SCHEMA,
        AY_SYMBOLIC_EXECUTION_ROUTE_ADMISSION_SCHEMA,
        AY_SYMBOLIC_EXECUTION_ROUTE_CURRENT_REVISION_KIND,
        AY_SYMBOLIC_EXECUTION_ROUTE_REQUIRED_CONTRACT_REVISION,
        AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER,
        AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_CRATE,
        AY_SYMBOLIC_EXECUTION_ROUTE_SELECTED_SOLVER_PATH_KIND,
    };
    pub use crate::{
        raw_smt_solve_profile_summary_from_process,
        raw_smt_solve_profile_summary_from_typed_details,
        raw_smt_solve_profile_summary_from_typed_summary, validate_raw_smt_solve_profile_summary,
        validate_raw_smt_solve_profile_summary_key_value_rows,
        validate_raw_smt_solve_profile_summary_text_lines, AssumptionSolveDetails,
        CounterexampleStyle, FpSpecialKind, Logic, Model, ModelBlockingAssignment,
        ModelBlockingClause, ModelBlockingClauseEvidence, ModelValue,
        RawSmtProcessSolveProfileInput, RawSmtSolveProfileReason, RawSmtSolveProfileSource,
        RawSmtSolveProfileStatus, RawSmtSolveProfileSummary, RawSmtSolveProfileValidationIssue,
        RawSmtSolveProfileValidationReason, RawSmtSolveProfileValidationReport,
        RawSmtSolveProfileValidationStatus, SolveDecisionProfileModelConsumerDecision,
        SolveDecisionProfileModelConsumerReason, SolveDecisionProfileModelConsumerStatus,
        SolveDecisionProfileSummary, SolveDetails, SolveResult, Solver, SolverConfig, SolverError,
        SolverScope, Sort, StatValue, Statistics, Term, TermId, TermKind, UnknownDiagnostic,
        UnknownReason, VerificationLevel, VerificationSummary, VerifiedModel, VerifiedSolveResult,
        AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_CURRENT_REVISION,
        AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_REQUIRED_FIELDS, AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA,
        AY_RAW_SMT_SOLVE_PROFILE_SUMMARY_SCHEMA_VERSION,
    };

    // API types for declare_fun() → apply() pattern (#2080)
    pub use crate::FuncDecl;
    pub use ay_dpll::api::SortExt;

    // Datatype types for datatype declarations (#2080)
    pub use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort};

    // Array and bitvector sort constructors (#2080)
    pub use ay_core::{ArraySort, BitVecSort};

    // Frontend parsing and error facade (#3039)
    pub use crate::{parse, Command, Error, ParseError, ParsedConstant, ParsedSort, Result};

    // Numeric types from Model API return values (#5140)
    pub use crate::{BigInt, BigRational};

    // Proof certificate types for UNSAT consumers (#4521)
    pub use crate::{
        FarkasCertificate, PartialProofCheck, ProofAcceptanceError, ProofAcceptanceMode,
        ProofCheckError, ProofQuality, StrictProofVerdict, UnsatProofArtifact,
    };
    // Phase 5 explainability types (#8153) + Phase 6 incremental (#8154, #8306)
    pub use crate::{
        AnnotatedCoreLiteral, AnnotatedUnsatCore, AssignmentReason, CongruenceReason,
        CongruenceStep, CoreConstraintExplanation, CoreEvolutionTracker, ExplanationKind,
        ExplanationReport, IncrementalCoreEvolution, ModelAssignmentExplanation, ModelProvenance,
        SatExplanation, SmtProofCertificate, TheoryAttribution, UnknownExplanation,
        UnsatCoreSource, UnsatExplanation, VariableProvenance,
    };
    // Farkas-annotated UNSAT core types (#8769)
    // Interpolation types (#8249)
    pub use crate::{InterpolantResult, InterpolantStrength};

    // Helper utilities for downstream consumers (#6589, #5140)
    pub use crate::cached_env_flag;
    pub use crate::{catch_ay_panics, is_ay_panic_reason, panic_payload_to_string, VERSION};

    // S-expression types for AST-level consumers (#5140)
    pub use crate::sexp::{parse_sexp, parse_sexps};
    pub use crate::SExpr;

    // Formula diagnostics for parse+analyze consumers (#461)
    pub use crate::{collect_formula_stats, FormulaStats};

    // Solution visualization helpers (#8702)
    pub use crate::{render_solution_visualization, VisualizationFormat};
}

#[cfg(test)]
#[path = "facade_reexport_tests.rs"]
mod facade_reexport_tests;

#[cfg(test)]
#[path = "proof_facade_tests.rs"]
mod proof_facade_tests;
