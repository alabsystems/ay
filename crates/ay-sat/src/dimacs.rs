// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DIMACS CNF parser
//!
//! Parses the standard DIMACS CNF format used in SAT competitions.
//! Delegates tokenization to [`crate::dimacs_core`] and converts raw
//! i32 literals to 0-indexed [`Literal`]/[`Variable`] values.

use crate::circuit_equiv_packet::{
    circuit_multiplier22_original_dimacs_sat_model_authority_decision,
    CircuitEquivOriginalDimacsSatModelAuthorityDecision, CircuitEquivPacket,
    CircuitEquivPacketCounters, CircuitEquivRouteAdmissionStatus,
};
use crate::circuit_scout::{
    produce_original_dimacs_sat_model_authority_packet, scout_formula,
    CircuitOriginalDimacsSatModelAuthorityPacket,
    CircuitOriginalDimacsSatModelAuthorityProductionError,
    CircuitOriginalDimacsSatModelAuthorityStatus, CircuitScoutRejection, CircuitSourceFrameRow,
};
use crate::dimacs_core::{self, DimacsCoreError, DimacsEvent, DimacsRecordRef};
use crate::literal::{Literal, Variable};
use crate::solver::Solver;
use crate::{SolverVariant, VariantInput, VariantProfilePlan};
use std::fs;
use std::io::{ErrorKind, Read};
use std::path::{Path, PathBuf};

const CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV: &str =
    "AY_SAT_CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ROUTE";
const CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_FORMULA_ENV: &str =
    "AY_SAT_CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_FORMULA";
const CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_STDOUT_ENV: &str =
    "AY_SAT_CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_STDOUT";
const CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_ARTIFACT_ENV: &str =
    "AY_SAT_CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_ARTIFACT";
const CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_COMMAND_ENV: &str =
    "AY_SAT_CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_COMMAND_JSON";
const CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_EXIT_STATUS_ENV: &str =
    "AY_SAT_CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_EXIT_STATUS";
const CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECK_SCHEMA: &str =
    "ay.satcomp-model-check/v1";
const MULTIPLIER_EQUIVALENCE_CONSERVATION_DIAGNOSTIC_SCHEMA_VERSION: u32 = 1;
const MULTIPLIER_EQUIVALENCE_TARGET_ISSUE: u32 = 9725;
const MULTIPLIER_EQUIVALENCE_LEAN_ADMISSION_ISSUE: u32 = 9733;
const MULTIPLIER_EQUIVALENCE_LEAN_CONSERVATION_ISSUE: u32 = 9736;
const MULTIPLIER_EQUIVALENCE_OFFICIAL_ROW_COUNT: u32 = 12;
const MULTIPLIER_EQUIVALENCE_MIN_OFFICIAL_VARS: usize = 2540;
const MULTIPLIER_EQUIVALENCE_MAX_OFFICIAL_VARS: usize = 3327;
const MULTIPLIER_EQUIVALENCE_MIN_OFFICIAL_CLAUSES: usize = 8495;
const MULTIPLIER_EQUIVALENCE_MAX_OFFICIAL_CLAUSES: usize = 10653;
const MULTIPLIER_EQUIVALENCE_BLOCKER_NONE: u64 = 0;
const MULTIPLIER_EQUIVALENCE_BLOCKER_NON_TARGET_SHAPE: u64 = 10;
const MULTIPLIER_EQUIVALENCE_BLOCKER_STRUCTURAL_REJECTION: u64 = 20;
const MULTIPLIER_EQUIVALENCE_BLOCKER_SOURCE_CLAUSE_BINDINGS_MISSING: u64 = 30;
const MULTIPLIER_EQUIVALENCE_BLOCKER_PROOF_REPLAY_MISSING: u64 = 40;

/// Error type for DIMACS parsing
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DimacsError {
    /// Missing problem line (p cnf ...)
    MissingProblemLine,
    /// Invalid problem line format
    InvalidProblemLine {
        /// The invalid line content.
        line_content: String,
        /// 1-based line number (0 if unknown).
        line_number: usize,
    },
    /// More than one `p cnf` problem line appeared.
    DuplicateProblemLine {
        /// 1-based line number of the repeated problem line.
        line_number: usize,
    },
    /// Invalid literal in clause
    InvalidLiteral {
        /// The invalid token.
        token: String,
        /// 1-based line number (0 if unknown).
        line_number: usize,
    },
    /// I/O error description
    IoError(String),
    /// More clauses than declared
    TooManyClauses {
        /// Expected number of clauses
        expected: usize,
        /// Actual number of clauses
        got: usize,
    },
    /// Literal variable exceeds declared variable count
    VariableOutOfRange {
        /// The variable that was out of range
        var: u32,
        /// Maximum allowed variable
        max: u32,
        /// 1-based line number (0 if unknown).
        line_number: usize,
    },
    /// A `p cnf` header declared an implausibly large count, which would drive
    /// an unbounded pre-allocation (OOM). Rejected before any per-variable
    /// allocation is attempted.
    HeaderCountTooLarge {
        /// Which count: `"variables"` or `"clauses"`.
        what: &'static str,
        /// The declared value from the header.
        declared: usize,
        /// The maximum accepted value.
        max: usize,
    },
    /// A tagged line (e.g. a QDIMACS quantifier prefix `a`/`e`) appeared in
    /// input consumed as plain CNF, which does not support tagged lines.
    UnsupportedTaggedLine {
        /// The tag character that introduced the line (e.g. 'a', 'e').
        tag: char,
    },
}

impl std::fmt::Display for DimacsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingProblemLine => {
                write!(
                    f,
                    "missing problem line, expected \"p cnf <num_vars> <num_clauses>\""
                )
            }
            Self::InvalidProblemLine {
                line_content,
                line_number,
            } if *line_number > 0 => {
                write!(f, "line {line_number}: invalid problem line: {line_content} (expected \"p cnf <num_vars> <num_clauses>\")")
            }
            Self::InvalidProblemLine { line_content, .. } => {
                write!(f, "invalid problem line: {line_content} (expected \"p cnf <num_vars> <num_clauses>\")")
            }
            Self::DuplicateProblemLine { line_number } => {
                write!(f, "line {line_number}: duplicate problem line")
            }
            Self::InvalidLiteral { token, line_number } if *line_number > 0 => {
                write!(
                    f,
                    "line {line_number}: invalid literal \"{token}\", expected integer"
                )
            }
            Self::InvalidLiteral { token, .. } => {
                write!(f, "invalid literal \"{token}\", expected integer")
            }
            Self::IoError(s) => write!(f, "I/O error: {s}"),
            Self::TooManyClauses { expected, got } => {
                write!(f, "too many clauses: expected {expected}, got {got}")
            }
            Self::VariableOutOfRange {
                var,
                max,
                line_number,
            } if *line_number > 0 => {
                write!(f, "line {line_number}: variable {var} out of range (declared max {max} in header)")
            }
            Self::VariableOutOfRange { var, max, .. } => {
                write!(
                    f,
                    "variable {var} out of range (declared max {max} in header)"
                )
            }
            Self::HeaderCountTooLarge {
                what,
                declared,
                max,
            } => {
                write!(
                    f,
                    "declared {what} count {declared} exceeds the maximum supported {max}; \
                     refusing to allocate (possible malformed/adversarial header)"
                )
            }
            Self::UnsupportedTaggedLine { tag } => {
                write!(
                    f,
                    "tagged line '{tag}' is not valid CNF (QDIMACS or WCNF input? \
                     use `ay qbf solve FILE` / `ay maxsat solve FILE`)"
                )
            }
        }
    }
}

impl std::error::Error for DimacsError {}

impl From<DimacsCoreError> for DimacsError {
    fn from(e: DimacsCoreError) -> Self {
        match e {
            DimacsCoreError::MissingHeader => Self::MissingProblemLine,
            DimacsCoreError::InvalidHeader {
                line_content,
                line_number,
            } => Self::InvalidProblemLine {
                line_content,
                line_number,
            },
            DimacsCoreError::DuplicateHeader { line_number } => {
                Self::DuplicateProblemLine { line_number }
            }
            DimacsCoreError::InvalidLiteral { token, line_number } => {
                Self::InvalidLiteral { token, line_number }
            }
            DimacsCoreError::IoError(s) => Self::IoError(s),
            DimacsCoreError::VariableOutOfRange {
                var,
                max,
                line_number,
            } => Self::VariableOutOfRange {
                var,
                max,
                line_number,
            },
            DimacsCoreError::HeaderCountTooLarge {
                what,
                declared,
                max,
            } => Self::HeaderCountTooLarge {
                what,
                declared,
                max,
            },
            DimacsCoreError::UnsupportedTaggedLine { tag } => Self::UnsupportedTaggedLine { tag },
        }
    }
}

/// Result of parsing a DIMACS file
#[derive(Debug)]
pub struct DimacsFormula {
    /// Number of variables
    pub num_vars: usize,
    /// Number of clauses (declared)
    pub num_clauses: usize,
    /// The clauses
    pub clauses: Vec<Vec<Literal>>,
}

/// Fail-closed multiplier-equivalence weighted-conservation diagnostic.
///
/// This is a bridge from the Lean 4 contracts in #9733/#9736 into AY runtime
/// evidence. It is intentionally diagnostic-only: all authority fields stay
/// false until a future original-DIMACS proof materializer and external checker
/// bind the certificate to a valid LRAT/LPR artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultiplierEquivalenceConservationDiagnostic {
    /// Stable diagnostic schema version.
    pub schema_version: u32,
    /// Parent SAT-COMP lane issue.
    pub target_issue: u32,
    /// Lean 4 admission contract issue.
    pub lean_admission_contract_issue: u32,
    /// Lean 4 weighted-conservation contract issue.
    pub lean_conservation_contract_issue: u32,
    /// Official multiplier-equivalence row count tracked by #9725.
    pub official_row_count: u32,
    /// DIMACS header variable count.
    pub num_vars: usize,
    /// DIMACS header clause count.
    pub num_clauses: usize,
    /// Header shape is inside the official #9725 row envelope.
    pub official_shape_candidate: bool,
    /// Existing circuit scout found multiplier-like structure.
    pub structural_candidate: bool,
    /// This row is useful as a diagnostic candidate, but not as authority.
    pub diagnostic_candidate: bool,
    /// The bridge is intentionally fail-closed.
    pub fail_closed: bool,
    /// Result-producing route admission. Always false in this scaffold.
    pub route_admitted: bool,
    /// SAT/UNSAT result authority. Always false in this scaffold.
    pub result_authority: bool,
    /// Proof-output authority. Always false in this scaffold.
    pub proof_output_authority: bool,
    /// Whether an original-DIMACS proof replay has been checked.
    pub proof_replay_checked: bool,
    /// Whether an external checker has verified the proof artifact.
    pub external_checker_verified: bool,
    /// Whether a proof artifact is present for the original DIMACS row.
    pub proof_artifact_present: bool,
    /// Recovered AND-gate count copied from the circuit scout.
    pub gate_and: u64,
    /// Recovered XOR-gate count copied from the circuit scout.
    pub gate_xor: u64,
    /// Recovered total gate count copied from the circuit scout.
    pub gates_total: u64,
    /// Partial-product-like AND rows recovered by the scout.
    pub partial_product_rows: u64,
    /// Half/full-adder rows recovered by the scout.
    pub compressor_layer_rows: u64,
    /// Weighted-conservation obligations implied by recovered rows.
    pub weighted_conservation_obligation_rows: u64,
    /// Source-clause-bound conservation rows accepted by this scaffold.
    pub source_clause_bound_rows: u64,
    /// Conservation rows still missing original-clause bindings.
    pub source_clause_bindings_missing: u64,
    /// Recovered gate defining-clause references inspected by the source sidecar.
    pub source_gate_clause_references: u64,
    /// Gate defining-clause references bound back to exact original DIMACS rows.
    pub source_gate_clause_bound_references: u64,
    /// Gate defining-clause references missing sidecar bindings.
    pub source_gate_clause_binding_missing_references: u64,
    /// Duplicate gate defining-clause references rejected by the sidecar.
    pub source_gate_clause_duplicate_references: u64,
    /// Gate defining-clause references mapped outside the original DIMACS rows.
    pub source_gate_clause_out_of_range_references: u64,
    /// Gate defining-clause references whose arena literals drifted from source.
    pub source_gate_clause_literal_mismatch_references: u64,
    /// Common-product witness rows accepted by this scaffold.
    pub common_product_witness_rows: u64,
    /// Miter disequality rows accepted by this scaffold.
    pub miter_disequality_rows: u64,
    /// Stable blocker code for audit/matrix ingestion.
    pub route_blocker_code: u64,
    /// Stable circuit-scout rejection code.
    pub scout_rejection_code: u64,
}

impl DimacsFormula {
    /// Create a solver from this formula.
    ///
    /// Uses the conservative DIMACS default profile.
    ///
    /// BVE, congruence, and decompose remain opt-in until their model
    /// reconstruction paths are safe on structured SAT instances. Subsumption
    /// remains enabled (#4872): CaDiCaL-style one-watch forward subsumption
    /// replaces the 150x-slower backward engine. Factorization stays enabled:
    /// it no longer records reconstruction entries and is safe by default.
    pub fn into_solver(self) -> Solver {
        self.into_solver_with_variant(SolverVariant::Default)
    }

    /// Create a solver using a named SAT-COMP variant preset.
    ///
    /// Applies feature-driven adaptive adjustments after the variant preset.
    /// See [`crate::adaptive::adjust_features_for_instance`] for the threshold
    /// rules applied.
    pub fn into_solver_with_variant(self, variant: SolverVariant) -> Solver {
        self.into_solver_with_variant_routed(variant, false)
    }

    /// Like [`Self::into_solver_with_variant`], but when `allow_auto_route` is
    /// set an unspecified Default preset may be auto-routed to Probe or
    /// Aggressive for binary-dominant mid-size formulas (see
    /// [`SolverVariant::auto_route`]). The CLI passes `true` only when no
    /// explicit `--sat-variant` was requested; library callers pass `false`.
    pub fn into_solver_with_variant_routed(
        self,
        variant: SolverVariant,
        allow_auto_route: bool,
    ) -> Solver {
        self.into_solver_with_variant_routed_source(
            variant,
            allow_auto_route,
            crate::auto::DecisionSource::Default,
        )
    }

    /// Like [`Self::into_solver_with_variant_routed`], with truthful provenance
    /// for the frontend's requested variant. An actual formula-driven reroute
    /// supersedes this source with `Auto`.
    pub fn into_solver_with_variant_routed_source(
        self,
        variant: SolverVariant,
        allow_auto_route: bool,
        requested_source: crate::auto::DecisionSource,
    ) -> Solver {
        // Content-driven sizing: allocate the solver for the variables that
        // ACTUALLY appear, not the (untrusted) declared header count, so an
        // over-declared `p cnf 4000000000 1` with three real variables is solved
        // as a 3-variable instance instead of OOMing. `self.num_vars`/`num_clauses`
        // remain declared metadata (callers such as model counting need the
        // declared count); only the solver's dense allocation tracks real content.
        let solver_vars = max_variable_count(&self.clauses);
        let mut solver = Solver::new(solver_vars);
        // A DIMACS formula becomes a ONE-SHOT solve: no assumptions, no
        // incremental reuse. That licenses structural symmetry breaking
        // (orbitopal fixing, the aux-free PHP refutation), which removes models
        // and would be unsound under assumptions. Embedders that build a Solver
        // directly never take this path, so they stay safe by default.
        solver.set_symmetry_oneshot(true);

        // Extract features first so an in-band Default input can be auto-routed
        // to Probe or Aggressive before the config is resolved (the same
        // features then drive the adaptive adjustments below).
        let features = crate::features::SatFeatures::extract(solver_vars, &self.clauses);
        let (variant, variant_source) = if allow_auto_route {
            variant.auto_route_with_source(&features, requested_source)
        } else {
            (variant, requested_source)
        };
        let config = variant.config(VariantInput::new(
            solver_vars,
            self.num_clauses,
            false,
            false,
        ));

        // Apply adaptive adjustments before applying the config to the solver.
        // This allows instance-specific overrides to take effect during the
        // initial variant application. Reorder is now part of
        // InprocessingFeatureProfile (#8149), so adjust_features_for_instance
        // handles it without a separate call.
        let plan =
            VariantProfilePlan::from_config_features_with_source(config, &features, variant_source);
        // Apply via the PLAN, not plan.config alone: the plan also carries the
        // capability ledger (B0), and applying the bare config would silently
        // drop it -- the same partial-application slip that kept
        // set_symmetry_oneshot off this path in §28.4.
        plan.apply_to_solver(&mut solver);

        for clause in self.clauses {
            solver.add_clause(clause);
        }
        solver
    }

    /// Build a diagnostic-only #9725 weighted-conservation certificate summary.
    #[must_use]
    pub fn multiplier_equivalence_conservation_diagnostic(
        &self,
    ) -> MultiplierEquivalenceConservationDiagnostic {
        let scout = scout_formula(self.num_vars, &self.clauses);
        let official_shape_candidate = self.num_vars >= MULTIPLIER_EQUIVALENCE_MIN_OFFICIAL_VARS
            && self.num_vars <= MULTIPLIER_EQUIVALENCE_MAX_OFFICIAL_VARS
            && self.num_clauses >= MULTIPLIER_EQUIVALENCE_MIN_OFFICIAL_CLAUSES
            && self.num_clauses <= MULTIPLIER_EQUIVALENCE_MAX_OFFICIAL_CLAUSES;
        let structural_candidate = scout.route_candidate;
        let diagnostic_candidate = official_shape_candidate && structural_candidate;
        let compressor_layer_rows = scout.half_adders + scout.full_adders;
        let weighted_conservation_obligation_rows =
            scout.partial_product_ands + compressor_layer_rows;
        let source_gate_clause_references = scout.source_clause_binding.gate_clause_references;
        let source_gate_clause_bound_references =
            scout.source_clause_binding.source_clause_bound_rows;
        let source_gate_clause_binding_missing_references = scout
            .source_clause_binding
            .source_clause_binding_missing_rows;
        let source_gate_clause_duplicate_references = scout
            .source_clause_binding
            .duplicate_gate_clause_reference_rows;
        let source_gate_clause_out_of_range_references =
            scout.source_clause_binding.source_clause_out_of_range_rows;
        let source_gate_clause_literal_mismatch_references = scout
            .source_clause_binding
            .source_clause_literal_mismatch_rows;
        let source_clause_bound_rows = 0;
        let source_clause_bindings_missing =
            weighted_conservation_obligation_rows.saturating_sub(source_clause_bound_rows);
        let route_blocker_code = if !official_shape_candidate {
            MULTIPLIER_EQUIVALENCE_BLOCKER_NON_TARGET_SHAPE
        } else if !structural_candidate {
            MULTIPLIER_EQUIVALENCE_BLOCKER_STRUCTURAL_REJECTION
        } else if source_clause_bindings_missing > 0 {
            MULTIPLIER_EQUIVALENCE_BLOCKER_SOURCE_CLAUSE_BINDINGS_MISSING
        } else {
            MULTIPLIER_EQUIVALENCE_BLOCKER_PROOF_REPLAY_MISSING
        };

        MultiplierEquivalenceConservationDiagnostic {
            schema_version: MULTIPLIER_EQUIVALENCE_CONSERVATION_DIAGNOSTIC_SCHEMA_VERSION,
            target_issue: MULTIPLIER_EQUIVALENCE_TARGET_ISSUE,
            lean_admission_contract_issue: MULTIPLIER_EQUIVALENCE_LEAN_ADMISSION_ISSUE,
            lean_conservation_contract_issue: MULTIPLIER_EQUIVALENCE_LEAN_CONSERVATION_ISSUE,
            official_row_count: MULTIPLIER_EQUIVALENCE_OFFICIAL_ROW_COUNT,
            num_vars: self.num_vars,
            num_clauses: self.num_clauses,
            official_shape_candidate,
            structural_candidate,
            diagnostic_candidate,
            fail_closed: route_blocker_code != MULTIPLIER_EQUIVALENCE_BLOCKER_NONE,
            route_admitted: false,
            result_authority: false,
            proof_output_authority: false,
            proof_replay_checked: false,
            external_checker_verified: false,
            proof_artifact_present: false,
            gate_and: scout.gate_and,
            gate_xor: scout.gate_xor,
            gates_total: scout.gates_total,
            partial_product_rows: scout.partial_product_ands,
            compressor_layer_rows,
            weighted_conservation_obligation_rows,
            source_clause_bound_rows,
            source_clause_bindings_missing,
            source_gate_clause_references,
            source_gate_clause_bound_references,
            source_gate_clause_binding_missing_references,
            source_gate_clause_duplicate_references,
            source_gate_clause_out_of_range_references,
            source_gate_clause_literal_mismatch_references,
            common_product_witness_rows: 0,
            miter_disequality_rows: 0,
            route_blocker_code,
            scout_rejection_code: circuit_scout_rejection_code(scout.rejection),
        }
    }
}

fn circuit_scout_rejection_code(rejection: CircuitScoutRejection) -> u64 {
    match rejection {
        CircuitScoutRejection::None => 0,
        CircuitScoutRejection::DenseCliqueShape => 1,
        CircuitScoutRejection::EquivalenceChainShape => 2,
        CircuitScoutRejection::MissingGateMix => 3,
        CircuitScoutRejection::MissingAdderCone => 4,
        CircuitScoutRejection::MissingMultiplierCone => 5,
    }
}

/// Default-off route decision for Circuit_multiplier22 SAT-model authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CircuitMultiplier22DimacsSatModelAuthorityRouteDecision {
    /// The route hook was not explicitly enabled.
    Disabled,
    /// The route hook was enabled but stayed fail-closed.
    Blocked {
        /// Typed blocker for the DIMACS-side hook.
        blocker: CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker,
        /// Sanitized counters copied from the packet facade.
        counters: CircuitMultiplier22DimacsSatModelAuthorityRouteCounters,
    },
    /// Retained original-DIMACS model/checker evidence admitted a complete model.
    Admitted {
        /// Complete original-DIMACS assignment in zero-based variable order.
        assignment: Vec<bool>,
        /// Sanitized counters copied from the packet facade.
        counters: CircuitMultiplier22DimacsSatModelAuthorityRouteCounters,
    },
}

#[cfg(test)]
impl CircuitMultiplier22DimacsSatModelAuthorityRouteDecision {
    /// True only when retained evidence admitted a complete SAT model.
    pub(crate) const fn is_admitted(&self) -> bool {
        matches!(self, Self::Admitted { .. })
    }
}

/// Fail-closed blockers for the default-off Circuit_multiplier22 DIMACS hook.
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker {
    /// No retained model/checker evidence was supplied.
    RetainedEvidenceMissing,
    /// A run/matrix artifact handoff omitted a required path variable.
    RetainedArtifactPathEnvMissing(CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind),
    /// A retained artifact path was supplied but the file was missing.
    RetainedArtifactMissing(CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind),
    /// A retained artifact path was supplied but the file could not be read.
    RetainedArtifactReadFailed(CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind),
    /// A run/matrix artifact handoff omitted the checker command.
    RetainedCheckerCommandEnvMissing,
    /// A run/matrix artifact handoff supplied a malformed checker command.
    RetainedCheckerCommandEnvInvalid,
    /// A retained checker command did not invoke `ay check model ... --json`.
    RetainedCheckerCommandShapeMismatch,
    /// A retained checker command did not name the retained original DIMACS path.
    RetainedCheckerCommandFormulaPathMismatch,
    /// A retained checker command did not name the retained model stdout path.
    RetainedCheckerCommandModelStdoutPathMismatch,
    /// A run/matrix artifact handoff omitted the checker exit status.
    RetainedCheckerExitStatusEnvMissing,
    /// A run/matrix artifact handoff supplied a malformed checker exit status.
    RetainedCheckerExitStatusEnvInvalid,
    /// Retained checker process status was not success.
    RetainedCheckerExitStatusNonZero,
    /// Retained checker verdict JSON was malformed.
    RetainedCheckerVerdictJsonInvalid,
    /// Retained checker verdict JSON did not use the model-check schema.
    RetainedCheckerVerdictSchemaMismatch,
    /// Retained checker verdict JSON omitted the original DIMACS path.
    RetainedCheckerVerdictFormulaPathMissing,
    /// Retained checker verdict JSON omitted the model stdout path.
    RetainedCheckerVerdictModelStdoutPathMissing,
    /// Matrix/env formula path disagreed with retained checker verdict JSON.
    RetainedCheckerVerdictFormulaPathMismatch,
    /// Matrix/env model stdout path disagreed with retained checker verdict JSON.
    RetainedCheckerVerdictModelStdoutPathMismatch,
    /// Retained checker verdict JSON omitted `model_status`.
    RetainedCheckerVerdictModelStatusMissing,
    /// Retained checker verdict JSON did not report `model_status=valid`.
    RetainedCheckerVerdictModelStatusNotValid,
    /// Retained checker verdict JSON omitted the top-level `valid` flag.
    RetainedCheckerVerdictValidMissing,
    /// Retained checker verdict JSON did not report `valid=true`.
    RetainedCheckerVerdictInvalid,
    /// Retained checker verdict JSON omitted `num_vars`.
    RetainedCheckerVerdictNumVarsMissing,
    /// Retained checker verdict JSON reported the wrong original variable count.
    RetainedCheckerVerdictNumVarsMismatch,
    /// Retained checker verdict JSON omitted `clauses_checked`.
    RetainedCheckerVerdictClausesCheckedMissing,
    /// Retained checker verdict JSON reported the wrong checked clause count.
    RetainedCheckerVerdictClausesCheckedMismatch,
    /// Retained checker verdict JSON omitted usable `ay_build` provenance.
    RetainedCheckerVerdictBuildProvenanceMissing,
    /// Retained artifact metadata did not include checker verdict bytes.
    RetainedCheckerVerdictJsonMissing,
    /// Retained artifact bytes could not produce an authority packet.
    RetainedArtifactPacketRejected(CircuitOriginalDimacsSatModelAuthorityProductionError),
    /// Retained formula artifact bytes did not match the parsed original DIMACS formula.
    RetainedFormulaBytesMismatch,
    /// Retained model stdout bytes did not match the AY materialized source-frame model.
    RetainedModelStdoutBytesMismatch,
    /// Retained model stdout was not parseable as SAT-COMP model output.
    RetainedModelStdoutParseFailed,
    /// Retained model stdout did not satisfy the parsed original DIMACS formula.
    RetainedModelStdoutInvalid,
    /// The ay-sat packet facade rejected the retained evidence.
    FacadeBlocked {
        /// Original-DIMACS model authority audit status.
        authority_status: CircuitOriginalDimacsSatModelAuthorityStatus,
        /// Packet-level route-admission status after the facade handoff.
        route_admission_status: CircuitEquivRouteAdmissionStatus,
    },
}

impl DimacsFormula {
    /// Return a retained Circuit_multiplier22 SAT assignment only after original-DIMACS validation.
    ///
    /// The hook is default-off and fail-closed. It consumes the same retained
    /// run/matrix artifact environment as the diagnostic route, requires a
    /// complete `ay check model --json` artifact, binds the retained formula
    /// bytes to `original_dimacs_bytes`, and replays the retained SAT-COMP
    /// model stdout against this parsed formula before returning an assignment.
    #[must_use]
    pub fn circuit_multiplier22_retained_sat_model_from_env(
        &self,
        original_dimacs_bytes: &[u8],
    ) -> Option<Vec<bool>> {
        match circuit_multiplier22_dimacs_sat_model_authority_route_from_env_retained_stdout(
            self,
            original_dimacs_bytes,
        ) {
            CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Admitted {
                assignment,
                ..
            } => Some(assignment),
            CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Disabled
            | CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked { .. } => None,
        }
    }
}

/// Retained artifact classes loaded by the DIMACS handoff.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind {
    /// Original DIMACS artifact.
    Formula,
    /// SAT-COMP model stdout artifact.
    ModelStdout,
    /// Retained `ay check model --json` artifact.
    CheckerVerdictJson,
}

/// Sanitized DIMACS-route counters without raw mutable authority bits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitMultiplier22DimacsSatModelAuthorityRouteCounters {
    /// Packet schema version.
    pub(crate) schema_version: u32,
    /// Scoreboard row identifier.
    pub(crate) row_id: &'static str,
    /// Source-frame rows observed by the authority path.
    pub(crate) circuit_source_frame_rows: usize,
    /// Whether the facade attached a complete original-DIMACS model.
    pub(crate) circuit_original_dimacs_model_present: bool,
    /// Original variable count covered by the attached model, if any.
    pub(crate) circuit_original_dimacs_model_vars: usize,
    /// Route-admission status copied from the packet facade.
    pub(crate) route_admission_status: CircuitEquivRouteAdmissionStatus,
}

/// Retained artifacts needed before the DIMACS-side hook can ask for authority.
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifacts {
    /// Original DIMACS artifact path reported to `ay check model --json`.
    pub(crate) formula_path: String,
    /// Retained original DIMACS artifact bytes.
    pub(crate) formula_bytes: Vec<u8>,
    /// SAT-COMP model stdout path reported to `ay check model --json`.
    pub(crate) model_stdout_path: String,
    /// Retained SAT-COMP model stdout bytes.
    pub(crate) model_stdout_bytes: Vec<u8>,
    /// Exact checker command used for the retained verdict.
    pub(crate) checker_command: Vec<String>,
    /// Checker process exit status.
    pub(crate) checker_exit_status: i32,
    /// Retained `ay check model --json` verdict bytes.
    pub(crate) checker_verdict_json: Option<Vec<u8>>,
}

/// Retained artifact paths for the DIMACS-side production handoff.
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactPaths {
    /// Original DIMACS artifact path.
    pub(crate) formula_path: PathBuf,
    /// SAT-COMP model stdout artifact path.
    pub(crate) model_stdout_path: PathBuf,
    /// Retained `ay check model --json` artifact path.
    pub(crate) checker_verdict_json_path: PathBuf,
    /// Exact checker command used for the retained verdict.
    pub(crate) checker_command: Vec<String>,
    /// Checker process exit status.
    pub(crate) checker_exit_status: i32,
}

/// Artifact paths retained by run/matrix model-check evidence columns.
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitMultiplier22DimacsSatModelAuthorityRunMatrixArtifacts {
    /// `model_checker_formula` path from the matrix/check-model artifact.
    pub(crate) model_checker_formula: PathBuf,
    /// `model_checker_stdout` path from the matrix/check-model artifact.
    pub(crate) model_checker_stdout: PathBuf,
    /// `model_checker_artifact` JSON path retained by the run/matrix job.
    pub(crate) model_checker_artifact: PathBuf,
    /// Exact checker command used to produce `model_checker_artifact`.
    pub(crate) checker_command: Vec<String>,
    /// Checker process exit status.
    pub(crate) checker_exit_status: i32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CircuitMultiplier22DimacsSatModelAuthorityArtifactSchemaPaths {
    formula_path: PathBuf,
    model_stdout_path: PathBuf,
}

impl From<&CircuitEquivPacketCounters> for CircuitMultiplier22DimacsSatModelAuthorityRouteCounters {
    fn from(counters: &CircuitEquivPacketCounters) -> Self {
        Self {
            schema_version: counters.schema_version,
            row_id: counters.row_id,
            circuit_source_frame_rows: counters.circuit_source_frame_rows,
            circuit_original_dimacs_model_present: counters.circuit_original_dimacs_model_present,
            circuit_original_dimacs_model_vars: counters.circuit_original_dimacs_model_vars,
            route_admission_status: counters.route_admission_status,
        }
    }
}

/// Evaluate the default-off hook from run/matrix model-check artifacts.
#[allow(dead_code)]
pub(crate) fn circuit_multiplier22_dimacs_sat_model_authority_route_from_run_matrix_artifacts(
    enabled: bool,
    formula: &DimacsFormula,
    source_rows: &[CircuitSourceFrameRow],
    retained: Option<CircuitMultiplier22DimacsSatModelAuthorityRunMatrixArtifacts>,
) -> CircuitMultiplier22DimacsSatModelAuthorityRouteDecision {
    if !enabled {
        return CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Disabled;
    }
    let Some(retained) = retained else {
        return circuit_multiplier22_dimacs_sat_model_authority_route_from_retained_artifact_paths(
            true,
            formula,
            source_rows,
            None,
        );
    };
    let artifact_paths = match circuit_multiplier22_model_checker_artifact_authority_paths(
        &retained.model_checker_artifact,
        Some(&retained.model_checker_formula),
        Some(&retained.model_checker_stdout),
        formula.num_vars,
        formula.clauses.len(),
    ) {
        Ok(paths) => paths,
        Err(blocker) => return circuit_multiplier22_dimacs_blocked_before_facade(formula, blocker),
    };
    if retained.checker_exit_status != 0 {
        return circuit_multiplier22_dimacs_blocked_before_facade(
            formula,
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerExitStatusNonZero,
        );
    }
    if let Err(blocker) = circuit_multiplier22_validate_checker_command_for_paths(
        &retained.checker_command,
        &artifact_paths.formula_path,
        &artifact_paths.model_stdout_path,
    ) {
        return circuit_multiplier22_dimacs_blocked_before_facade(formula, blocker);
    }
    circuit_multiplier22_dimacs_sat_model_authority_route_from_retained_artifact_paths(
        true,
        formula,
        source_rows,
        Some(
            CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactPaths {
                formula_path: artifact_paths.formula_path,
                model_stdout_path: artifact_paths.model_stdout_path,
                checker_verdict_json_path: retained.model_checker_artifact,
                checker_command: retained.checker_command,
                checker_exit_status: retained.checker_exit_status,
            },
        ),
    )
}

fn circuit_multiplier22_dimacs_sat_model_authority_route_from_env_retained_stdout(
    formula: &DimacsFormula,
    original_dimacs_bytes: &[u8],
) -> CircuitMultiplier22DimacsSatModelAuthorityRouteDecision {
    if !circuit_multiplier22_dimacs_sat_model_authority_env_enabled() {
        return CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Disabled;
    }
    match circuit_multiplier22_dimacs_sat_model_authority_run_matrix_artifacts_from_env() {
        Ok(Some(retained)) => {
            circuit_multiplier22_dimacs_sat_model_authority_route_from_retained_stdout_artifacts(
                formula,
                original_dimacs_bytes,
                retained,
            )
        }
        Ok(None) => circuit_multiplier22_dimacs_blocked_before_facade(
            formula,
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedEvidenceMissing,
        ),
        Err(blocker) => circuit_multiplier22_dimacs_blocked_before_facade(formula, blocker),
    }
}

fn circuit_multiplier22_dimacs_sat_model_authority_route_from_retained_stdout_artifacts(
    formula: &DimacsFormula,
    original_dimacs_bytes: &[u8],
    retained: CircuitMultiplier22DimacsSatModelAuthorityRunMatrixArtifacts,
) -> CircuitMultiplier22DimacsSatModelAuthorityRouteDecision {
    let artifact_paths = match circuit_multiplier22_model_checker_artifact_authority_paths(
        &retained.model_checker_artifact,
        Some(&retained.model_checker_formula),
        Some(&retained.model_checker_stdout),
        formula.num_vars,
        formula.clauses.len(),
    ) {
        Ok(paths) => paths,
        Err(blocker) => return circuit_multiplier22_dimacs_blocked_before_facade(formula, blocker),
    };
    if retained.checker_exit_status != 0 {
        return circuit_multiplier22_dimacs_blocked_before_facade(
            formula,
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerExitStatusNonZero,
        );
    }
    if let Err(blocker) = circuit_multiplier22_validate_checker_command_for_paths(
        &retained.checker_command,
        &artifact_paths.formula_path,
        &artifact_paths.model_stdout_path,
    ) {
        return circuit_multiplier22_dimacs_blocked_before_facade(formula, blocker);
    }

    let formula_bytes = match circuit_multiplier22_read_retained_artifact(
        &artifact_paths.formula_path,
        CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::Formula,
    ) {
        Ok(bytes) => bytes,
        Err(blocker) => return circuit_multiplier22_dimacs_blocked_before_facade(formula, blocker),
    };
    if formula_bytes != original_dimacs_bytes {
        return circuit_multiplier22_dimacs_blocked_before_facade(
            formula,
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedFormulaBytesMismatch,
        );
    }

    let model_stdout_bytes = match circuit_multiplier22_read_retained_artifact(
        &artifact_paths.model_stdout_path,
        CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::ModelStdout,
    ) {
        Ok(bytes) => bytes,
        Err(blocker) => return circuit_multiplier22_dimacs_blocked_before_facade(formula, blocker),
    };
    let assignment = match circuit_multiplier22_assignment_from_retained_model_stdout(
        formula.num_vars,
        &model_stdout_bytes,
    ) {
        Ok(assignment) => assignment,
        Err(blocker) => return circuit_multiplier22_dimacs_blocked_before_facade(formula, blocker),
    };
    if !circuit_multiplier22_assignment_satisfies_formula(formula, &assignment) {
        return circuit_multiplier22_dimacs_blocked_before_facade(
            formula,
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutInvalid,
        );
    }

    CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Admitted {
        counters: circuit_multiplier22_dimacs_retained_stdout_admitted_counters(formula),
        assignment,
    }
}

fn circuit_multiplier22_assignment_from_retained_model_stdout(
    num_vars: usize,
    model_stdout_bytes: &[u8],
) -> Result<Vec<bool>, CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker> {
    let model_stdout = std::str::from_utf8(model_stdout_bytes).map_err(|_| {
        CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutParseFailed
    })?;
    let mut assignment = vec![None; num_vars];
    let mut saw_model_line = false;
    let mut saw_assignment = false;
    let mut saw_terminator = false;

    for line in model_stdout.lines() {
        if !line.starts_with('v') {
            continue;
        }
        saw_model_line = true;
        if line != "v" && !line.starts_with("v ") {
            return Err(
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutParseFailed,
            );
        }
        let tokens: Vec<_> = line[1..].split_whitespace().collect();
        if tokens.is_empty() {
            return Err(
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutParseFailed,
            );
        }
        if saw_terminator {
            return Err(
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutParseFailed,
            );
        }
        for (token_index, token) in tokens.iter().enumerate() {
            let lit = token.parse::<i32>().map_err(|_| {
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutParseFailed
            })?;
            if lit == 0 {
                if token_index != tokens.len() - 1 {
                    return Err(
                        CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutParseFailed,
                    );
                }
                saw_terminator = true;
                break;
            }

            let var = usize::try_from(lit.unsigned_abs())
                .ok()
                .and_then(|var| var.checked_sub(1));
            let Some(var) = var.filter(|&var| var < num_vars) else {
                return Err(
                    CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutParseFailed,
                );
            };
            let value = lit > 0;
            match assignment[var] {
                None => {
                    assignment[var] = Some(value);
                    saw_assignment = true;
                }
                Some(previous) if previous == value => {
                    return Err(
                        CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutParseFailed,
                    );
                }
                Some(_) => {
                    return Err(
                        CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutParseFailed,
                    );
                }
            }
        }
    }

    if !saw_model_line || !saw_assignment || !saw_terminator {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutParseFailed,
        );
    }
    Ok(assignment
        .into_iter()
        .map(|value| value.unwrap_or(false))
        .collect())
}

fn circuit_multiplier22_assignment_satisfies_formula(
    formula: &DimacsFormula,
    assignment: &[bool],
) -> bool {
    assignment.len() == formula.num_vars
        && formula.clauses.iter().all(|clause| {
            clause.iter().any(|literal| {
                let value = assignment[literal.variable().index()];
                value == literal.is_positive()
            })
        })
}

fn circuit_multiplier22_dimacs_retained_stdout_admitted_counters(
    formula: &DimacsFormula,
) -> CircuitMultiplier22DimacsSatModelAuthorityRouteCounters {
    let circuit = scout_formula(formula.num_vars, &formula.clauses);
    let packet = CircuitEquivPacket::for_circuit_multiplier22(&circuit);
    let mut counters =
        CircuitMultiplier22DimacsSatModelAuthorityRouteCounters::from(&packet.counters());
    counters.circuit_original_dimacs_model_present = true;
    counters.circuit_original_dimacs_model_vars = formula.num_vars;
    counters.route_admission_status = CircuitEquivRouteAdmissionStatus::Admitted;
    counters
}

/// Evaluate the default-off hook from retained artifact paths.
#[allow(dead_code)]
pub(crate) fn circuit_multiplier22_dimacs_sat_model_authority_route_from_retained_artifact_paths(
    enabled: bool,
    formula: &DimacsFormula,
    source_rows: &[CircuitSourceFrameRow],
    retained: Option<CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactPaths>,
) -> CircuitMultiplier22DimacsSatModelAuthorityRouteDecision {
    if !enabled {
        return CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Disabled;
    }
    let Some(retained) = retained else {
        return circuit_multiplier22_dimacs_sat_model_authority_route_from_retained_artifacts(
            true,
            formula,
            source_rows,
            None,
        );
    };

    let formula_bytes = match circuit_multiplier22_read_retained_artifact(
        &retained.formula_path,
        CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::Formula,
    ) {
        Ok(bytes) => bytes,
        Err(blocker) => return circuit_multiplier22_dimacs_blocked_before_facade(formula, blocker),
    };
    let model_stdout_bytes = match circuit_multiplier22_read_retained_artifact(
        &retained.model_stdout_path,
        CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::ModelStdout,
    ) {
        Ok(bytes) => bytes,
        Err(blocker) => return circuit_multiplier22_dimacs_blocked_before_facade(formula, blocker),
    };
    let checker_verdict_json = match circuit_multiplier22_read_retained_artifact(
        &retained.checker_verdict_json_path,
        CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::CheckerVerdictJson,
    ) {
        Ok(bytes) => bytes,
        Err(blocker) => return circuit_multiplier22_dimacs_blocked_before_facade(formula, blocker),
    };

    circuit_multiplier22_dimacs_sat_model_authority_route_from_retained_artifacts(
        true,
        formula,
        source_rows,
        Some(
            CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifacts {
                formula_path: retained.formula_path.display().to_string(),
                formula_bytes,
                model_stdout_path: retained.model_stdout_path.display().to_string(),
                model_stdout_bytes,
                checker_command: retained.checker_command,
                checker_exit_status: retained.checker_exit_status,
                checker_verdict_json: Some(checker_verdict_json),
            },
        ),
    )
}

fn circuit_multiplier22_read_retained_artifact(
    path: &Path,
    kind: CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind,
) -> Result<Vec<u8>, CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker> {
    fs::read(path).map_err(|error| {
        if error.kind() == ErrorKind::NotFound {
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedArtifactMissing(kind)
        } else {
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedArtifactReadFailed(kind)
        }
    })
}

fn circuit_multiplier22_model_checker_artifact_schema_paths(
    checker_artifact_path: &Path,
    expected_formula_path: Option<&Path>,
    expected_model_stdout_path: Option<&Path>,
) -> Result<
    CircuitMultiplier22DimacsSatModelAuthorityArtifactSchemaPaths,
    CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker,
> {
    let checker_verdict_json = circuit_multiplier22_read_retained_artifact(
        checker_artifact_path,
        CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::CheckerVerdictJson,
    )?;
    circuit_multiplier22_model_checker_artifact_schema_paths_from_bytes(
        &checker_verdict_json,
        expected_formula_path,
        expected_model_stdout_path,
    )
}

fn circuit_multiplier22_model_checker_artifact_authority_paths(
    checker_artifact_path: &Path,
    expected_formula_path: Option<&Path>,
    expected_model_stdout_path: Option<&Path>,
    expected_num_vars: usize,
    expected_clauses_checked: usize,
) -> Result<
    CircuitMultiplier22DimacsSatModelAuthorityArtifactSchemaPaths,
    CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker,
> {
    let checker_verdict_json = circuit_multiplier22_read_retained_artifact(
        checker_artifact_path,
        CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::CheckerVerdictJson,
    )?;
    circuit_multiplier22_model_checker_artifact_authority_paths_from_bytes(
        &checker_verdict_json,
        expected_formula_path,
        expected_model_stdout_path,
        expected_num_vars,
        expected_clauses_checked,
    )
}

fn circuit_multiplier22_model_checker_artifact_schema_paths_from_bytes(
    checker_verdict_json: &[u8],
    expected_formula_path: Option<&Path>,
    expected_model_stdout_path: Option<&Path>,
) -> Result<
    CircuitMultiplier22DimacsSatModelAuthorityArtifactSchemaPaths,
    CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker,
> {
    let payload: serde_json::Value = serde_json::from_slice(checker_verdict_json).map_err(|_| {
        CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictJsonInvalid
    })?;
    circuit_multiplier22_model_checker_artifact_schema_paths_from_payload(
        &payload,
        expected_formula_path,
        expected_model_stdout_path,
    )
}

fn circuit_multiplier22_model_checker_artifact_authority_paths_from_bytes(
    checker_verdict_json: &[u8],
    expected_formula_path: Option<&Path>,
    expected_model_stdout_path: Option<&Path>,
    expected_num_vars: usize,
    expected_clauses_checked: usize,
) -> Result<
    CircuitMultiplier22DimacsSatModelAuthorityArtifactSchemaPaths,
    CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker,
> {
    let payload: serde_json::Value = serde_json::from_slice(checker_verdict_json).map_err(|_| {
        CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictJsonInvalid
    })?;
    let paths = circuit_multiplier22_model_checker_artifact_schema_paths_from_payload(
        &payload,
        expected_formula_path,
        expected_model_stdout_path,
    )?;
    circuit_multiplier22_validate_model_checker_authority_payload(
        &payload,
        expected_num_vars,
        expected_clauses_checked,
    )?;
    Ok(paths)
}

fn circuit_multiplier22_model_checker_artifact_schema_paths_from_payload(
    payload: &serde_json::Value,
    expected_formula_path: Option<&Path>,
    expected_model_stdout_path: Option<&Path>,
) -> Result<
    CircuitMultiplier22DimacsSatModelAuthorityArtifactSchemaPaths,
    CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker,
> {
    let schema = payload
        .get("schema")
        .and_then(serde_json::Value::as_str)
        .unwrap_or_default();
    if schema != CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECK_SCHEMA {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictSchemaMismatch,
        );
    }
    let formula_path = circuit_multiplier22_model_checker_path_field(
        payload,
        "formula",
        CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictFormulaPathMissing,
    )?;
    let model_stdout_path = circuit_multiplier22_model_checker_path_field(
        payload,
        "stdout",
        CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictModelStdoutPathMissing,
    )?;
    if expected_formula_path.is_some_and(|expected| expected != formula_path.as_path()) {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictFormulaPathMismatch,
        );
    }
    if expected_model_stdout_path.is_some_and(|expected| expected != model_stdout_path.as_path()) {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictModelStdoutPathMismatch,
        );
    }
    Ok(
        CircuitMultiplier22DimacsSatModelAuthorityArtifactSchemaPaths {
            formula_path,
            model_stdout_path,
        },
    )
}

fn circuit_multiplier22_model_checker_path_field(
    payload: &serde_json::Value,
    key: &'static str,
    blocker: CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker,
) -> Result<PathBuf, CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker> {
    let Some(path) = payload
        .get(key)
        .and_then(serde_json::Value::as_str)
        .map(str::trim)
        .filter(|path| !path.is_empty())
    else {
        return Err(blocker);
    };
    Ok(PathBuf::from(path))
}

fn circuit_multiplier22_validate_model_checker_authority_payload(
    payload: &serde_json::Value,
    expected_num_vars: usize,
    expected_clauses_checked: usize,
) -> Result<(), CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker> {
    let model_status = payload
        .get("model_status")
        .and_then(serde_json::Value::as_str)
        .ok_or(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictModelStatusMissing,
        )?;
    if model_status != "valid" {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictModelStatusNotValid,
        );
    }

    let valid = payload
        .get("valid")
        .and_then(serde_json::Value::as_bool)
        .ok_or(
        CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictValidMissing,
    )?;
    if !valid {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictInvalid,
        );
    }

    let num_vars = payload
        .get("num_vars")
        .and_then(serde_json::Value::as_u64)
        .and_then(|value| usize::try_from(value).ok())
        .ok_or(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictNumVarsMissing,
        )?;
    if num_vars != expected_num_vars {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictNumVarsMismatch,
        );
    }

    let clauses_checked = payload
        .get("clauses_checked")
        .and_then(serde_json::Value::as_u64)
        .ok_or(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictClausesCheckedMissing,
        )?;
    if clauses_checked != expected_clauses_checked as u64 {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictClausesCheckedMismatch,
        );
    }

    if !circuit_multiplier22_model_checker_payload_has_build_provenance(payload) {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictBuildProvenanceMissing,
        );
    }

    Ok(())
}

fn circuit_multiplier22_model_checker_payload_has_build_provenance(
    payload: &serde_json::Value,
) -> bool {
    let Some(value) = payload.get("ay_build") else {
        return false;
    };
    if value.as_str().is_some_and(|raw| !raw.trim().is_empty()) {
        return true;
    }
    ["stamp", "commit", "version"].into_iter().any(|key| {
        value
            .get(key)
            .and_then(serde_json::Value::as_str)
            .is_some_and(|raw| !raw.trim().is_empty())
    })
}

/// Evaluate the default-off hook from retained artifact bytes.
#[allow(dead_code)]
pub(crate) fn circuit_multiplier22_dimacs_sat_model_authority_route_from_retained_artifacts(
    enabled: bool,
    formula: &DimacsFormula,
    source_rows: &[CircuitSourceFrameRow],
    retained: Option<CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifacts>,
) -> CircuitMultiplier22DimacsSatModelAuthorityRouteDecision {
    if !enabled {
        return CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Disabled;
    }
    let Some(retained) = retained else {
        return circuit_multiplier22_dimacs_sat_model_authority_route(
            true,
            formula,
            source_rows,
            None,
        );
    };
    match circuit_multiplier22_dimacs_sat_model_authority_packet_from_retained_artifacts(
        formula,
        source_rows,
        retained,
    ) {
        Ok(packet) => circuit_multiplier22_dimacs_sat_model_authority_route(
            true,
            formula,
            source_rows,
            Some(packet),
        ),
        Err(blocker) => circuit_multiplier22_dimacs_blocked_before_facade(formula, blocker),
    }
}

#[allow(dead_code)]
fn circuit_multiplier22_dimacs_sat_model_authority_packet_from_retained_artifacts(
    formula: &DimacsFormula,
    source_rows: &[CircuitSourceFrameRow],
    retained: CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifacts,
) -> Result<
    CircuitOriginalDimacsSatModelAuthorityPacket,
    CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker,
> {
    let Some(checker_verdict_json) = retained.checker_verdict_json else {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerVerdictJsonMissing,
        );
    };
    circuit_multiplier22_model_checker_artifact_authority_paths_from_bytes(
        &checker_verdict_json,
        Some(Path::new(&retained.formula_path)),
        Some(Path::new(&retained.model_stdout_path)),
        formula.num_vars,
        formula.clauses.len(),
    )?;
    if retained.checker_exit_status != 0 {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerExitStatusNonZero,
        );
    }
    circuit_multiplier22_validate_checker_command_for_paths(
        &retained.checker_command,
        Path::new(&retained.formula_path),
        Path::new(&retained.model_stdout_path),
    )?;
    let packet = produce_original_dimacs_sat_model_authority_packet(
        formula.num_vars,
        &formula.clauses,
        source_rows,
        &retained.formula_path,
        &retained.model_stdout_path,
        retained.checker_command,
        retained.checker_exit_status,
        checker_verdict_json,
    )
    .map_err(
        CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedArtifactPacketRejected,
    )?;

    if packet.formula_dimacs != retained.formula_bytes {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedFormulaBytesMismatch,
        );
    }
    if packet.model_stdout != retained.model_stdout_bytes {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedModelStdoutBytesMismatch,
        );
    }

    Ok(packet)
}

fn circuit_multiplier22_validate_checker_command_for_paths(
    command: &[String],
    formula_path: &Path,
    model_stdout_path: &Path,
) -> Result<(), CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker> {
    if command.len() < 6 || command[1] != "check" || command[2] != "model" || command[5] != "--json"
    {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerCommandShapeMismatch,
        );
    }
    if command
        .get(3)
        .map(Path::new)
        .is_none_or(|path| path != formula_path)
    {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerCommandFormulaPathMismatch,
        );
    }
    if command
        .get(4)
        .map(Path::new)
        .is_none_or(|path| path != model_stdout_path)
    {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerCommandModelStdoutPathMismatch,
        );
    }
    Ok(())
}

#[allow(dead_code)]
fn circuit_multiplier22_dimacs_blocked_before_facade(
    formula: &DimacsFormula,
    blocker: CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker,
) -> CircuitMultiplier22DimacsSatModelAuthorityRouteDecision {
    let circuit = scout_formula(formula.num_vars, &formula.clauses);
    let packet = CircuitEquivPacket::for_circuit_multiplier22(&circuit);
    CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked {
        blocker,
        counters: CircuitMultiplier22DimacsSatModelAuthorityRouteCounters::from(&packet.counters()),
    }
}

/// Evaluate the default-off Circuit_multiplier22 original-DIMACS SAT-model hook.
#[allow(dead_code)]
pub(crate) fn circuit_multiplier22_dimacs_sat_model_authority_route_from_env(
    formula: &DimacsFormula,
    source_rows: &[CircuitSourceFrameRow],
    retained: Option<CircuitOriginalDimacsSatModelAuthorityPacket>,
) -> CircuitMultiplier22DimacsSatModelAuthorityRouteDecision {
    let enabled = circuit_multiplier22_dimacs_sat_model_authority_env_enabled();
    if !enabled {
        return CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Disabled;
    }
    if retained.is_none() {
        match circuit_multiplier22_dimacs_sat_model_authority_run_matrix_artifacts_from_env() {
            Ok(Some(retained)) => {
                return circuit_multiplier22_dimacs_sat_model_authority_route_from_run_matrix_artifacts(
                    true,
                    formula,
                    source_rows,
                    Some(retained),
                );
            }
            Ok(None) => {}
            Err(blocker) => {
                return circuit_multiplier22_dimacs_blocked_before_facade(formula, blocker);
            }
        }
    }
    circuit_multiplier22_dimacs_sat_model_authority_route(true, formula, source_rows, retained)
}

/// Evaluate a Circuit_multiplier22 original-DIMACS SAT-model hook with an explicit gate.
pub(crate) fn circuit_multiplier22_dimacs_sat_model_authority_route(
    enabled: bool,
    formula: &DimacsFormula,
    source_rows: &[CircuitSourceFrameRow],
    retained: Option<CircuitOriginalDimacsSatModelAuthorityPacket>,
) -> CircuitMultiplier22DimacsSatModelAuthorityRouteDecision {
    if !enabled {
        return CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Disabled;
    }

    let circuit = scout_formula(formula.num_vars, &formula.clauses);
    let Some(retained) = retained else {
        let packet = CircuitEquivPacket::for_circuit_multiplier22(&circuit);
        return CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked {
            blocker:
                CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedEvidenceMissing,
            counters: CircuitMultiplier22DimacsSatModelAuthorityRouteCounters::from(
                &packet.counters(),
            ),
        };
    };

    match circuit_multiplier22_original_dimacs_sat_model_authority_decision(
        &circuit,
        formula.num_vars,
        &formula.clauses,
        source_rows,
        retained,
    ) {
        CircuitEquivOriginalDimacsSatModelAuthorityDecision::Admitted {
            assignment,
            counters,
        } => CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Admitted {
            assignment,
            counters: CircuitMultiplier22DimacsSatModelAuthorityRouteCounters::from(&counters),
        },
        CircuitEquivOriginalDimacsSatModelAuthorityDecision::Blocked {
            authority_status,
            route_admission_status,
            counters,
        } => CircuitMultiplier22DimacsSatModelAuthorityRouteDecision::Blocked {
            blocker: CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::FacadeBlocked {
                authority_status,
                route_admission_status,
            },
            counters: CircuitMultiplier22DimacsSatModelAuthorityRouteCounters::from(&counters),
        },
    }
}

fn circuit_multiplier22_dimacs_sat_model_authority_env_enabled() -> bool {
    std::env::var(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV).is_ok_and(|value| {
        matches!(
            value.trim().to_ascii_lowercase().as_str(),
            "1" | "true" | "yes" | "on"
        )
    })
}

fn circuit_multiplier22_dimacs_sat_model_authority_run_matrix_artifacts_from_env() -> Result<
    Option<CircuitMultiplier22DimacsSatModelAuthorityRunMatrixArtifacts>,
    CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker,
> {
    let formula_path = circuit_multiplier22_path_env(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_FORMULA_ENV,
    );
    let model_stdout_path = circuit_multiplier22_path_env(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_STDOUT_ENV,
    );
    let checker_artifact_path = circuit_multiplier22_path_env(
        CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_MODEL_CHECKER_ARTIFACT_ENV,
    );

    if formula_path.is_none() && model_stdout_path.is_none() && checker_artifact_path.is_none() {
        return Ok(None);
    }

    let checker_artifact_path = if let Some(path) = checker_artifact_path {
        path
    } else {
        let _formula_path = formula_path.ok_or(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedArtifactPathEnvMissing(
                CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::Formula,
            ),
        )?;
        let _model_stdout_path = model_stdout_path.ok_or(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedArtifactPathEnvMissing(
                CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::ModelStdout,
            ),
        )?;
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedArtifactPathEnvMissing(
                CircuitMultiplier22DimacsSatModelAuthorityRetainedArtifactKind::CheckerVerdictJson,
            ),
        );
    };
    let artifact_paths = circuit_multiplier22_model_checker_artifact_schema_paths(
        &checker_artifact_path,
        formula_path.as_deref(),
        model_stdout_path.as_deref(),
    )?;

    let checker_command = circuit_multiplier22_checker_command_env()?.ok_or(
        CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerCommandEnvMissing,
    )?;
    let checker_exit_status = circuit_multiplier22_checker_exit_status_env()?.ok_or(
        CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerExitStatusEnvMissing,
    )?;

    Ok(Some(
        CircuitMultiplier22DimacsSatModelAuthorityRunMatrixArtifacts {
            model_checker_formula: artifact_paths.formula_path,
            model_checker_stdout: artifact_paths.model_stdout_path,
            model_checker_artifact: checker_artifact_path,
            checker_command,
            checker_exit_status,
        },
    ))
}

fn circuit_multiplier22_path_env(name: &str) -> Option<PathBuf> {
    let value = std::env::var(name).ok()?;
    let trimmed = value.trim();
    if trimmed.is_empty() {
        None
    } else {
        Some(PathBuf::from(trimmed))
    }
}

fn circuit_multiplier22_checker_command_env(
) -> Result<Option<Vec<String>>, CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker> {
    let Some(value) =
        std::env::var(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_COMMAND_ENV).ok()
    else {
        return Ok(None);
    };
    if value.trim().is_empty() {
        return Ok(None);
    }
    let command: Vec<String> = serde_json::from_str(&value).map_err(|_| {
        CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerCommandEnvInvalid
    })?;
    if command.is_empty() || command.iter().any(|part| part.trim().is_empty()) {
        return Err(
            CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerCommandEnvInvalid,
        );
    }
    Ok(Some(command))
}

fn circuit_multiplier22_checker_exit_status_env(
) -> Result<Option<i32>, CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker> {
    let Some(value) =
        std::env::var(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_CHECKER_EXIT_STATUS_ENV).ok()
    else {
        return Ok(None);
    };
    if value.trim().is_empty() {
        return Ok(None);
    }
    value.trim().parse::<i32>().map(Some).map_err(|_| {
        CircuitMultiplier22DimacsSatModelAuthorityRouteBlocker::RetainedCheckerExitStatusEnvInvalid
    })
}

/// Convert a raw i32 DIMACS literal to a 0-indexed Literal.
///
/// DIMACS variables are 1-indexed; we use 0-indexed internally.
fn dimacs_lit_to_literal(lit: i32) -> Literal {
    let var = lit.unsigned_abs();
    let variable = Variable(var - 1);
    if lit > 0 {
        Literal::positive(variable)
    } else {
        Literal::negative(variable)
    }
}

/// Cap on the speculative clause-vector pre-allocation derived from the
/// (untrusted) declared `num_clauses`. The real clause vector still grows to
/// fit the actual parsed clauses; this only bounds the up-front `reserve` so a
/// lying header like `p cnf 1 4000000000` cannot pre-allocate gigabytes.
const MAX_CLAUSE_PREALLOC: usize = 1 << 20;

/// Parse a DIMACS CNF formula from a reader
pub(crate) fn parse<R: Read>(reader: R) -> Result<DimacsFormula, DimacsError> {
    let mut header = None;
    let mut clauses: Vec<Vec<Literal>> = Vec::new();
    let parsed_header = dimacs_core::parse_dimacs_events(reader, |event| {
        match event {
            DimacsEvent::Header(parsed) => {
                header = Some(parsed);
                // Cap the speculative pre-allocation: the declared count is
                // untrusted and the vector grows to fit real clauses anyway.
                clauses.reserve(parsed.num_clauses.min(MAX_CLAUSE_PREALLOC));
            }
            DimacsEvent::Record(DimacsRecordRef::Clause(raw)) => {
                let clause: Vec<Literal> = raw.iter().map(|&l| dimacs_lit_to_literal(l)).collect();
                clauses.push(clause);
            }
            DimacsEvent::Record(DimacsRecordRef::Tagged { tag, .. }) => {
                return Err(DimacsCoreError::UnsupportedTaggedLine { tag });
            }
        }
        Ok(())
    })?;
    let header = header.unwrap_or(parsed_header);

    // The declared header `num_vars`/`num_clauses` are kept as-is metadata: they
    // are NOT used to size any allocation (solvers size by actual content — see
    // `into_solver_with_variant` and the streaming paths), but callers such as
    // model counting legitimately need the declared variable count (free
    // variables contribute 2^free models).
    //
    // Backstop on the *actual* maximum variable index (dense numbering makes the
    // per-variable arrays O(max index)): an explicitly-referenced astronomically
    // large index is refused here, before any consumer allocates for it.
    let actual_vars = max_variable_count(&clauses);
    if actual_vars > dimacs_core::MAX_DIMACS_VARS {
        return Err(DimacsError::HeaderCountTooLarge {
            what: "variable",
            declared: actual_vars,
            max: dimacs_core::MAX_DIMACS_VARS,
        });
    }

    Ok(DimacsFormula {
        num_vars: header.num_vars,
        num_clauses: header.num_clauses,
        clauses,
    })
}

/// The number of variables a clause set actually uses: one past the maximum
/// 0-based variable index that appears (0 if there are no literals). This is the
/// content-driven variable count used to size the solver, independent of any
/// declared header.
fn max_variable_count(clauses: &[Vec<Literal>]) -> usize {
    clauses
        .iter()
        .flat_map(|clause| clause.iter())
        .map(|lit| lit.variable().index() + 1)
        .max()
        .unwrap_or(0)
}

/// Parse a DIMACS CNF formula from a string
pub fn parse_str(input: &str) -> Result<DimacsFormula, DimacsError> {
    parse(input.as_bytes())
}

#[cfg(test)]
/// Write a CNF formula in DIMACS format
pub(crate) fn write_dimacs<W: std::io::Write>(
    writer: &mut W,
    num_vars: usize,
    clauses: &[Vec<Literal>],
) -> std::io::Result<()> {
    writeln!(writer, "p cnf {} {}", num_vars, clauses.len())?;
    for clause in clauses {
        for lit in clause {
            write!(writer, "{} ", lit.to_dimacs())?;
        }
        writeln!(writer, "0")?;
    }
    Ok(())
}

#[cfg(test)]
#[path = "dimacs_tests.rs"]
mod tests;
