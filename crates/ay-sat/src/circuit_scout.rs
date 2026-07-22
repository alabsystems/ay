// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Default-off structural scout for circuit/multiplier CNF instances.
//!
//! This module is deliberately diagnostic-only.  It recovers deterministic
//! DIMACS-visible structure from already parsed clauses, but it does not
//! simplify the formula, emit SAT/UNSAT, or relax proof/model obligations.

use crate::clause_arena::ClauseArena;
use crate::features::SatFeatures;
use crate::gates::{Gate, GateExtractor, GateType};
use crate::kani_compat::DetHashMap;
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const MIN_MULTIPLIER_PARTIAL_PRODUCTS: u64 = 2;
const MIN_MULTIPLIER_ADDER_MOTIFS: u64 = 8;
const ORIGINAL_DIMACS_MODEL_CHECK_SCHEMA: &str = "ay.satcomp-model-check/v1";
const ORIGINAL_DIMACS_VALID_MODEL_STATUS: &str = "valid";

/// Why the circuit scout did not classify a formula as a multiplier route.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum CircuitScoutRejection {
    /// No rejection; the report has enough deterministic structure for a
    /// default-off multiplier candidate.
    #[default]
    None,
    /// Dense clique/mutex shape. This must stay in the dense specialist lane.
    DenseCliqueShape,
    /// Equivalence-chain shape without multiplier gate evidence.
    EquivalenceChainShape,
    /// Too few recovered AND/XOR gates.
    MissingGateMix,
    /// Gates were present, but no adder-like cones were recovered.
    MissingAdderCone,
    /// Adders were present, but no multiplier partial-product cone was visible.
    MissingMultiplierCone,
}

/// Why the model-witness scout cannot promise reconstruction from recovered
/// functional structure plus a specialist-provided frontier assignment.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum CircuitModelWitnessRejection {
    /// No rejection; all original variables are either frontier variables or
    /// derivable gate outputs.
    #[default]
    None,
    /// A recovered gate output variable was outside the DIMACS header range.
    GateOutputOutOfRange,
    /// A recovered gate input variable was outside the DIMACS header range.
    GateInputOutOfRange,
    /// More than one recovered gate tried to define the same output variable.
    DuplicateGateOutput,
    /// Some gate outputs could not be covered as direct or derivable values.
    BlockedGateOutput,
}

/// Default-off reconstruction obligations for a future circuit specialist.
///
/// The counts are intentionally structural only. Gate outputs that cannot be
/// replayed from the current recovered dependency graph are counted as direct
/// specialist-assignment obligations, not as solved values.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CircuitModelWitnessReport {
    /// Original DIMACS variable count that a complete model must cover.
    pub(crate) original_model_vars: usize,
    /// Recovered gate-output witnesses over original variables.
    pub(crate) gate_output_witnesses: u64,
    /// AND gate output witnesses.
    pub(crate) and_output_witnesses: u64,
    /// XOR gate output witnesses.
    pub(crate) xor_output_witnesses: u64,
    /// ITE gate output witnesses.
    pub(crate) ite_output_witnesses: u64,
    /// Equivalence gate output witnesses.
    pub(crate) equiv_output_witnesses: u64,
    /// Non-representative members of recovered equivalence classes.
    pub(crate) equivalence_alias_witnesses: u64,
    /// Half/full adder sum-output witnesses.
    pub(crate) adder_sum_witnesses: u64,
    /// AND carry-term witnesses used by recovered adder motifs.
    pub(crate) adder_carry_witnesses: u64,
    /// Partial-product AND witnesses whose inputs are not recovered gate outputs.
    pub(crate) partial_product_witnesses: u64,
    /// Original variables that a partial specialist assignment must provide.
    /// This includes frontier variables and blocked recovered gate outputs.
    pub(crate) partial_assignment_required_vars: usize,
    /// Unique gate-output variables derivable from the frontier.
    pub(crate) derivable_gate_output_vars: usize,
    /// Deterministic topological replay order length over derivable outputs.
    pub(crate) acyclic_replay_order_len: usize,
    /// Unique gate-output variables requiring direct assignment or a stronger
    /// certified derivation order.
    pub(crate) blocked_gate_output_vars: usize,
    /// Blocked outputs whose defining gate depends on a cycle of blocked gate
    /// outputs.
    pub(crate) blocked_by_cycle_output_vars: usize,
    /// Blocked outputs sharing a duplicate recovered definition.
    pub(crate) blocked_by_duplicate_output_vars: usize,
    /// Blocked outputs with malformed or out-of-range gate dependencies.
    pub(crate) blocked_by_malformed_dependency_output_vars: usize,
    /// Blocked outputs with unresolved non-cyclic dependencies. This should be
    /// zero when the dependency classifier is complete.
    pub(crate) blocked_by_unresolved_dependency_output_vars: usize,
    /// Dependency edges from blocked gate outputs to other blocked outputs.
    pub(crate) blocked_output_dependency_edges: usize,
    /// Duplicate recovered gate definitions for the same output variable.
    pub(crate) duplicate_gate_output_defs: u64,
    /// Recovered gate outputs outside the DIMACS header range.
    pub(crate) out_of_range_gate_outputs: u64,
    /// Recovered gate inputs outside the DIMACS header range.
    pub(crate) out_of_range_gate_inputs: u64,
    /// Number of original variables covered by frontier plus derivable outputs.
    pub(crate) complete_original_model_vars: usize,
    /// True when reconstruction metadata must not be used for model output.
    pub(crate) fail_closed: bool,
    /// First fail-closed reason.
    pub(crate) rejection: CircuitModelWitnessRejection,
}

/// Diagnostic binding from recovered gate clause offsets back to DIMACS rows.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CircuitSourceClauseBindingReport {
    /// Gate defining-clause references inspected.
    pub(crate) gate_clause_references: u64,
    /// References that resolved to an exact original DIMACS clause.
    pub(crate) source_clause_bound_rows: u64,
    /// References with no arena-offset-to-source-clause entry.
    pub(crate) source_clause_binding_missing_rows: u64,
    /// Duplicate clause references inside one recovered gate.
    pub(crate) duplicate_gate_clause_reference_rows: u64,
    /// Sidecar entries that named a clause outside the original formula.
    pub(crate) source_clause_out_of_range_rows: u64,
    /// Sidecar entries whose arena literals no longer match the original clause.
    pub(crate) source_clause_literal_mismatch_rows: u64,
    /// True when this diagnostic must block any proof/materialization authority.
    pub(crate) fail_closed: bool,
}

/// Read-only counters recovered by the circuit scout.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CircuitScoutReport {
    /// Number of variables supplied by the DIMACS header.
    pub(crate) num_vars: usize,
    /// Number of clauses supplied by the parser.
    pub(crate) num_clauses: usize,
    /// Recovered AND gates.
    pub(crate) gate_and: u64,
    /// Recovered XOR gates.
    pub(crate) gate_xor: u64,
    /// Recovered ITE gates.
    pub(crate) gate_ite: u64,
    /// Recovered equivalence gates.
    pub(crate) gate_equiv: u64,
    /// Total recovered gate records.
    pub(crate) gates_total: u64,
    /// Sign-aware equivalence classes with more than one variable member.
    pub(crate) equivalence_classes: u64,
    /// Variable members participating in non-singleton equivalence classes.
    pub(crate) equivalence_members: u64,
    /// Duplicate structural gate fingerprints available for hashing.
    pub(crate) structural_hash_groups: u64,
    /// Extra gate outputs inside duplicate structural-hash groups.
    pub(crate) structural_hash_opportunities: u64,
    /// Half-adder motifs: matching XOR2 and AND2 over the same input pair.
    pub(crate) half_adders: u64,
    /// Full-adder motifs recovered from XOR/AND pair structure.
    pub(crate) full_adders: u64,
    /// AND carry-term links participating in recovered adder motifs.
    pub(crate) adder_carry_links: u64,
    /// AND2 gates whose inputs are not outputs of another recovered gate.
    pub(crate) partial_product_ands: u64,
    /// Multiplier-like cones supported by partial products and adder motifs.
    pub(crate) multiplier_cones: u64,
    /// True only for the default-off circuit multiplier candidate surface.
    pub(crate) route_candidate: bool,
    /// Fail-closed route reason when `route_candidate` is false.
    pub(crate) rejection: CircuitScoutRejection,
    /// Default-off original-DIMACS model reconstruction obligations.
    pub(crate) model_witness: CircuitModelWitnessReport,
    /// Diagnostic binding from recovered gate facts to original DIMACS clauses.
    pub(crate) source_clause_binding: CircuitSourceClauseBindingReport,
}

impl CircuitScoutReport {
    fn classify_route(&mut self, features: &SatFeatures) {
        self.rejection = if is_dense_clique_shape(features) {
            CircuitScoutRejection::DenseCliqueShape
        } else if is_equivalence_chain_shape(self) {
            CircuitScoutRejection::EquivalenceChainShape
        } else if self.gate_and < 2 || self.gate_xor == 0 {
            CircuitScoutRejection::MissingGateMix
        } else if self.half_adders + self.full_adders == 0 {
            CircuitScoutRejection::MissingAdderCone
        } else if self.multiplier_cones == 0 {
            CircuitScoutRejection::MissingMultiplierCone
        } else {
            CircuitScoutRejection::None
        };
        self.route_candidate = self.rejection == CircuitScoutRejection::None;
    }
}

/// Recover circuit/multiplier structure from parsed CNF clauses.
pub(crate) fn scout_formula(num_vars: usize, clauses: &[Vec<Literal>]) -> CircuitScoutReport {
    let features = SatFeatures::extract(num_vars, clauses);
    let recovered = recover_gates_with_source_bindings(num_vars, clauses);
    let gates = &recovered.gates;

    let mut report = CircuitScoutReport {
        num_vars,
        num_clauses: clauses.len(),
        ..CircuitScoutReport::default()
    };
    count_gate_kinds(&mut report, gates);
    count_equivalence_classes(&mut report, num_vars, gates);
    count_structural_hashes(&mut report, gates);
    count_adder_and_multiplier_motifs(&mut report, num_vars, gates);
    report.model_witness = build_model_witness_report(num_vars, gates, &report);
    report.source_clause_binding = recovered.source_clause_binding;
    report.classify_route(&features);
    report
}

fn recover_gates(num_vars: usize, clauses: &[Vec<Literal>]) -> Vec<Gate> {
    recover_gates_with_source_bindings(num_vars, clauses).gates
}

struct RecoveredGates {
    gates: Vec<Gate>,
    source_clause_binding: CircuitSourceClauseBindingReport,
}

fn recover_gates_with_source_bindings(num_vars: usize, clauses: &[Vec<Literal>]) -> RecoveredGates {
    let arena = build_clause_arena(num_vars, clauses);
    let mut extractor = GateExtractor::new(num_vars);
    let mut marks = LitMarks::new(num_vars.max(1));
    let vals: &[i8] = &[];
    let mut gates = Vec::new();

    for var_idx in 0..num_vars {
        let var = Variable(var_idx as u32);
        let pos = &arena.pos_occs[var_idx];
        let neg = &arena.neg_occs[var_idx];
        if pos.is_empty() && neg.is_empty() {
            continue;
        }
        if let Some(gate) = extractor.find_gate_for_schedule_with_vals_and_marks(
            var,
            &arena.arena,
            pos,
            neg,
            vals,
            &mut marks,
        ) {
            gates.push(gate);
        }
    }
    let source_clause_binding = audit_gate_source_clause_bindings(&gates, &arena, clauses);
    RecoveredGates {
        gates,
        source_clause_binding,
    }
}

/// Validate a complete assignment against the original parsed DIMACS clauses.
///
/// A specialist route must run this check, or an equivalent original-DIMACS
/// model checker, before reporting SAT. The helper is not wired into Main.
pub(crate) fn validate_original_dimacs_assignment(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    assignment: &[Option<bool>],
) -> Result<(), CircuitModelValidationError> {
    if assignment.len() != num_vars {
        return Err(CircuitModelValidationError::WrongLength {
            expected: num_vars,
            actual: assignment.len(),
        });
    }
    for (idx, value) in assignment.iter().enumerate() {
        if value.is_none() {
            return Err(CircuitModelValidationError::Incomplete { var: idx });
        }
    }
    for (clause_index, clause) in clauses.iter().enumerate() {
        if !clause.iter().any(|&lit| {
            let var_idx = lit.variable().index();
            var_idx < assignment.len()
                && assignment[var_idx].expect("complete assignment checked") == lit.is_positive()
        }) {
            return Err(CircuitModelValidationError::UnsatisfiedClause { clause_index });
        }
    }
    Ok(())
}

/// Materialize a complete original-variable assignment by replaying recovered
/// gates whose inputs are already assigned.
///
/// The caller must provide every non-replayable value directly. The helper is
/// scout-only and validates the finished assignment against the original CNF
/// before returning it.
pub(crate) fn materialize_original_dimacs_assignment(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    direct_assignment: &[Option<bool>],
) -> Result<Vec<bool>, CircuitModelMaterializationError> {
    let assignment = replay_original_dimacs_assignment(num_vars, clauses, direct_assignment)?;

    for (var, value) in assignment.iter().enumerate() {
        if value.is_none() {
            return Err(CircuitModelMaterializationError::MissingDirectValue { var });
        }
    }
    validate_original_dimacs_assignment(num_vars, clauses, &assignment)
        .map_err(CircuitModelMaterializationError::Validation)?;
    Ok(assignment
        .into_iter()
        .map(|value| value.expect("complete assignment validated"))
        .collect())
}

/// Source-frame family allowed to seed scout-only assignment materialization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitSourceFrameFamily {
    /// W390/A162-approved forced-gate source-frame bridge input.
    ForcedGateReplayBridge,
    /// W210 frontier value ledger rows.
    W210Frontier,
    /// W210 SCC choice value ledger rows.
    W210SccChoice,
    /// W377 combined selector rows. These are proxy-frame-only negative
    /// evidence and must not seed original-DIMACS materialization.
    W377CombinedSelector,
    /// Any selector whose only accepted evidence is proxy-frame closure.
    ProxyOnlySelector,
    /// Unknown or not-yet-audited source frame family.
    Other,
}

impl CircuitSourceFrameFamily {
    fn is_materialization_allowed(self) -> bool {
        matches!(
            self,
            Self::ForcedGateReplayBridge | Self::W210Frontier | Self::W210SccChoice
        )
    }
}

/// One deterministic source-frame value for a DIMACS-visible variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CircuitSourceFrameValue {
    /// Zero-based original DIMACS variable index.
    pub(crate) var: usize,
    /// Source-frame truth value for `var`.
    pub(crate) value: bool,
    /// Provenance family for this value.
    pub(crate) family: CircuitSourceFrameFamily,
}

/// Source-frame row kind carried only for audit/provenance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitSourceFrameKind {
    /// Forced gate replay bridge value.
    ForcedGateReplayBridge,
    /// Frontier value from W210-style ledger rows.
    FrontierValue,
    /// SCC choice value from W210-style ledger rows.
    SccChoiceValue,
    /// Other accepted direct value from an audited source family.
    DirectValue,
    /// Direct value for an original DIMACS variable that has no clause occurrence.
    UnreferencedOriginalValue,
}

/// One audited source-frame row bound to an original DIMACS clause literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CircuitSourceFrameRow {
    /// Stable source row identifier from the producing packet.
    pub(crate) source_row_id: u64,
    /// Zero-based original DIMACS variable index.
    pub(crate) var: usize,
    /// Literal that binds this value to an original clause.
    pub(crate) literal: Literal,
    /// Zero-based original clause index containing `literal`.
    pub(crate) clause_id: usize,
    /// Source-frame truth value for `var`.
    pub(crate) source_value: bool,
    /// Provenance family for this value.
    pub(crate) family: CircuitSourceFrameFamily,
    /// Source-frame row kind for diagnostics.
    pub(crate) kind: CircuitSourceFrameKind,
}

/// Audit counters for source-frame materialization.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CircuitSourceFrameAudit {
    /// Input source-frame rows scanned.
    pub(crate) rows_seen: usize,
    /// Rows accepted into the direct assignment seed.
    pub(crate) rows_accepted: usize,
    /// Rows rejected before assignment replay.
    pub(crate) rows_rejected: usize,
    /// Rows rejected because their family is not an original-DIMACS source.
    pub(crate) unsupported_family: usize,
    /// Rows with `var` outside the original DIMACS range.
    pub(crate) var_out_of_range: usize,
    /// Rows whose literal variable did not match `var`.
    pub(crate) literal_var_mismatch: usize,
    /// Rows with `clause_id` outside the original clause list.
    pub(crate) clause_out_of_range: usize,
    /// Rows whose bound literal was absent from the named original clause.
    pub(crate) literal_missing_from_clause: usize,
    /// Rows accepted because the original variable has no clause occurrence.
    pub(crate) unreferenced_original_var_rows: usize,
    /// Rows that claimed unreferenced-variable status for an occurring variable.
    pub(crate) unreferenced_var_occurs: usize,
    /// Rows that conflicted with an earlier source value for the same variable.
    pub(crate) conflicts: usize,
    /// Variables still unassigned after source rows plus replay.
    pub(crate) missing_source_rows: usize,
    /// Original clauses scanned after replay.
    pub(crate) original_clauses_checked: usize,
    /// Falsified original clauses after replay.
    pub(crate) residual_falsified_count: usize,
    /// First falsified original clause, if any.
    pub(crate) first_residual_clause: Option<usize>,
    /// Falsified original clause IDs after replay.
    pub(crate) residual_clause_ids: Vec<usize>,
    /// True when every original variable has a value after replay.
    pub(crate) assignment_complete: bool,
    /// True only when the final original-DIMACS validation passes.
    pub(crate) validation_passed: bool,
}

/// Successful audited source-frame materialization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitMaterializedAssignment {
    /// Complete original-DIMACS assignment.
    pub(crate) assignment: Vec<bool>,
    /// Source-frame and residual audit counters.
    pub(crate) audit: CircuitSourceFrameAudit,
}

/// Retained artifact identity for original-DIMACS model authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitOriginalDimacsArtifactIdentity {
    /// Retained artifact path.
    pub(crate) path: String,
    /// SHA-256 of the retained artifact contents.
    pub(crate) sha256: String,
}

/// Retained artifact binding required before model-check evidence can grant authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitOriginalDimacsModelAuthorityArtifacts {
    /// Original DIMACS artifact used by the checker.
    pub(crate) formula: CircuitOriginalDimacsArtifactIdentity,
    /// SAT-COMP model stdout artifact checked against `formula`.
    pub(crate) model_stdout: CircuitOriginalDimacsArtifactIdentity,
    /// Exact checker command used to produce the verdict JSON.
    pub(crate) checker_command: Vec<String>,
    /// SHA-256 of the retained checker verdict JSON.
    pub(crate) checker_verdict_sha256: String,
}

/// Checker output fields required before a materialized SAT model can carry
/// original-DIMACS authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitOriginalDimacsModelCheckEvidence {
    /// `ay check model --json` schema.
    pub(crate) schema: String,
    /// Original DIMACS artifact reported by the model checker.
    pub(crate) formula: CircuitOriginalDimacsArtifactIdentity,
    /// SAT-COMP model stdout artifact reported by the model checker.
    pub(crate) stdout: CircuitOriginalDimacsArtifactIdentity,
    /// `model_status` reported by the model checker.
    pub(crate) model_status: String,
    /// Top-level `valid` verdict reported by the model checker.
    pub(crate) valid: bool,
    /// Header variable count reported by the model checker.
    pub(crate) num_vars: Option<usize>,
    /// Original clauses streamed by the model checker.
    pub(crate) clauses_checked: u64,
    /// First unsatisfied original clause reported by the checker, if any.
    pub(crate) first_unsatisfied_clause: Option<u64>,
    /// Exact checker command that produced this verdict.
    pub(crate) checker_command: Vec<String>,
    /// Process exit status from the checker command.
    pub(crate) checker_exit_status: i32,
    /// SHA-256 of the retained checker verdict JSON.
    pub(crate) checker_verdict_sha256: String,
    /// Build commit or stamp reported under `ay_build`.
    pub(crate) ay_build_id: String,
}

/// Retained bytes from an original-DIMACS model-check run.
///
/// This is the production binding boundary: hashes are computed from these
/// retained bytes before the authority audit sees any checker evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitOriginalDimacsRetainedModelCheckArtifacts {
    /// Original DIMACS artifact path.
    pub(crate) formula_path: String,
    /// Original DIMACS artifact bytes.
    pub(crate) formula_bytes: Vec<u8>,
    /// SAT-COMP model stdout artifact path.
    pub(crate) model_stdout_path: String,
    /// SAT-COMP model stdout bytes.
    pub(crate) model_stdout_bytes: Vec<u8>,
    /// Exact checker command used to produce `checker_verdict_json`.
    pub(crate) checker_command: Vec<String>,
    /// Process exit status from the checker command.
    pub(crate) checker_exit_status: i32,
    /// Retained `ay check model --json` verdict bytes.
    pub(crate) checker_verdict_json: Vec<u8>,
}

/// Artifact-bound evidence ready for the authority audit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitOriginalDimacsBoundModelCheckEvidence {
    /// Retained artifact identities.
    pub(crate) artifacts: CircuitOriginalDimacsModelAuthorityArtifacts,
    /// Parsed checker evidence with retained-byte hashes attached.
    pub(crate) checker_evidence: CircuitOriginalDimacsModelCheckEvidence,
}

/// Route-silent artifact packet for a validated original-DIMACS SAT model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitOriginalDimacsSatModelAuthorityPacket {
    /// Retained artifact identities.
    pub(crate) artifacts: CircuitOriginalDimacsModelAuthorityArtifacts,
    /// Parsed checker evidence with retained-byte hashes attached.
    pub(crate) checker_evidence: CircuitOriginalDimacsModelCheckEvidence,
    /// Emitted original DIMACS bytes.
    pub(crate) formula_dimacs: Vec<u8>,
    /// Emitted SAT-COMP model stdout bytes.
    pub(crate) model_stdout: Vec<u8>,
    /// Retained checker verdict JSON bytes.
    pub(crate) checker_verdict_json: Vec<u8>,
}

/// Why retained model-check evidence could not be bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitOriginalDimacsModelCheckEvidenceBindingError {
    /// Checker verdict JSON was not valid JSON.
    CheckerVerdictJsonInvalid,
    /// A required string field was missing or was not a string.
    JsonStringFieldMissing(&'static str),
    /// A required bool field was missing or was not a bool.
    JsonBoolFieldMissing(&'static str),
    /// A required unsigned integer field was missing or was not an integer.
    JsonU64FieldMissing(&'static str),
    /// An optional unsigned integer field was present with the wrong type.
    JsonOptionalU64FieldInvalid(&'static str),
    /// `ay_build` did not carry a usable stamp/commit/version string.
    JsonBuildProvenanceMissing,
}

/// Why a SAT-model authority packet could not be produced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitOriginalDimacsSatModelAuthorityProductionError {
    /// Source rows failed original-DIMACS materialization.
    Materialization(CircuitModelMaterializationError),
    /// Retained artifact binding failed.
    Binding(CircuitOriginalDimacsModelCheckEvidenceBindingError),
}

/// Fail-closed original-DIMACS SAT-model authority status.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CircuitOriginalDimacsSatModelAuthorityStatus {
    /// Authority is blocked with a typed reason.
    Blocked(CircuitOriginalDimacsSatModelAuthorityBlocker),
    /// Authority is admitted for SAT/model output only.
    Admitted,
}

impl CircuitOriginalDimacsSatModelAuthorityStatus {
    /// True only when the materialized model and checker evidence both pass.
    pub(crate) const fn is_admitted(&self) -> bool {
        matches!(self, Self::Admitted)
    }
}

/// Fail-closed blockers for original-DIMACS SAT-model authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitOriginalDimacsSatModelAuthorityBlocker {
    /// Source rows did not materialize into a complete, valid original model.
    SourceFrameValidationFailed,
    /// The materializer rejected source rows after the diagnostic audit.
    MaterializationRejected(CircuitModelMaterializationError),
    /// No retained formula/model/checker artifacts were supplied.
    RetainedArtifactsMissing,
    /// Retained original-DIMACS path was empty.
    RetainedFormulaPathMissing,
    /// Retained original-DIMACS SHA-256 was absent or malformed.
    RetainedFormulaHashInvalid,
    /// Retained SAT-COMP model stdout path was empty.
    RetainedModelStdoutPathMissing,
    /// Retained SAT-COMP model stdout SHA-256 was absent or malformed.
    RetainedModelStdoutHashInvalid,
    /// Retained checker command was empty.
    RetainedCheckerCommandMissing,
    /// Retained checker verdict SHA-256 was absent or malformed.
    RetainedCheckerVerdictHashInvalid,
    /// No `ay check model --json` style evidence was supplied.
    CheckerEvidenceMissing,
    /// Checker schema was not `ay.satcomp-model-check/v1`.
    CheckerSchemaMismatch,
    /// Checker evidence did not identify an original formula artifact.
    CheckerFormulaMissing,
    /// Checker evidence formula SHA-256 was absent or malformed.
    CheckerFormulaHashInvalid,
    /// Checker evidence did not identify a SAT-COMP model stdout artifact.
    CheckerStdoutMissing,
    /// Checker evidence model stdout SHA-256 was absent or malformed.
    CheckerStdoutHashInvalid,
    /// Checker command was not retained with the verdict.
    CheckerCommandMissing,
    /// Checker process status was not success.
    CheckerExitStatusNonZero,
    /// Checker verdict SHA-256 was absent or malformed.
    CheckerVerdictHashInvalid,
    /// Checker formula path did not match the retained artifact binding.
    FormulaArtifactPathMismatch,
    /// Checker formula SHA-256 did not match the retained artifact binding.
    FormulaArtifactHashMismatch,
    /// Checker model stdout path did not match the retained artifact binding.
    ModelStdoutArtifactPathMismatch,
    /// Checker model stdout SHA-256 did not match the retained artifact binding.
    ModelStdoutArtifactHashMismatch,
    /// Checker command did not match the retained provenance binding.
    CheckerCommandMismatch,
    /// Checker verdict SHA-256 did not match the retained provenance binding.
    CheckerVerdictHashMismatch,
    /// Checker evidence did not carry build provenance.
    CheckerBuildProvenanceMissing,
    /// Checker `model_status` was not `valid`.
    CheckerModelStatusNotValid,
    /// Checker top-level `valid` flag was false.
    CheckerVerdictInvalid,
    /// Checker did not report the original DIMACS variable count.
    CheckerNumVarsMissing,
    /// Checker variable count did not match the parsed original DIMACS.
    CheckerNumVarsMismatch,
    /// Checker clause count did not match the parsed original DIMACS.
    CheckerClausesCheckedMismatch,
    /// Checker reported an unsatisfied original clause.
    CheckerFirstUnsatisfiedClause,
}

/// Fail-closed authority audit for a AY-owned original-DIMACS SAT model.
///
/// This audit is deliberately route-silent. It may authorize SAT/model output
/// for a future caller only after source-frame materialization validates the
/// original clauses and checker-style evidence proves the emitted SAT-COMP model
/// stdout against that same original DIMACS shape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitOriginalDimacsSatModelAuthorityAudit {
    /// Source-frame and residual scan counters from original-DIMACS materialization.
    pub(crate) source_frame_audit: CircuitSourceFrameAudit,
    /// Materialized assignment when the source rows validate completely.
    pub(crate) materialized_assignment: Option<Vec<bool>>,
    /// Whether retained formula/model/checker artifacts were supplied.
    pub(crate) retained_artifacts_supplied: bool,
    /// Whether checker-style evidence was supplied.
    pub(crate) checker_evidence_supplied: bool,
    /// Retained original-DIMACS path.
    pub(crate) retained_formula_path: Option<String>,
    /// Retained original-DIMACS SHA-256.
    pub(crate) retained_formula_sha256: Option<String>,
    /// Retained SAT-COMP model stdout path.
    pub(crate) retained_model_stdout_path: Option<String>,
    /// Retained SAT-COMP model stdout SHA-256.
    pub(crate) retained_model_stdout_sha256: Option<String>,
    /// Retained checker command.
    pub(crate) retained_checker_command: Option<Vec<String>>,
    /// Retained checker verdict JSON SHA-256.
    pub(crate) retained_checker_verdict_sha256: Option<String>,
    /// Checker schema, if evidence was supplied.
    pub(crate) checker_schema: Option<String>,
    /// Checker original-DIMACS path, if evidence was supplied.
    pub(crate) checker_formula_path: Option<String>,
    /// Checker original-DIMACS SHA-256, if evidence was supplied.
    pub(crate) checker_formula_sha256: Option<String>,
    /// Checker SAT-COMP model stdout path, if evidence was supplied.
    pub(crate) checker_model_stdout_path: Option<String>,
    /// Checker SAT-COMP model stdout SHA-256, if evidence was supplied.
    pub(crate) checker_model_stdout_sha256: Option<String>,
    /// Checker model status, if evidence was supplied.
    pub(crate) checker_model_status: Option<String>,
    /// Checker top-level valid flag, if evidence was supplied.
    pub(crate) checker_valid: Option<bool>,
    /// Checker variable count, if evidence was supplied and parsed.
    pub(crate) checker_num_vars: Option<usize>,
    /// Checker clause count, if evidence was supplied.
    pub(crate) checker_clauses_checked: Option<u64>,
    /// Checker first-unsatisfied-clause field, if any.
    pub(crate) checker_first_unsatisfied_clause: Option<u64>,
    /// Checker command, if evidence was supplied.
    pub(crate) checker_command: Option<Vec<String>>,
    /// Checker exit status, if evidence was supplied.
    pub(crate) checker_exit_status: Option<i32>,
    /// Checker verdict JSON SHA-256, if evidence was supplied.
    pub(crate) checker_verdict_sha256: Option<String>,
    /// Result-silent SAT-model authority status.
    pub(crate) authority_status: CircuitOriginalDimacsSatModelAuthorityStatus,
    /// True only when SAT stdout is authorized.
    pub(crate) sat_output_authority: bool,
    /// True only when a SAT model artifact is authorized.
    pub(crate) model_output_authority: bool,
    /// This SAT-model audit never authorizes proof output.
    pub(crate) proof_output_authority: bool,
    /// True only when the solver SAT verdict is authorized.
    pub(crate) solver_verdict_authority: bool,
}

impl CircuitOriginalDimacsSatModelAuthorityAudit {
    /// True only when every authority bit remains absent.
    pub(crate) const fn authority_is_absent(&self) -> bool {
        !self.sat_output_authority
            && !self.model_output_authority
            && !self.proof_output_authority
            && !self.solver_verdict_authority
    }
}

/// W210 value-ledger family parsed from report TSV.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitSourceFrameValueLedgerKind {
    /// `frontier-value-ledger.tsv`.
    W210Frontier,
    /// `scc-choice-value-ledger.tsv`.
    W210SccChoice,
    /// `forced-gate-value-ledger.tsv`.
    W210ForcedGate,
}

impl CircuitSourceFrameValueLedgerKind {
    fn family(self) -> CircuitSourceFrameFamily {
        match self {
            Self::W210Frontier => CircuitSourceFrameFamily::W210Frontier,
            Self::W210SccChoice => CircuitSourceFrameFamily::W210SccChoice,
            Self::W210ForcedGate => CircuitSourceFrameFamily::ForcedGateReplayBridge,
        }
    }

    fn source_kind(self) -> &'static str {
        match self {
            Self::W210Frontier => "frontier_choice_cegar_best_assignment",
            Self::W210SccChoice => "cyclic_scc_tie_cegar_best_assignment",
            Self::W210ForcedGate => "forced_gate_output_cegar_checked_best_assignment",
        }
    }

    fn production_hook(self) -> &'static str {
        match self {
            Self::W210Frontier => "circuit_global_assignment_search.frontier_value_ledger",
            Self::W210SccChoice => "circuit_global_assignment_search.scc_choice_value_ledger",
            Self::W210ForcedGate => {
                "crates/ay-sat/src/circuit_scout.rs::materialize_original_dimacs_assignment"
            }
        }
    }

    fn row_prefix(self) -> &'static str {
        match self {
            Self::W210Frontier => "w210_frontier_value_",
            Self::W210SccChoice => "w210_scc_choice_value_",
            Self::W210ForcedGate => "w210_forced_gate_value_",
        }
    }
}

/// One parsed W210 value-ledger row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitSourceFrameValueLedgerRow {
    /// Numeric suffix from the W210 `ledger_row_id`.
    pub(crate) source_row_id: u64,
    /// Original ledger row ID.
    pub(crate) ledger_row_id: String,
    /// Parsed source-frame value with zero-based original variable index.
    pub(crate) value: CircuitSourceFrameValue,
    /// Whether the row was present in one of W159's remaining falsified clauses.
    pub(crate) present_in_w159_remaining_clause: bool,
    /// One-based original clause IDs copied from the W210 ledger.
    pub(crate) remaining_clause_ids_1_based: Vec<usize>,
    /// W210 route-eligibility bit. This parser records it but grants no route authority.
    pub(crate) route_eligible: bool,
    /// W210 route blocker text, if present.
    pub(crate) route_blocker: Option<String>,
}

/// Counters for a parsed W210 value ledger.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CircuitSourceFrameValueLedgerStats {
    /// Data rows scanned.
    pub(crate) rows_seen: usize,
    /// Data rows accepted.
    pub(crate) rows_accepted: usize,
    /// Rows marked route-eligible by the report.
    pub(crate) route_eligible_rows: usize,
    /// Rows carrying a non-empty route blocker.
    pub(crate) route_blocked_rows: usize,
    /// Rows present in W159's remaining falsified clause surface.
    pub(crate) present_in_remaining_clause_rows: usize,
    /// Maximum one-based original variable ID seen in the ledger.
    pub(crate) max_original_var_1_based: usize,
}

/// Parsed W210 source-frame value ledger.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitParsedSourceFrameValueLedger {
    /// Ledger kind parsed.
    pub(crate) kind: CircuitSourceFrameValueLedgerKind,
    /// Parsed rows.
    pub(crate) rows: Vec<CircuitSourceFrameValueLedgerRow>,
    /// Parse counters.
    pub(crate) stats: CircuitSourceFrameValueLedgerStats,
}

/// Fail-closed W210 source-frame value-ledger parse error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CircuitSourceFrameValueLedgerParseError {
    /// Input did not contain a TSV header.
    EmptyInput,
    /// A required TSV column was absent.
    MissingColumn {
        /// Missing column name.
        column: &'static str,
    },
    /// A data row had the wrong number of cells.
    RowWidthMismatch {
        /// One-based input line number.
        line: usize,
        /// Header column count.
        expected: usize,
        /// Data row cell count.
        actual: usize,
    },
    /// `ledger_row_id` did not match the expected W210 prefix/suffix.
    InvalidLedgerRowId {
        /// One-based input line number.
        line: usize,
        /// Offending row ID.
        value: String,
    },
    /// `original_var` was not a positive integer.
    InvalidOriginalVar {
        /// One-based input line number.
        line: usize,
        /// Offending value.
        value: String,
    },
    /// `original_var` was zero or larger than the DIMACS header variable count.
    OriginalVarOutOfRange {
        /// One-based input line number.
        line: usize,
        /// One-based original variable ID from W210.
        original_var: usize,
        /// DIMACS header variable count.
        num_vars: usize,
    },
    /// A boolean TSV cell was not `true` or `false`.
    InvalidBool {
        /// One-based input line number.
        line: usize,
        /// Column name.
        column: &'static str,
        /// Offending value.
        value: String,
    },
    /// `value_int` was not `0` or `1`.
    InvalidValueInt {
        /// One-based input line number.
        line: usize,
        /// Offending value.
        value: String,
    },
    /// `value` and `value_int` disagreed.
    ValueIntMismatch {
        /// One-based input line number.
        line: usize,
        /// Parsed `value` cell.
        value: bool,
        /// Parsed `value_int` cell.
        value_int: u8,
    },
    /// `source_kind` did not match the requested W210 ledger kind.
    SourceKindMismatch {
        /// One-based input line number.
        line: usize,
        /// Expected source kind.
        expected: &'static str,
        /// Actual source kind.
        actual: String,
    },
    /// `production_hook` did not match the requested W210 ledger kind.
    ProductionHookMismatch {
        /// One-based input line number.
        line: usize,
        /// Expected production hook.
        expected: &'static str,
        /// Actual production hook.
        actual: String,
    },
    /// A space-separated integer list cell contained a malformed integer.
    InvalidIntegerListCell {
        /// One-based input line number.
        line: usize,
        /// Column name.
        column: &'static str,
        /// Offending value.
        value: String,
    },
    /// W210 row claimed route eligibility before original-DIMACS validation.
    RouteEligibleUnsupported {
        /// One-based input line number.
        line: usize,
    },
    /// W210 route blocker was not the accepted fail-closed blocker.
    RouteBlockerMismatch {
        /// One-based input line number.
        line: usize,
        /// Actual route blocker text.
        actual: String,
    },
}

/// Audit-only combined assignment surface from the three W210 value ledgers.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CircuitW210ValueLedgerAudit {
    /// Total parsed W210 rows scanned.
    pub(crate) rows_seen: usize,
    /// Rows accepted as the first value for an original variable.
    pub(crate) rows_accepted: usize,
    /// Duplicate rows that repeated the same value for an already covered variable.
    pub(crate) duplicate_same_value_rows: usize,
    /// Duplicate rows that conflicted with an already covered variable.
    pub(crate) conflicting_rows: usize,
    /// Original variables covered by at least one W210 row.
    pub(crate) covered_vars: usize,
    /// Original variables not covered by the combined W210 ledgers.
    pub(crate) missing_vars: usize,
    /// First missing original variable, if any.
    pub(crate) first_missing_var: Option<usize>,
    /// Original clauses scanned by residual diagnostics.
    pub(crate) original_clauses_checked: usize,
    /// Falsified original clauses under the combined W210 value surface.
    pub(crate) residual_falsified_count: usize,
    /// First falsified original clause, if any.
    pub(crate) first_residual_clause: Option<usize>,
    /// All falsified original clause IDs.
    pub(crate) residual_clause_ids: Vec<usize>,
    /// True when every original variable was covered.
    pub(crate) assignment_complete: bool,
    /// True only when coverage is complete, no conflict exists, and every original clause is satisfied.
    pub(crate) validation_passed: bool,
}

/// Fail-closed W210 combiner error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CircuitW210ValueLedgerAuditError {
    /// A ledger was passed in the wrong role/order.
    LedgerKindMismatch {
        /// Input role being checked.
        role: &'static str,
        /// Expected ledger kind for that role.
        expected: CircuitSourceFrameValueLedgerKind,
        /// Actual ledger kind supplied.
        actual: CircuitSourceFrameValueLedgerKind,
    },
}

/// Source-frame rows derived from W210 value ledgers plus derivation counters.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CircuitW210SourceFrameRows {
    /// Rows safe to pass into the source-frame audit surface.
    pub(crate) rows: Vec<CircuitSourceFrameRow>,
    /// Fail-closed derivation counters.
    pub(crate) audit: CircuitW210SourceFrameRowAudit,
}

/// Audit counters for deriving clause-bound source-frame rows from W210 ledgers.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CircuitW210SourceFrameRowAudit {
    /// Parsed W210 value rows scanned.
    pub(crate) rows_seen: usize,
    /// Rows materialized into source-frame rows.
    pub(crate) rows_materialized: usize,
    /// Rows materialized from an opposite literal in a W210 residual clause.
    pub(crate) residual_opposite_literal_rows: usize,
    /// Rows rejected before source-frame audit.
    pub(crate) rows_rejected: usize,
    /// Rows with no W210 remaining-clause witness.
    pub(crate) missing_clause_witness_rows: usize,
    /// Rows whose W210 remaining-clause witness was absent or stale and that
    /// AY rebound to an original clause containing the value-consistent literal.
    pub(crate) reconstructed_clause_witness_rows: usize,
    /// Rows whose stale W210 remaining-clause witness was rebound to a
    /// value-consistent original clause instead of using residual-opposite
    /// diagnostic evidence.
    pub(crate) stale_clause_witness_rebound_rows: usize,
    /// Rows with no W210 remaining-clause witness because the original variable
    /// does not occur in any original DIMACS clause.
    pub(crate) unreferenced_original_var_rows: usize,
    /// Rows whose W210 remaining-clause witness was outside the original formula.
    pub(crate) clause_out_of_range_rows: usize,
    /// Rows whose W210 remaining-clause witness did not contain the value literal.
    pub(crate) literal_missing_from_clause_rows: usize,
    /// First fail-closed row rejection, if any.
    pub(crate) first_rejection: Option<CircuitW210SourceFrameRowRejection>,
}

/// First fail-closed W210 source-frame row derivation rejection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CircuitW210SourceFrameRowRejection {
    /// A row had no remaining-clause witness to bind the value.
    MissingClauseWitness {
        /// Stable source row identifier from W210.
        source_row_id: u64,
    },
    /// A W210 one-based remaining-clause ID was outside the formula.
    ClauseOutOfRange {
        /// Stable source row identifier from W210.
        source_row_id: u64,
        /// One-based original clause ID copied from W210.
        clause_id_1_based: usize,
    },
    /// No W210 remaining clause contained the value-consistent literal.
    LiteralMissingFromClause {
        /// Stable source row identifier from W210.
        source_row_id: u64,
        /// Value-consistent DIMACS literal expected in one W210 remaining clause.
        literal_dimacs: i32,
        /// One-based original clause IDs searched.
        clause_ids_1_based: Vec<usize>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CircuitDerivedW210SourceFrameRow {
    row: CircuitSourceFrameRow,
    reconstructed_clause_witness: bool,
    stale_clause_witness_rebound: bool,
    unreferenced_original_var: bool,
}

/// Result-silent W210 route-admission status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitW210RouteAdmissionStatus {
    /// Route admission is blocked with a typed reason.
    Blocked(CircuitW210RouteAdmissionBlocker),
    /// A future caller supplied every required authority bit after validation.
    Admitted,
}

impl CircuitW210RouteAdmissionStatus {
    /// True only for an admitted route.
    pub(crate) const fn is_admitted(self) -> bool {
        matches!(self, Self::Admitted)
    }
}

/// Fail-closed blockers for W210-derived source-frame route admission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitW210RouteAdmissionBlocker {
    /// Combined W210 ledgers contain conflicting values.
    ValueLedgerConflict,
    /// Combined W210 ledgers do not cover every original variable.
    ValueLedgerIncomplete,
    /// Combined W210 ledgers leave falsified original DIMACS clauses.
    ValueLedgerResidualNonZero,
    /// One or more W210 rows could not be bound to an original clause literal.
    SourceFrameDerivationRejected,
    /// Derived source rows were rejected by the source-frame audit.
    SourceFrameRejected,
    /// Derived source rows do not cover every original variable after replay.
    SourceFrameIncomplete,
    /// Derived source rows leave falsified original DIMACS clauses.
    SourceFrameResidualNonZero,
    /// Original-DIMACS validation passed, but no authority bits were supplied.
    AuthorityAbsent,
}

/// Fail-closed W210 route-admission blocker packet.
///
/// This audit consumes the derived W210 source-frame rows before any
/// materialization path can see them. It never returns a model and never grants
/// route, SAT stdout, proof output, model output, or solver-verdict authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitW210RouteAdmissionAudit {
    /// Combined W210 value-ledger residual audit.
    pub(crate) value_ledger_audit: CircuitW210ValueLedgerAudit,
    /// Clause-bound source-row derivation counters.
    pub(crate) source_frame_row_audit: CircuitW210SourceFrameRowAudit,
    /// Source-frame row audit, populated only after every W210 row binds.
    pub(crate) source_frame_audit: CircuitSourceFrameAudit,
    /// True when the source-frame audit was allowed to consume derived rows.
    pub(crate) source_frame_audit_ran: bool,
    /// True only when all audit layers validate the original DIMACS formula.
    pub(crate) original_dimacs_validation_passed: bool,
    /// Result-silent route-admission status.
    pub(crate) route_admission_status: CircuitW210RouteAdmissionStatus,
    /// Hard false in this audit helper.
    pub(crate) route_admitted: bool,
    /// Hard false in this audit helper.
    pub(crate) sat_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) model_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) proof_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) solver_verdict_authority: bool,
}

impl CircuitW210RouteAdmissionAudit {
    /// True only when every authority bit remains absent.
    pub(crate) const fn authority_is_absent(&self) -> bool {
        !self.route_admitted
            && !self.sat_output_authority
            && !self.model_output_authority
            && !self.proof_output_authority
            && !self.solver_verdict_authority
    }
}

/// Original-DIMACS authority kind required before a W210 route can emit a result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitW210OriginalDimacsAuthorityKind {
    /// SAT authority backed by a validated model for the original DIMACS formula.
    SatModel,
    /// UNSAT authority backed by an externally checked proof for the original DIMACS formula.
    UnsatProof,
}

mod w210_original_dimacs_authority {
    use super::CircuitW210OriginalDimacsAuthorityKind;

    /// Checker-backed original-DIMACS authority verdict supplied by a future route.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) struct CircuitW210OriginalDimacsAuthorityVerdict {
        kind: CircuitW210OriginalDimacsAuthorityKind,
        checked: bool,
        accepted: bool,
    }

    impl CircuitW210OriginalDimacsAuthorityVerdict {
        /// Rejected checker-backed authority verdict for tests and future callers.
        pub(crate) const fn rejected(kind: CircuitW210OriginalDimacsAuthorityKind) -> Self {
            Self {
                kind,
                checked: true,
                accepted: false,
            }
        }

        /// Unchecked authority claim; this must never admit the W210 route.
        pub(crate) const fn unchecked(kind: CircuitW210OriginalDimacsAuthorityKind) -> Self {
            Self {
                kind,
                checked: false,
                accepted: false,
            }
        }

        /// Accepted checker-backed authority verdict for fail-closed regression tests only.
        #[cfg(test)]
        pub(crate) const fn test_accepted(kind: CircuitW210OriginalDimacsAuthorityKind) -> Self {
            Self {
                kind,
                checked: true,
                accepted: true,
            }
        }

        /// Kind of checked authority supplied.
        pub(crate) const fn kind(self) -> CircuitW210OriginalDimacsAuthorityKind {
            self.kind
        }

        /// True only when a AY-owned model validator or external proof checker ran.
        pub(crate) const fn is_checked(self) -> bool {
            self.checked
        }

        /// True only when that validator/checker accepted the original DIMACS artifact.
        pub(crate) const fn is_accepted(self) -> bool {
            self.accepted
        }
    }
}

/// Checker-backed original-DIMACS authority verdict with private construction.
pub(crate) use w210_original_dimacs_authority::CircuitW210OriginalDimacsAuthorityVerdict;

/// Result-silent W210 source-witness authority status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitW210SourceWitnessAuthorityStatus {
    /// Authority is blocked with a typed reason.
    Blocked(CircuitW210SourceWitnessAuthorityBlocker),
    /// Authority is admitted for the named original-DIMACS result kind.
    Admitted(CircuitW210OriginalDimacsAuthorityKind),
}

impl CircuitW210SourceWitnessAuthorityStatus {
    /// True only for admitted checker-backed authority.
    pub(crate) const fn is_admitted(self) -> bool {
        matches!(self, Self::Admitted(_))
    }
}

/// Fail-closed blockers for W210 source-witness authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitW210SourceWitnessAuthorityBlocker {
    /// The underlying W210 route-admission audit did not reach authority handoff.
    RouteAdmission(CircuitW210RouteAdmissionBlocker),
    /// No original-DIMACS model/proof checker verdict was supplied.
    OriginalDimacsAuthorityMissing,
    /// The supplied authority kind does not match the expected result kind.
    OriginalDimacsAuthorityKindMismatch,
    /// A caller supplied an authority claim that no checker/validator backed.
    OriginalDimacsAuthorityUnchecked,
    /// A checker/validator ran and rejected the original-DIMACS artifact.
    OriginalDimacsAuthorityRejected,
}

/// Fail-closed W210 source-witness authority audit.
///
/// This is the narrow handoff API between W210 source-ledger diagnostics and a
/// future Main-legal route. It grants authority only after value-ledger and
/// source-frame validation pass and a checker-backed original-DIMACS verdict is
/// supplied for the expected result kind.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitW210SourceWitnessAuthorityAudit {
    /// Existing W210 route-admission validation and blocker audit.
    pub(crate) route_admission_audit: CircuitW210RouteAdmissionAudit,
    /// Diagnostic residual-source witnesses that bind opposite residual literals.
    pub(crate) residual_source_witness_row_audit: CircuitW210SourceFrameRowAudit,
    /// Expected original-DIMACS authority kind for this circuit row.
    pub(crate) expected_authority_kind: CircuitW210OriginalDimacsAuthorityKind,
    /// Supplied original-DIMACS authority kind, if any.
    pub(crate) supplied_authority_kind: Option<CircuitW210OriginalDimacsAuthorityKind>,
    /// Whether the supplied authority verdict was checker-backed.
    pub(crate) original_dimacs_authority_checked: bool,
    /// Whether the checker/validator accepted the original-DIMACS artifact.
    pub(crate) original_dimacs_authority_accepted: bool,
    /// Result-silent W210 authority status.
    pub(crate) authority_status: CircuitW210SourceWitnessAuthorityStatus,
    /// True only when the validated W210 route may emit a result.
    pub(crate) route_admitted: bool,
    /// True only when SAT stdout is authorized.
    pub(crate) sat_output_authority: bool,
    /// True only when UNSAT stdout is authorized.
    pub(crate) unsat_output_authority: bool,
    /// True only when a SAT model artifact is authorized.
    pub(crate) model_output_authority: bool,
    /// True only when an UNSAT proof artifact is authorized.
    pub(crate) proof_output_authority: bool,
    /// True only when the solver verdict is authorized.
    pub(crate) solver_verdict_authority: bool,
}

impl CircuitW210SourceWitnessAuthorityAudit {
    /// True only when every authority bit remains absent.
    pub(crate) const fn authority_is_absent(&self) -> bool {
        !self.route_admitted
            && !self.sat_output_authority
            && !self.unsat_output_authority
            && !self.model_output_authority
            && !self.proof_output_authority
            && !self.solver_verdict_authority
    }
}

/// One W210 residual-clause flip candidate checked against the full DIMACS.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitW210ResidualRepairCandidate {
    /// Ledger family that supplied the stale value.
    pub(crate) ledger_kind: CircuitSourceFrameValueLedgerKind,
    /// Stable W210 row identifier.
    pub(crate) source_row_id: u64,
    /// Zero-based original DIMACS variable index.
    pub(crate) var: usize,
    /// W210 value before the candidate flip.
    pub(crate) from_value: bool,
    /// Candidate value that would satisfy `clause_id`.
    pub(crate) to_value: bool,
    /// Zero-based original residual clause containing the flipped literal.
    pub(crate) clause_id: usize,
    /// Falsified original clauses after the candidate flip.
    pub(crate) residual_falsified_count: usize,
    /// Original W210 residual clauses repaired by this flip.
    pub(crate) repaired_original_residual_count: usize,
    /// Original W210 residual clauses still falsified after this flip.
    pub(crate) remaining_original_residual_count: usize,
    /// Newly falsified clauses outside the original W210 residual set.
    pub(crate) new_residual_count: usize,
    /// First newly falsified clause, if any.
    pub(crate) first_new_residual_clause: Option<usize>,
    /// True only when the full original-DIMACS scan passes.
    pub(crate) validation_passed: bool,
}

/// One W210 value flip used by higher-order residual diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CircuitW210ResidualRepairFlip {
    /// Ledger family that supplied the stale value.
    pub(crate) ledger_kind: CircuitSourceFrameValueLedgerKind,
    /// Stable W210 row identifier.
    pub(crate) source_row_id: u64,
    /// Zero-based original DIMACS variable index.
    pub(crate) var: usize,
    /// W210 value before the candidate flip.
    pub(crate) from_value: bool,
    /// Candidate value that would satisfy `clause_id`.
    pub(crate) to_value: bool,
    /// Zero-based original residual clause containing the flipped literal.
    pub(crate) clause_id: usize,
}

impl From<&CircuitW210ResidualRepairCandidate> for CircuitW210ResidualRepairFlip {
    fn from(candidate: &CircuitW210ResidualRepairCandidate) -> Self {
        Self {
            ledger_kind: candidate.ledger_kind,
            source_row_id: candidate.source_row_id,
            var: candidate.var,
            from_value: candidate.from_value,
            to_value: candidate.to_value,
            clause_id: candidate.clause_id,
        }
    }
}

/// One pair of W210 residual-clause flips checked against the full DIMACS.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitW210ResidualRepairPairCandidate {
    /// First candidate flip in deterministic W210 ledger order.
    pub(crate) first: CircuitW210ResidualRepairFlip,
    /// Second candidate flip in deterministic W210 ledger order.
    pub(crate) second: CircuitW210ResidualRepairFlip,
    /// Falsified original clauses after both candidate flips.
    pub(crate) residual_falsified_count: usize,
    /// Original W210 residual clauses repaired by this pair.
    pub(crate) repaired_original_residual_count: usize,
    /// Original W210 residual clauses still falsified after this pair.
    pub(crate) remaining_original_residual_count: usize,
    /// Newly falsified clauses outside the original W210 residual set.
    pub(crate) new_residual_count: usize,
    /// First newly falsified clause, if any.
    pub(crate) first_new_residual_clause: Option<usize>,
    /// True only when the full original-DIMACS scan passes.
    pub(crate) validation_passed: bool,
}

/// One triple of W210 residual-clause flips checked against the full DIMACS.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitW210ResidualRepairTripleCandidate {
    /// First candidate flip in deterministic W210 ledger order.
    pub(crate) first: CircuitW210ResidualRepairFlip,
    /// Second candidate flip in deterministic W210 ledger order.
    pub(crate) second: CircuitW210ResidualRepairFlip,
    /// Third candidate flip in deterministic W210 ledger order.
    pub(crate) third: CircuitW210ResidualRepairFlip,
    /// Falsified original clauses after all three candidate flips.
    pub(crate) residual_falsified_count: usize,
    /// Original W210 residual clauses repaired by this triple.
    pub(crate) repaired_original_residual_count: usize,
    /// Original W210 residual clauses still falsified after this triple.
    pub(crate) remaining_original_residual_count: usize,
    /// Newly falsified clauses outside the original W210 residual set.
    pub(crate) new_residual_count: usize,
    /// First newly falsified clause, if any.
    pub(crate) first_new_residual_clause: Option<usize>,
    /// True only when the full original-DIMACS scan passes.
    pub(crate) validation_passed: bool,
}

/// Full-CNF audit for local W210 residual-clause repair candidates.
///
/// The audit is diagnostic-only. It never returns a model and never grants
/// route, SAT stdout, proof output, model output, or solver-verdict authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitW210ResidualRepairAudit {
    /// Combined W210 value-ledger residual audit before any candidate flip.
    pub(crate) value_ledger_audit: CircuitW210ValueLedgerAudit,
    /// Parsed W210 rows scanned.
    pub(crate) rows_seen: usize,
    /// Rows without a remaining-clause witness.
    pub(crate) rows_without_clause_witness: usize,
    /// Rows whose witnesses did not contain the flip-satisfied literal.
    pub(crate) rows_without_flip_literal: usize,
    /// Candidate rows checked with a full original-DIMACS scan.
    pub(crate) candidate_rows: usize,
    /// Candidates that reduce total falsified original clauses.
    pub(crate) improving_candidates: usize,
    /// Candidates that keep the same total falsified original clause count.
    pub(crate) plateau_candidates: usize,
    /// Candidates that increase total falsified original clauses.
    pub(crate) worsening_candidates: usize,
    /// Best total falsified original-clause count observed.
    pub(crate) best_residual_falsified_count: usize,
    /// Best count of original W210 residual clauses repaired.
    pub(crate) best_repaired_original_residual_count: usize,
    /// Best count of original W210 residual clauses still falsified.
    pub(crate) best_remaining_original_residual_count: usize,
    /// Best candidate by full residual count, then original-residual repair.
    pub(crate) best_candidate: Option<CircuitW210ResidualRepairCandidate>,
    /// True only if a candidate passed full original-DIMACS validation.
    pub(crate) validation_passed: bool,
    /// Hard false in this audit helper.
    pub(crate) route_admitted: bool,
    /// Hard false in this audit helper.
    pub(crate) sat_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) model_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) proof_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) solver_verdict_authority: bool,
}

impl CircuitW210ResidualRepairAudit {
    /// True only when every authority bit remains absent.
    pub(crate) const fn authority_is_absent(&self) -> bool {
        !self.route_admitted
            && !self.sat_output_authority
            && !self.model_output_authority
            && !self.proof_output_authority
            && !self.solver_verdict_authority
    }
}

/// Full-CNF audit for two-row W210 residual-clause repair candidates.
///
/// This is a diagnostic reducer for the single-row plateau. It never returns a
/// model and never grants route, SAT stdout, proof output, model output, or
/// solver-verdict authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitW210ResidualRepairPairAudit {
    /// Combined W210 value-ledger residual audit before any candidate flip.
    pub(crate) value_ledger_audit: CircuitW210ValueLedgerAudit,
    /// Clause-witnessed single-row candidates used to form pairs.
    pub(crate) single_candidate_rows: usize,
    /// Same-variable pairs skipped because the flips are mutually exclusive.
    pub(crate) same_var_pairs_skipped: usize,
    /// Two-row candidates checked with a full original-DIMACS scan.
    pub(crate) pair_candidates: usize,
    /// Pairs that reduce total falsified original clauses.
    pub(crate) improving_pairs: usize,
    /// Pairs that keep the same total falsified original clause count.
    pub(crate) plateau_pairs: usize,
    /// Pairs that increase total falsified original clauses.
    pub(crate) worsening_pairs: usize,
    /// Best total falsified original-clause count observed.
    pub(crate) best_residual_falsified_count: usize,
    /// Best count of original W210 residual clauses repaired.
    pub(crate) best_repaired_original_residual_count: usize,
    /// Best count of original W210 residual clauses still falsified.
    pub(crate) best_remaining_original_residual_count: usize,
    /// Best count of newly falsified clauses outside the W210 residual set.
    pub(crate) best_new_residual_count: usize,
    /// Best pair by full residual count, then original-residual repair.
    pub(crate) best_pair: Option<CircuitW210ResidualRepairPairCandidate>,
    /// True only if a pair passed full original-DIMACS validation.
    pub(crate) validation_passed: bool,
    /// Hard false in this audit helper.
    pub(crate) route_admitted: bool,
    /// Hard false in this audit helper.
    pub(crate) sat_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) model_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) proof_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) solver_verdict_authority: bool,
}

impl CircuitW210ResidualRepairPairAudit {
    /// True only when every authority bit remains absent.
    pub(crate) const fn authority_is_absent(&self) -> bool {
        !self.route_admitted
            && !self.sat_output_authority
            && !self.model_output_authority
            && !self.proof_output_authority
            && !self.solver_verdict_authority
    }
}

/// Full-CNF audit for three-row W210 residual-clause repair candidates.
///
/// This is the next bounded diagnostic after the pair search. It never returns
/// a model and never grants route, SAT stdout, proof output, model output, or
/// solver-verdict authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitW210ResidualRepairTripleAudit {
    /// Combined W210 value-ledger residual audit before any candidate flip.
    pub(crate) value_ledger_audit: CircuitW210ValueLedgerAudit,
    /// Clause-witnessed single-row candidates used to form triples.
    pub(crate) single_candidate_rows: usize,
    /// Same-variable triples skipped because the flips are mutually exclusive.
    pub(crate) same_var_triples_skipped: usize,
    /// Three-row candidates checked with a full original-DIMACS scan.
    pub(crate) triple_candidates: usize,
    /// Triples that reduce total falsified original clauses.
    pub(crate) improving_triples: usize,
    /// Triples that keep the same total falsified original clause count.
    pub(crate) plateau_triples: usize,
    /// Triples that increase total falsified original clauses.
    pub(crate) worsening_triples: usize,
    /// Best total falsified original-clause count observed.
    pub(crate) best_residual_falsified_count: usize,
    /// Best count of original W210 residual clauses repaired.
    pub(crate) best_repaired_original_residual_count: usize,
    /// Best count of original W210 residual clauses still falsified.
    pub(crate) best_remaining_original_residual_count: usize,
    /// Best count of newly falsified clauses outside the W210 residual set.
    pub(crate) best_new_residual_count: usize,
    /// Best triple by full residual count, then original-residual repair.
    pub(crate) best_triple: Option<CircuitW210ResidualRepairTripleCandidate>,
    /// True only if a triple passed full original-DIMACS validation.
    pub(crate) validation_passed: bool,
    /// Hard false in this audit helper.
    pub(crate) route_admitted: bool,
    /// Hard false in this audit helper.
    pub(crate) sat_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) model_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) proof_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) solver_verdict_authority: bool,
}

impl CircuitW210ResidualRepairTripleAudit {
    /// True only when every authority bit remains absent.
    pub(crate) const fn authority_is_absent(&self) -> bool {
        !self.route_admitted
            && !self.sat_output_authority
            && !self.model_output_authority
            && !self.proof_output_authority
            && !self.solver_verdict_authority
    }
}

/// Full-CNF audit for replaying all residual-source witnesses into W210 values.
///
/// This is a diagnostic-only model reconstruction check. It overlays the
/// opposite-literal residual witnesses on top of the complete W210 assignment,
/// scans the original DIMACS formula, and never grants route, SAT stdout, proof
/// output, model output, or solver-verdict authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitW210ResidualSourceWitnessReplayAudit {
    /// Combined W210 value-ledger residual audit before any witness overlay.
    pub(crate) value_ledger_audit: CircuitW210ValueLedgerAudit,
    /// Residual-source witness row derivation counters.
    pub(crate) residual_source_witness_row_audit: CircuitW210SourceFrameRowAudit,
    /// Residual-source rows from the W210 frontier ledger.
    pub(crate) frontier_rows: usize,
    /// Residual-source rows from the W210 SCC-choice ledger.
    pub(crate) scc_choice_rows: usize,
    /// Residual-source rows from the W210 forced-gate ledger.
    pub(crate) forced_gate_rows: usize,
    /// Rows overlaid on top of the W210 assignment.
    pub(crate) overlay_rows_applied: usize,
    /// Rows whose overlaid value was already present.
    pub(crate) overlay_rows_already_matched: usize,
    /// Same-variable overlay rows that repeated the same source value.
    pub(crate) overlay_duplicate_rows: usize,
    /// Same-variable overlay rows that disagreed on the source value.
    pub(crate) overlay_conflicting_rows: usize,
    /// Rows skipped because their variable was outside the model range.
    pub(crate) overlay_rows_out_of_range: usize,
    /// Original clauses scanned after the overlay.
    pub(crate) original_clauses_checked: usize,
    /// Falsified original clauses after the overlay.
    pub(crate) residual_falsified_count: usize,
    /// Original W210 residual clauses repaired by the overlay.
    pub(crate) repaired_original_residual_count: usize,
    /// Original W210 residual clauses still falsified after the overlay.
    pub(crate) remaining_original_residual_count: usize,
    /// Newly falsified clauses outside the original W210 residual set.
    pub(crate) new_residual_count: usize,
    /// First newly falsified clause, if any.
    pub(crate) first_new_residual_clause: Option<usize>,
    /// Falsified original clause IDs after the overlay.
    pub(crate) residual_clause_ids: Vec<usize>,
    /// True only if the overlaid assignment passed full original-DIMACS validation.
    pub(crate) validation_passed: bool,
    /// Hard false in this audit helper.
    pub(crate) route_admitted: bool,
    /// Hard false in this audit helper.
    pub(crate) sat_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) model_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) proof_output_authority: bool,
    /// Hard false in this audit helper.
    pub(crate) solver_verdict_authority: bool,
}

impl CircuitW210ResidualSourceWitnessReplayAudit {
    /// True only when every authority bit remains absent.
    pub(crate) const fn authority_is_absent(&self) -> bool {
        !self.route_admitted
            && !self.sat_output_authority
            && !self.model_output_authority
            && !self.proof_output_authority
            && !self.solver_verdict_authority
    }
}

/// Full original-DIMACS residual diagnostics for a candidate assignment.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CircuitModelResidualReport {
    /// Original DIMACS variable count expected by the formula.
    pub(crate) original_model_vars: usize,
    /// Candidate assignment length.
    pub(crate) assignment_len: usize,
    /// Variables still unassigned.
    pub(crate) missing_values: usize,
    /// First unassigned variable, if any.
    pub(crate) first_missing_var: Option<usize>,
    /// Original clauses scanned.
    pub(crate) original_clauses_checked: usize,
    /// Number of falsified original clauses.
    pub(crate) residual_falsified_count: usize,
    /// First falsified original clause, if any.
    pub(crate) first_residual_clause: Option<usize>,
    /// All falsified original clause IDs.
    pub(crate) residual_clause_ids: Vec<usize>,
    /// True when the candidate assignment length and values are complete.
    pub(crate) assignment_complete: bool,
    /// True when the complete assignment satisfies all original clauses.
    pub(crate) validation_passed: bool,
}

/// Combine parsed W210 ledgers and audit the resulting assignment surface.
///
/// The result is diagnostic-only. It deliberately returns counters and
/// residuals, not a SAT model or route authority.
pub(crate) fn audit_w210_source_frame_value_ledgers(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    frontier: &CircuitParsedSourceFrameValueLedger,
    scc_choice: &CircuitParsedSourceFrameValueLedger,
    forced_gate: &CircuitParsedSourceFrameValueLedger,
) -> Result<CircuitW210ValueLedgerAudit, CircuitW210ValueLedgerAuditError> {
    let (assignment, audit) =
        build_w210_value_ledger_assignment(num_vars, frontier, scc_choice, forced_gate)?;
    Ok(finalize_w210_value_ledger_audit(
        num_vars,
        clauses,
        &assignment,
        audit,
    ))
}

fn build_w210_value_ledger_assignment(
    num_vars: usize,
    frontier: &CircuitParsedSourceFrameValueLedger,
    scc_choice: &CircuitParsedSourceFrameValueLedger,
    forced_gate: &CircuitParsedSourceFrameValueLedger,
) -> Result<(Vec<Option<bool>>, CircuitW210ValueLedgerAudit), CircuitW210ValueLedgerAuditError> {
    require_w210_ledger_kind(
        "frontier",
        CircuitSourceFrameValueLedgerKind::W210Frontier,
        frontier.kind,
    )?;
    require_w210_ledger_kind(
        "scc_choice",
        CircuitSourceFrameValueLedgerKind::W210SccChoice,
        scc_choice.kind,
    )?;
    require_w210_ledger_kind(
        "forced_gate",
        CircuitSourceFrameValueLedgerKind::W210ForcedGate,
        forced_gate.kind,
    )?;

    let mut audit = CircuitW210ValueLedgerAudit::default();
    let mut assignment = vec![None; num_vars];
    for row in frontier
        .rows
        .iter()
        .chain(scc_choice.rows.iter())
        .chain(forced_gate.rows.iter())
    {
        audit.rows_seen += 1;
        let var = row.value.var;
        if var >= num_vars {
            audit.conflicting_rows += 1;
            continue;
        }
        if let Some(existing) = assignment[var] {
            if existing == row.value.value {
                audit.duplicate_same_value_rows += 1;
            } else {
                audit.conflicting_rows += 1;
            }
            continue;
        }
        assignment[var] = Some(row.value.value);
        audit.rows_accepted += 1;
    }

    Ok((assignment, audit))
}

fn finalize_w210_value_ledger_audit(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    assignment: &[Option<bool>],
    mut audit: CircuitW210ValueLedgerAudit,
) -> CircuitW210ValueLedgerAudit {
    let residual = diagnose_original_dimacs_assignment(num_vars, clauses, assignment);
    audit.covered_vars = assignment.iter().filter(|value| value.is_some()).count();
    audit.missing_vars = residual.missing_values;
    audit.first_missing_var = residual.first_missing_var;
    audit.original_clauses_checked = residual.original_clauses_checked;
    audit.residual_falsified_count = residual.residual_falsified_count;
    audit.first_residual_clause = residual.first_residual_clause;
    audit.residual_clause_ids = residual.residual_clause_ids;
    audit.assignment_complete = residual.assignment_complete;
    audit.validation_passed = audit.conflicting_rows == 0 && residual.validation_passed;
    audit
}

#[derive(Debug)]
struct W210ResidualRepairCandidateSet {
    assignment: Vec<Option<bool>>,
    value_ledger_audit: CircuitW210ValueLedgerAudit,
    rows_without_clause_witness: usize,
    rows_without_flip_literal: usize,
    candidates: Vec<CircuitW210ResidualRepairCandidate>,
}

/// Audit local W210 residual-clause repair candidates without returning a model.
///
/// Each candidate flips one W210 row only when the row names an original clause
/// containing the literal that the flipped value would satisfy. Every candidate
/// is checked against the full original CNF.
pub(crate) fn audit_w210_residual_repair_candidates(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    frontier: &CircuitParsedSourceFrameValueLedger,
    scc_choice: &CircuitParsedSourceFrameValueLedger,
    forced_gate: &CircuitParsedSourceFrameValueLedger,
) -> Result<CircuitW210ResidualRepairAudit, CircuitW210ValueLedgerAuditError> {
    let W210ResidualRepairCandidateSet {
        value_ledger_audit,
        rows_without_clause_witness,
        rows_without_flip_literal,
        candidates,
        ..
    } = collect_w210_residual_repair_candidates(
        num_vars,
        clauses,
        frontier,
        scc_choice,
        forced_gate,
    )?;
    let baseline_residual_count = value_ledger_audit.residual_falsified_count;

    let mut audit = CircuitW210ResidualRepairAudit {
        rows_seen: value_ledger_audit.rows_seen,
        best_residual_falsified_count: baseline_residual_count,
        best_remaining_original_residual_count: baseline_residual_count,
        value_ledger_audit,
        route_admitted: false,
        sat_output_authority: false,
        model_output_authority: false,
        proof_output_authority: false,
        solver_verdict_authority: false,
        rows_without_clause_witness,
        rows_without_flip_literal,
        candidate_rows: 0,
        improving_candidates: 0,
        plateau_candidates: 0,
        worsening_candidates: 0,
        best_repaired_original_residual_count: 0,
        best_candidate: None,
        validation_passed: false,
    };

    for candidate in candidates {
        audit.candidate_rows += 1;
        if candidate.residual_falsified_count < baseline_residual_count {
            audit.improving_candidates += 1;
        } else if candidate.residual_falsified_count == baseline_residual_count {
            audit.plateau_candidates += 1;
        } else {
            audit.worsening_candidates += 1;
        }
        audit.validation_passed |= candidate.validation_passed;
        if w210_residual_repair_candidate_is_better(
            &candidate,
            audit.best_candidate.as_ref(),
            audit.best_residual_falsified_count,
            audit.best_remaining_original_residual_count,
        ) {
            audit.best_residual_falsified_count = candidate.residual_falsified_count;
            audit.best_repaired_original_residual_count =
                candidate.repaired_original_residual_count;
            audit.best_remaining_original_residual_count =
                candidate.remaining_original_residual_count;
            audit.best_candidate = Some(candidate);
        }
    }

    Ok(audit)
}

/// Audit two-row W210 residual-clause repair candidates without returning a model.
///
/// The pair search is intentionally bounded to rows that already passed the
/// single-row clause-witness filter. Every pair is checked against the full
/// original CNF, and authority remains absent even if a diagnostic pair
/// satisfies the formula.
pub(crate) fn audit_w210_residual_repair_pair_candidates(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    frontier: &CircuitParsedSourceFrameValueLedger,
    scc_choice: &CircuitParsedSourceFrameValueLedger,
    forced_gate: &CircuitParsedSourceFrameValueLedger,
) -> Result<CircuitW210ResidualRepairPairAudit, CircuitW210ValueLedgerAuditError> {
    let W210ResidualRepairCandidateSet {
        assignment,
        value_ledger_audit,
        candidates,
        ..
    } = collect_w210_residual_repair_candidates(
        num_vars,
        clauses,
        frontier,
        scc_choice,
        forced_gate,
    )?;
    let baseline_residual_count = value_ledger_audit.residual_falsified_count;
    let baseline_residual_ids = value_ledger_audit.residual_clause_ids.clone();

    let mut audit = CircuitW210ResidualRepairPairAudit {
        single_candidate_rows: candidates.len(),
        best_residual_falsified_count: baseline_residual_count,
        best_remaining_original_residual_count: baseline_residual_count,
        best_new_residual_count: 0,
        value_ledger_audit,
        route_admitted: false,
        sat_output_authority: false,
        model_output_authority: false,
        proof_output_authority: false,
        solver_verdict_authority: false,
        same_var_pairs_skipped: 0,
        pair_candidates: 0,
        improving_pairs: 0,
        plateau_pairs: 0,
        worsening_pairs: 0,
        best_repaired_original_residual_count: 0,
        best_pair: None,
        validation_passed: false,
    };

    for first_idx in 0..candidates.len() {
        let first = &candidates[first_idx];
        for second in &candidates[first_idx + 1..] {
            if first.var == second.var {
                audit.same_var_pairs_skipped += 1;
                continue;
            }

            let mut candidate_assignment = assignment.clone();
            candidate_assignment[first.var] = Some(first.to_value);
            candidate_assignment[second.var] = Some(second.to_value);
            let residual =
                diagnose_original_dimacs_assignment(num_vars, clauses, &candidate_assignment);
            let remaining_original_residual_count =
                count_sorted_intersection(&baseline_residual_ids, &residual.residual_clause_ids);
            let repaired_original_residual_count =
                baseline_residual_count.saturating_sub(remaining_original_residual_count);
            let new_residual_count = residual
                .residual_falsified_count
                .saturating_sub(remaining_original_residual_count);
            let candidate = CircuitW210ResidualRepairPairCandidate {
                first: first.into(),
                second: second.into(),
                residual_falsified_count: residual.residual_falsified_count,
                repaired_original_residual_count,
                remaining_original_residual_count,
                new_residual_count,
                first_new_residual_clause: first_sorted_difference(
                    &residual.residual_clause_ids,
                    &baseline_residual_ids,
                ),
                validation_passed: residual.validation_passed,
            };

            audit.pair_candidates += 1;
            if candidate.residual_falsified_count < baseline_residual_count {
                audit.improving_pairs += 1;
            } else if candidate.residual_falsified_count == baseline_residual_count {
                audit.plateau_pairs += 1;
            } else {
                audit.worsening_pairs += 1;
            }
            audit.validation_passed |= candidate.validation_passed;
            if w210_residual_repair_pair_candidate_is_better(
                &candidate,
                audit.best_pair.as_ref(),
                audit.best_residual_falsified_count,
                audit.best_remaining_original_residual_count,
                audit.best_new_residual_count,
            ) {
                audit.best_residual_falsified_count = candidate.residual_falsified_count;
                audit.best_repaired_original_residual_count =
                    candidate.repaired_original_residual_count;
                audit.best_remaining_original_residual_count =
                    candidate.remaining_original_residual_count;
                audit.best_new_residual_count = candidate.new_residual_count;
                audit.best_pair = Some(candidate);
            }
        }
    }

    Ok(audit)
}

/// Audit three-row W210 residual-clause repair candidates without returning a model.
///
/// The triple search is intentionally bounded to rows that already passed the
/// single-row clause-witness filter. Every triple is checked against the full
/// original CNF, and authority remains absent even if a diagnostic triple
/// satisfies the formula.
pub(crate) fn audit_w210_residual_repair_triple_candidates(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    frontier: &CircuitParsedSourceFrameValueLedger,
    scc_choice: &CircuitParsedSourceFrameValueLedger,
    forced_gate: &CircuitParsedSourceFrameValueLedger,
) -> Result<CircuitW210ResidualRepairTripleAudit, CircuitW210ValueLedgerAuditError> {
    let W210ResidualRepairCandidateSet {
        assignment,
        value_ledger_audit,
        candidates,
        ..
    } = collect_w210_residual_repair_candidates(
        num_vars,
        clauses,
        frontier,
        scc_choice,
        forced_gate,
    )?;
    let baseline_residual_count = value_ledger_audit.residual_falsified_count;
    let baseline_residual_ids = value_ledger_audit.residual_clause_ids.clone();

    let mut audit = CircuitW210ResidualRepairTripleAudit {
        single_candidate_rows: candidates.len(),
        best_residual_falsified_count: baseline_residual_count,
        best_remaining_original_residual_count: baseline_residual_count,
        best_new_residual_count: 0,
        value_ledger_audit,
        route_admitted: false,
        sat_output_authority: false,
        model_output_authority: false,
        proof_output_authority: false,
        solver_verdict_authority: false,
        same_var_triples_skipped: 0,
        triple_candidates: 0,
        improving_triples: 0,
        plateau_triples: 0,
        worsening_triples: 0,
        best_repaired_original_residual_count: 0,
        best_triple: None,
        validation_passed: false,
    };

    for first_idx in 0..candidates.len() {
        let first = &candidates[first_idx];
        for second_idx in first_idx + 1..candidates.len() {
            let second = &candidates[second_idx];
            for third in &candidates[second_idx + 1..] {
                if first.var == second.var || first.var == third.var || second.var == third.var {
                    audit.same_var_triples_skipped += 1;
                    continue;
                }

                let mut candidate_assignment = assignment.clone();
                candidate_assignment[first.var] = Some(first.to_value);
                candidate_assignment[second.var] = Some(second.to_value);
                candidate_assignment[third.var] = Some(third.to_value);
                let residual =
                    diagnose_original_dimacs_assignment(num_vars, clauses, &candidate_assignment);
                let remaining_original_residual_count = count_sorted_intersection(
                    &baseline_residual_ids,
                    &residual.residual_clause_ids,
                );
                let repaired_original_residual_count =
                    baseline_residual_count.saturating_sub(remaining_original_residual_count);
                let new_residual_count = residual
                    .residual_falsified_count
                    .saturating_sub(remaining_original_residual_count);
                let candidate = CircuitW210ResidualRepairTripleCandidate {
                    first: first.into(),
                    second: second.into(),
                    third: third.into(),
                    residual_falsified_count: residual.residual_falsified_count,
                    repaired_original_residual_count,
                    remaining_original_residual_count,
                    new_residual_count,
                    first_new_residual_clause: first_sorted_difference(
                        &residual.residual_clause_ids,
                        &baseline_residual_ids,
                    ),
                    validation_passed: residual.validation_passed,
                };

                audit.triple_candidates += 1;
                if candidate.residual_falsified_count < baseline_residual_count {
                    audit.improving_triples += 1;
                } else if candidate.residual_falsified_count == baseline_residual_count {
                    audit.plateau_triples += 1;
                } else {
                    audit.worsening_triples += 1;
                }
                audit.validation_passed |= candidate.validation_passed;
                if w210_residual_repair_triple_candidate_is_better(
                    &candidate,
                    audit.best_triple.as_ref(),
                    audit.best_residual_falsified_count,
                    audit.best_remaining_original_residual_count,
                    audit.best_new_residual_count,
                ) {
                    audit.best_residual_falsified_count = candidate.residual_falsified_count;
                    audit.best_repaired_original_residual_count =
                        candidate.repaired_original_residual_count;
                    audit.best_remaining_original_residual_count =
                        candidate.remaining_original_residual_count;
                    audit.best_new_residual_count = candidate.new_residual_count;
                    audit.best_triple = Some(candidate);
                }
            }
        }
    }

    Ok(audit)
}

/// Audit whether residual-source witnesses replay into a valid original model.
///
/// The overlay uses only opposite-literal rows that are already bound to W159
/// residual clauses. It returns blocker counters only; even a satisfying overlay
/// would still need an artifact-backed original-DIMACS authority before route
/// admission.
pub(crate) fn audit_w210_residual_source_witness_replay(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    frontier: &CircuitParsedSourceFrameValueLedger,
    scc_choice: &CircuitParsedSourceFrameValueLedger,
    forced_gate: &CircuitParsedSourceFrameValueLedger,
) -> Result<CircuitW210ResidualSourceWitnessReplayAudit, CircuitW210ValueLedgerAuditError> {
    let (mut assignment, audit_seed) =
        build_w210_value_ledger_assignment(num_vars, frontier, scc_choice, forced_gate)?;
    let value_ledger_audit =
        finalize_w210_value_ledger_audit(num_vars, clauses, &assignment, audit_seed);
    let baseline_residual_ids = value_ledger_audit.residual_clause_ids.clone();
    let baseline_residual_count = value_ledger_audit.residual_falsified_count;
    let residual_source_witness_rows =
        derive_w210_residual_source_witness_rows(clauses, frontier, scc_choice, forced_gate)?;

    let mut frontier_rows = 0;
    let mut scc_choice_rows = 0;
    let mut forced_gate_rows = 0;
    let mut overlay_rows_applied = 0;
    let mut overlay_rows_already_matched = 0;
    let mut overlay_duplicate_rows = 0;
    let mut overlay_conflicting_rows = 0;
    let mut overlay_rows_out_of_range = 0;
    let mut overlay_assignment = vec![None; num_vars];

    for source_row in &residual_source_witness_rows.rows {
        match source_row.family {
            CircuitSourceFrameFamily::W210Frontier => frontier_rows += 1,
            CircuitSourceFrameFamily::W210SccChoice => scc_choice_rows += 1,
            CircuitSourceFrameFamily::ForcedGateReplayBridge => forced_gate_rows += 1,
            _ => {}
        }

        let Some(value_slot) = assignment.get_mut(source_row.var) else {
            overlay_rows_out_of_range += 1;
            continue;
        };
        let Some(overlay_slot) = overlay_assignment.get_mut(source_row.var) else {
            overlay_rows_out_of_range += 1;
            continue;
        };
        if let Some(existing_overlay) = *overlay_slot {
            if existing_overlay == source_row.source_value {
                overlay_duplicate_rows += 1;
            } else {
                overlay_conflicting_rows += 1;
            }
            continue;
        }

        *overlay_slot = Some(source_row.source_value);
        if *value_slot == Some(source_row.source_value) {
            overlay_rows_already_matched += 1;
        } else {
            *value_slot = Some(source_row.source_value);
            overlay_rows_applied += 1;
        }
    }

    let residual = diagnose_original_dimacs_assignment(num_vars, clauses, &assignment);
    let remaining_original_residual_count =
        count_sorted_intersection(&baseline_residual_ids, &residual.residual_clause_ids);
    let repaired_original_residual_count =
        baseline_residual_count.saturating_sub(remaining_original_residual_count);
    let new_residual_count = residual
        .residual_falsified_count
        .saturating_sub(remaining_original_residual_count);

    Ok(CircuitW210ResidualSourceWitnessReplayAudit {
        value_ledger_audit,
        residual_source_witness_row_audit: residual_source_witness_rows.audit,
        frontier_rows,
        scc_choice_rows,
        forced_gate_rows,
        overlay_rows_applied,
        overlay_rows_already_matched,
        overlay_duplicate_rows,
        overlay_conflicting_rows,
        overlay_rows_out_of_range,
        original_clauses_checked: residual.original_clauses_checked,
        residual_falsified_count: residual.residual_falsified_count,
        repaired_original_residual_count,
        remaining_original_residual_count,
        new_residual_count,
        first_new_residual_clause: first_sorted_difference(
            &residual.residual_clause_ids,
            &baseline_residual_ids,
        ),
        residual_clause_ids: residual.residual_clause_ids,
        validation_passed: residual.validation_passed
            && overlay_conflicting_rows == 0
            && overlay_rows_out_of_range == 0,
        route_admitted: false,
        sat_output_authority: false,
        model_output_authority: false,
        proof_output_authority: false,
        solver_verdict_authority: false,
    })
}

fn collect_w210_residual_repair_candidates(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    frontier: &CircuitParsedSourceFrameValueLedger,
    scc_choice: &CircuitParsedSourceFrameValueLedger,
    forced_gate: &CircuitParsedSourceFrameValueLedger,
) -> Result<W210ResidualRepairCandidateSet, CircuitW210ValueLedgerAuditError> {
    let (assignment, audit_seed) =
        build_w210_value_ledger_assignment(num_vars, frontier, scc_choice, forced_gate)?;
    let value_ledger_audit =
        finalize_w210_value_ledger_audit(num_vars, clauses, &assignment, audit_seed);
    let baseline_residual_count = value_ledger_audit.residual_falsified_count;
    let baseline_residual_ids = value_ledger_audit.residual_clause_ids.clone();
    let mut rows_without_clause_witness = 0;
    let mut rows_without_flip_literal = 0;
    let mut candidates = Vec::new();

    for ledger in [frontier, scc_choice, forced_gate] {
        for row in &ledger.rows {
            if row.remaining_clause_ids_1_based.is_empty() {
                rows_without_clause_witness += 1;
                continue;
            }
            if assignment.get(row.value.var).copied().flatten() != Some(row.value.value) {
                rows_without_flip_literal += 1;
                continue;
            }
            let Some(clause_id) = w210_residual_flip_clause_id(clauses, row) else {
                rows_without_flip_literal += 1;
                continue;
            };

            let mut candidate_assignment = assignment.clone();
            candidate_assignment[row.value.var] = Some(!row.value.value);
            let residual =
                diagnose_original_dimacs_assignment(num_vars, clauses, &candidate_assignment);
            let remaining_original_residual_count =
                count_sorted_intersection(&baseline_residual_ids, &residual.residual_clause_ids);
            let repaired_original_residual_count =
                baseline_residual_count.saturating_sub(remaining_original_residual_count);
            let new_residual_count = residual
                .residual_falsified_count
                .saturating_sub(remaining_original_residual_count);
            candidates.push(CircuitW210ResidualRepairCandidate {
                ledger_kind: ledger.kind,
                source_row_id: row.source_row_id,
                var: row.value.var,
                from_value: row.value.value,
                to_value: !row.value.value,
                clause_id,
                residual_falsified_count: residual.residual_falsified_count,
                repaired_original_residual_count,
                remaining_original_residual_count,
                new_residual_count,
                first_new_residual_clause: first_sorted_difference(
                    &residual.residual_clause_ids,
                    &baseline_residual_ids,
                ),
                validation_passed: residual.validation_passed,
            });
        }
    }

    Ok(W210ResidualRepairCandidateSet {
        assignment,
        value_ledger_audit,
        rows_without_clause_witness,
        rows_without_flip_literal,
        candidates,
    })
}

fn w210_residual_flip_clause_id(
    clauses: &[Vec<Literal>],
    row: &CircuitSourceFrameValueLedgerRow,
) -> Option<usize> {
    let flip_literal = literal_for_source_frame_value(CircuitSourceFrameValue {
        var: row.value.var,
        value: !row.value.value,
        family: row.value.family,
    });
    for &clause_id_1_based in &row.remaining_clause_ids_1_based {
        let Some(clause_id) = clause_id_1_based.checked_sub(1) else {
            continue;
        };
        let Some(clause) = clauses.get(clause_id) else {
            continue;
        };
        if clause.contains(&flip_literal) {
            return Some(clause_id);
        }
    }
    None
}

fn w210_residual_repair_candidate_is_better(
    candidate: &CircuitW210ResidualRepairCandidate,
    best_candidate: Option<&CircuitW210ResidualRepairCandidate>,
    best_residual_falsified_count: usize,
    best_remaining_original_residual_count: usize,
) -> bool {
    let candidate_key = (
        candidate.residual_falsified_count,
        candidate.remaining_original_residual_count,
        candidate.new_residual_count,
        candidate.var,
        candidate.source_row_id,
        candidate.clause_id,
    );
    let best_key = best_candidate.map_or(
        (
            best_residual_falsified_count,
            best_remaining_original_residual_count,
            0,
            usize::MAX,
            u64::MAX,
            usize::MAX,
        ),
        |best| {
            (
                best.residual_falsified_count,
                best.remaining_original_residual_count,
                best.new_residual_count,
                best.var,
                best.source_row_id,
                best.clause_id,
            )
        },
    );
    candidate_key < best_key
}

fn w210_residual_repair_pair_candidate_is_better(
    candidate: &CircuitW210ResidualRepairPairCandidate,
    best_candidate: Option<&CircuitW210ResidualRepairPairCandidate>,
    best_residual_falsified_count: usize,
    best_remaining_original_residual_count: usize,
    best_new_residual_count: usize,
) -> bool {
    let candidate_key = (
        candidate.residual_falsified_count,
        candidate.remaining_original_residual_count,
        candidate.new_residual_count,
        candidate.first.var,
        candidate.first.source_row_id,
        candidate.first.clause_id,
        candidate.second.var,
        candidate.second.source_row_id,
        candidate.second.clause_id,
    );
    let best_key = best_candidate.map_or(
        (
            best_residual_falsified_count,
            best_remaining_original_residual_count,
            best_new_residual_count,
            usize::MAX,
            u64::MAX,
            usize::MAX,
            usize::MAX,
            u64::MAX,
            usize::MAX,
        ),
        |best| {
            (
                best.residual_falsified_count,
                best.remaining_original_residual_count,
                best.new_residual_count,
                best.first.var,
                best.first.source_row_id,
                best.first.clause_id,
                best.second.var,
                best.second.source_row_id,
                best.second.clause_id,
            )
        },
    );
    candidate_key < best_key
}

fn w210_residual_repair_triple_candidate_is_better(
    candidate: &CircuitW210ResidualRepairTripleCandidate,
    best_candidate: Option<&CircuitW210ResidualRepairTripleCandidate>,
    best_residual_falsified_count: usize,
    best_remaining_original_residual_count: usize,
    best_new_residual_count: usize,
) -> bool {
    let candidate_key = (
        candidate.residual_falsified_count,
        candidate.remaining_original_residual_count,
        candidate.new_residual_count,
        candidate.first.var,
        candidate.first.source_row_id,
        candidate.first.clause_id,
        candidate.second.var,
        candidate.second.source_row_id,
        candidate.second.clause_id,
        candidate.third.var,
        candidate.third.source_row_id,
        candidate.third.clause_id,
    );
    let best_key = best_candidate.map_or(
        (
            best_residual_falsified_count,
            best_remaining_original_residual_count,
            best_new_residual_count,
            usize::MAX,
            u64::MAX,
            usize::MAX,
            usize::MAX,
            u64::MAX,
            usize::MAX,
            usize::MAX,
            u64::MAX,
            usize::MAX,
        ),
        |best| {
            (
                best.residual_falsified_count,
                best.remaining_original_residual_count,
                best.new_residual_count,
                best.first.var,
                best.first.source_row_id,
                best.first.clause_id,
                best.second.var,
                best.second.source_row_id,
                best.second.clause_id,
                best.third.var,
                best.third.source_row_id,
                best.third.clause_id,
            )
        },
    );
    candidate_key < best_key
}

fn count_sorted_intersection(left: &[usize], right: &[usize]) -> usize {
    let mut left_idx = 0;
    let mut right_idx = 0;
    let mut count = 0;
    while left_idx < left.len() && right_idx < right.len() {
        match left[left_idx].cmp(&right[right_idx]) {
            std::cmp::Ordering::Less => left_idx += 1,
            std::cmp::Ordering::Equal => {
                count += 1;
                left_idx += 1;
                right_idx += 1;
            }
            std::cmp::Ordering::Greater => right_idx += 1,
        }
    }
    count
}

fn first_sorted_difference(left: &[usize], right: &[usize]) -> Option<usize> {
    let mut right_idx = 0;
    for &left_value in left {
        while right_idx < right.len() && right[right_idx] < left_value {
            right_idx += 1;
        }
        if right.get(right_idx).copied() != Some(left_value) {
            return Some(left_value);
        }
    }
    None
}

/// Derive clause-bound source-frame rows from parsed W210 value ledgers.
///
/// This helper does not validate or emit a model. It only converts a W210 value
/// into a source-frame row when W210 names an original clause containing the
/// value-consistent literal, or when the value-consistent literal can be rebound
/// to another original clause. Opposite-literal residual rows remain
/// diagnostic-only through [`derive_w210_residual_source_witness_rows`] and
/// grant no model/proof authority.
pub(crate) fn derive_w210_source_frame_rows(
    clauses: &[Vec<Literal>],
    frontier: &CircuitParsedSourceFrameValueLedger,
    scc_choice: &CircuitParsedSourceFrameValueLedger,
    forced_gate: &CircuitParsedSourceFrameValueLedger,
) -> Result<CircuitW210SourceFrameRows, CircuitW210ValueLedgerAuditError> {
    require_w210_ledger_kind(
        "frontier",
        CircuitSourceFrameValueLedgerKind::W210Frontier,
        frontier.kind,
    )?;
    require_w210_ledger_kind(
        "scc_choice",
        CircuitSourceFrameValueLedgerKind::W210SccChoice,
        scc_choice.kind,
    )?;
    require_w210_ledger_kind(
        "forced_gate",
        CircuitSourceFrameValueLedgerKind::W210ForcedGate,
        forced_gate.kind,
    )?;

    let mut derived = CircuitW210SourceFrameRows::default();
    for ledger in [frontier, scc_choice, forced_gate] {
        for row in &ledger.rows {
            derived.audit.rows_seen += 1;
            match derive_w210_authorized_source_frame_row(clauses, ledger.kind, row) {
                Ok(derived_row) => {
                    if derived_row.row.source_value != row.value.value {
                        derived.audit.residual_opposite_literal_rows += 1;
                    }
                    if derived_row.reconstructed_clause_witness {
                        derived.audit.reconstructed_clause_witness_rows += 1;
                    }
                    if derived_row.stale_clause_witness_rebound {
                        derived.audit.stale_clause_witness_rebound_rows += 1;
                    }
                    if derived_row.unreferenced_original_var {
                        derived.audit.unreferenced_original_var_rows += 1;
                    }
                    derived.rows.push(derived_row.row);
                    derived.audit.rows_materialized += 1;
                }
                Err(rejection) => {
                    record_w210_source_frame_row_rejection(&mut derived.audit, rejection);
                }
            }
        }
    }
    Ok(derived)
}

fn derive_w210_authorized_source_frame_row(
    clauses: &[Vec<Literal>],
    kind: CircuitSourceFrameValueLedgerKind,
    row: &CircuitSourceFrameValueLedgerRow,
) -> Result<CircuitDerivedW210SourceFrameRow, CircuitW210SourceFrameRowRejection> {
    let value_literal = literal_for_source_frame_value(row.value);
    match derive_w210_source_frame_row(clauses, kind, row) {
        Ok(source_row) => Ok(source_row),
        Err(rejection @ CircuitW210SourceFrameRowRejection::LiteralMissingFromClause { .. }) => {
            reconstruct_w210_source_frame_row_from_original_clauses(
                clauses,
                kind,
                row,
                value_literal,
                CircuitW210SourceFrameReconstruction::StaleClauseWitness,
            )
            .or(Err(rejection))
        }
        Err(rejection) => Err(rejection),
    }
}

/// Derive diagnostic residual-source rows from opposite literals in W210 clauses.
///
/// This helper does not grant route authority. It records which stale W210 rows
/// can be rebound to an original residual clause by using the opposite literal,
/// leaving strict route admission on `derive_w210_source_frame_rows`.
pub(crate) fn derive_w210_residual_source_witness_rows(
    clauses: &[Vec<Literal>],
    frontier: &CircuitParsedSourceFrameValueLedger,
    scc_choice: &CircuitParsedSourceFrameValueLedger,
    forced_gate: &CircuitParsedSourceFrameValueLedger,
) -> Result<CircuitW210SourceFrameRows, CircuitW210ValueLedgerAuditError> {
    require_w210_ledger_kind(
        "frontier",
        CircuitSourceFrameValueLedgerKind::W210Frontier,
        frontier.kind,
    )?;
    require_w210_ledger_kind(
        "scc_choice",
        CircuitSourceFrameValueLedgerKind::W210SccChoice,
        scc_choice.kind,
    )?;
    require_w210_ledger_kind(
        "forced_gate",
        CircuitSourceFrameValueLedgerKind::W210ForcedGate,
        forced_gate.kind,
    )?;

    let mut derived = CircuitW210SourceFrameRows::default();
    for ledger in [frontier, scc_choice, forced_gate] {
        for row in &ledger.rows {
            derived.audit.rows_seen += 1;
            match derive_w210_residual_source_witness_row(clauses, ledger.kind, row) {
                Ok(source_row) => {
                    derived.rows.push(source_row);
                    derived.audit.rows_materialized += 1;
                    derived.audit.residual_opposite_literal_rows += 1;
                }
                Err(rejection) => {
                    record_w210_source_frame_row_rejection(&mut derived.audit, rejection);
                }
            }
        }
    }
    Ok(derived)
}

/// Build a result-silent W210 route-admission blocker packet.
///
/// The packet first preserves the combined W210 value-ledger residual audit,
/// then derives clause-bound source rows. Derived rows are fed into the
/// source-frame audit only when every W210 value row has an original-clause
/// witness; otherwise stale or unbound rows stop before materialization.
pub(crate) fn audit_w210_route_admission_blocker(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    frontier: &CircuitParsedSourceFrameValueLedger,
    scc_choice: &CircuitParsedSourceFrameValueLedger,
    forced_gate: &CircuitParsedSourceFrameValueLedger,
) -> Result<CircuitW210RouteAdmissionAudit, CircuitW210ValueLedgerAuditError> {
    let value_ledger_audit = audit_w210_source_frame_value_ledgers(
        num_vars,
        clauses,
        frontier,
        scc_choice,
        forced_gate,
    )?;
    let derived = derive_w210_source_frame_rows(clauses, frontier, scc_choice, forced_gate)?;

    let (source_frame_audit, source_frame_audit_ran) = if derived.audit.rows_rejected == 0 {
        (
            audit_source_frame_rows(num_vars, clauses, &derived.rows),
            true,
        )
    } else {
        (CircuitSourceFrameAudit::default(), false)
    };

    let original_dimacs_validation_passed = value_ledger_audit.validation_passed
        && derived.audit.rows_rejected == 0
        && source_frame_audit.validation_passed;
    let blocker =
        w210_route_admission_blocker(&value_ledger_audit, &derived.audit, &source_frame_audit);

    Ok(CircuitW210RouteAdmissionAudit {
        value_ledger_audit,
        source_frame_row_audit: derived.audit,
        source_frame_audit,
        source_frame_audit_ran,
        original_dimacs_validation_passed,
        route_admission_status: CircuitW210RouteAdmissionStatus::Blocked(blocker),
        route_admitted: false,
        sat_output_authority: false,
        model_output_authority: false,
        proof_output_authority: false,
        solver_verdict_authority: false,
    })
}

/// Audit W210 source-witness authority with an explicit original-DIMACS verdict.
///
/// This helper is fail-closed: the W210 value ledger and derived source-frame
/// rows must validate the original DIMACS formula before the caller's
/// checker-backed model/proof verdict is considered. Unsupported rows remain
/// blocked even if a caller supplies an accepted verdict.
pub(crate) fn audit_w210_source_witness_authority(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    frontier: &CircuitParsedSourceFrameValueLedger,
    scc_choice: &CircuitParsedSourceFrameValueLedger,
    forced_gate: &CircuitParsedSourceFrameValueLedger,
    expected_authority_kind: CircuitW210OriginalDimacsAuthorityKind,
    authority_verdict: Option<CircuitW210OriginalDimacsAuthorityVerdict>,
) -> Result<CircuitW210SourceWitnessAuthorityAudit, CircuitW210ValueLedgerAuditError> {
    let route_admission_audit =
        audit_w210_route_admission_blocker(num_vars, clauses, frontier, scc_choice, forced_gate)?;
    let residual_source_witness_rows =
        derive_w210_residual_source_witness_rows(clauses, frontier, scc_choice, forced_gate)?;
    let route_status = route_admission_audit.route_admission_status;
    let supplied_authority_kind =
        authority_verdict.map(CircuitW210OriginalDimacsAuthorityVerdict::kind);
    let original_dimacs_authority_checked =
        authority_verdict.is_some_and(CircuitW210OriginalDimacsAuthorityVerdict::is_checked);
    let original_dimacs_authority_accepted =
        authority_verdict.is_some_and(CircuitW210OriginalDimacsAuthorityVerdict::is_accepted);

    let mut audit = CircuitW210SourceWitnessAuthorityAudit {
        route_admission_audit,
        residual_source_witness_row_audit: residual_source_witness_rows.audit,
        expected_authority_kind,
        supplied_authority_kind,
        original_dimacs_authority_checked,
        original_dimacs_authority_accepted,
        authority_status: CircuitW210SourceWitnessAuthorityStatus::Blocked(
            CircuitW210SourceWitnessAuthorityBlocker::OriginalDimacsAuthorityMissing,
        ),
        route_admitted: false,
        sat_output_authority: false,
        unsat_output_authority: false,
        model_output_authority: false,
        proof_output_authority: false,
        solver_verdict_authority: false,
    };

    if let CircuitW210RouteAdmissionStatus::Blocked(blocker) = route_status {
        if blocker != CircuitW210RouteAdmissionBlocker::AuthorityAbsent {
            audit.authority_status = CircuitW210SourceWitnessAuthorityStatus::Blocked(
                CircuitW210SourceWitnessAuthorityBlocker::RouteAdmission(blocker),
            );
            return Ok(audit);
        }
    }

    let Some(authority_verdict) = authority_verdict else {
        return Ok(audit);
    };
    if authority_verdict.kind() != expected_authority_kind {
        audit.authority_status = CircuitW210SourceWitnessAuthorityStatus::Blocked(
            CircuitW210SourceWitnessAuthorityBlocker::OriginalDimacsAuthorityKindMismatch,
        );
        return Ok(audit);
    }
    if !authority_verdict.is_checked() {
        audit.authority_status = CircuitW210SourceWitnessAuthorityStatus::Blocked(
            CircuitW210SourceWitnessAuthorityBlocker::OriginalDimacsAuthorityUnchecked,
        );
        return Ok(audit);
    }
    if !authority_verdict.is_accepted() {
        audit.authority_status = CircuitW210SourceWitnessAuthorityStatus::Blocked(
            CircuitW210SourceWitnessAuthorityBlocker::OriginalDimacsAuthorityRejected,
        );
        return Ok(audit);
    }

    audit.authority_status =
        CircuitW210SourceWitnessAuthorityStatus::Admitted(expected_authority_kind);
    audit.route_admitted = true;
    audit.solver_verdict_authority = true;
    match expected_authority_kind {
        CircuitW210OriginalDimacsAuthorityKind::SatModel => {
            audit.sat_output_authority = true;
            audit.model_output_authority = true;
        }
        CircuitW210OriginalDimacsAuthorityKind::UnsatProof => {
            audit.unsat_output_authority = true;
            audit.proof_output_authority = true;
        }
    }
    Ok(audit)
}

fn w210_route_admission_blocker(
    value_ledger_audit: &CircuitW210ValueLedgerAudit,
    source_row_audit: &CircuitW210SourceFrameRowAudit,
    source_frame_audit: &CircuitSourceFrameAudit,
) -> CircuitW210RouteAdmissionBlocker {
    if value_ledger_audit.conflicting_rows > 0 {
        return CircuitW210RouteAdmissionBlocker::ValueLedgerConflict;
    }
    if !value_ledger_audit.assignment_complete || value_ledger_audit.missing_vars > 0 {
        return CircuitW210RouteAdmissionBlocker::ValueLedgerIncomplete;
    }
    if value_ledger_audit.residual_falsified_count > 0 || !value_ledger_audit.validation_passed {
        return CircuitW210RouteAdmissionBlocker::ValueLedgerResidualNonZero;
    }
    if source_row_audit.rows_rejected > 0 {
        return CircuitW210RouteAdmissionBlocker::SourceFrameDerivationRejected;
    }
    if source_frame_audit_has_rejections(source_frame_audit) {
        return CircuitW210RouteAdmissionBlocker::SourceFrameRejected;
    }
    if !source_frame_audit.assignment_complete || source_frame_audit.missing_source_rows > 0 {
        return CircuitW210RouteAdmissionBlocker::SourceFrameIncomplete;
    }
    if source_frame_audit.residual_falsified_count > 0 || !source_frame_audit.validation_passed {
        return CircuitW210RouteAdmissionBlocker::SourceFrameResidualNonZero;
    }
    CircuitW210RouteAdmissionBlocker::AuthorityAbsent
}

fn source_frame_audit_has_rejections(audit: &CircuitSourceFrameAudit) -> bool {
    audit.rows_rejected > 0
        || audit.unsupported_family > 0
        || audit.var_out_of_range > 0
        || audit.literal_var_mismatch > 0
        || audit.clause_out_of_range > 0
        || audit.literal_missing_from_clause > 0
        || audit.unreferenced_var_occurs > 0
        || audit.conflicts > 0
}

fn record_w210_source_frame_row_rejection(
    audit: &mut CircuitW210SourceFrameRowAudit,
    rejection: CircuitW210SourceFrameRowRejection,
) {
    audit.rows_rejected += 1;
    match &rejection {
        CircuitW210SourceFrameRowRejection::MissingClauseWitness { .. } => {
            audit.missing_clause_witness_rows += 1;
        }
        CircuitW210SourceFrameRowRejection::ClauseOutOfRange { .. } => {
            audit.clause_out_of_range_rows += 1;
        }
        CircuitW210SourceFrameRowRejection::LiteralMissingFromClause { .. } => {
            audit.literal_missing_from_clause_rows += 1;
        }
    }
    audit.first_rejection.get_or_insert(rejection);
}

fn derive_w210_source_frame_row(
    clauses: &[Vec<Literal>],
    kind: CircuitSourceFrameValueLedgerKind,
    row: &CircuitSourceFrameValueLedgerRow,
) -> Result<CircuitDerivedW210SourceFrameRow, CircuitW210SourceFrameRowRejection> {
    let literal = literal_for_source_frame_value(row.value);
    if row.remaining_clause_ids_1_based.is_empty() {
        return reconstruct_w210_source_frame_row_from_original_clauses(
            clauses,
            kind,
            row,
            literal,
            CircuitW210SourceFrameReconstruction::MissingClauseWitness,
        );
    }

    for &clause_id_1_based in &row.remaining_clause_ids_1_based {
        let Some(clause_id) = clause_id_1_based.checked_sub(1) else {
            return Err(CircuitW210SourceFrameRowRejection::ClauseOutOfRange {
                source_row_id: row.source_row_id,
                clause_id_1_based,
            });
        };
        let Some(clause) = clauses.get(clause_id) else {
            return Err(CircuitW210SourceFrameRowRejection::ClauseOutOfRange {
                source_row_id: row.source_row_id,
                clause_id_1_based,
            });
        };
        if clause.contains(&literal) {
            return Ok(CircuitDerivedW210SourceFrameRow {
                row: CircuitSourceFrameRow {
                    source_row_id: row.source_row_id,
                    var: row.value.var,
                    literal,
                    clause_id,
                    source_value: row.value.value,
                    family: row.value.family,
                    kind: source_frame_kind_for_w210_ledger(kind),
                },
                reconstructed_clause_witness: false,
                stale_clause_witness_rebound: false,
                unreferenced_original_var: false,
            });
        }
    }

    Err(
        CircuitW210SourceFrameRowRejection::LiteralMissingFromClause {
            source_row_id: row.source_row_id,
            literal_dimacs: literal.to_dimacs(),
            clause_ids_1_based: row.remaining_clause_ids_1_based.clone(),
        },
    )
}

fn reconstruct_w210_source_frame_row_from_original_clauses(
    clauses: &[Vec<Literal>],
    kind: CircuitSourceFrameValueLedgerKind,
    row: &CircuitSourceFrameValueLedgerRow,
    literal: Literal,
    reconstruction: CircuitW210SourceFrameReconstruction,
) -> Result<CircuitDerivedW210SourceFrameRow, CircuitW210SourceFrameRowRejection> {
    for (clause_id, clause) in clauses.iter().enumerate() {
        if clause.contains(&literal) {
            return Ok(CircuitDerivedW210SourceFrameRow {
                row: CircuitSourceFrameRow {
                    source_row_id: row.source_row_id,
                    var: row.value.var,
                    literal,
                    clause_id,
                    source_value: row.value.value,
                    family: row.value.family,
                    kind: source_frame_kind_for_w210_ledger(kind),
                },
                reconstructed_clause_witness: true,
                stale_clause_witness_rebound: reconstruction
                    == CircuitW210SourceFrameReconstruction::StaleClauseWitness,
                unreferenced_original_var: false,
            });
        }
    }

    if reconstruction == CircuitW210SourceFrameReconstruction::MissingClauseWitness
        && !original_var_occurs_in_clauses(clauses, row.value.var)
    {
        return Ok(CircuitDerivedW210SourceFrameRow {
            row: CircuitSourceFrameRow {
                source_row_id: row.source_row_id,
                var: row.value.var,
                literal,
                clause_id: usize::MAX,
                source_value: row.value.value,
                family: row.value.family,
                kind: CircuitSourceFrameKind::UnreferencedOriginalValue,
            },
            reconstructed_clause_witness: false,
            stale_clause_witness_rebound: false,
            unreferenced_original_var: true,
        });
    }

    Err(CircuitW210SourceFrameRowRejection::MissingClauseWitness {
        source_row_id: row.source_row_id,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CircuitW210SourceFrameReconstruction {
    MissingClauseWitness,
    StaleClauseWitness,
}

fn original_var_occurs_in_clauses(clauses: &[Vec<Literal>], var: usize) -> bool {
    clauses
        .iter()
        .flatten()
        .any(|lit| lit.variable().index() == var)
}

fn derive_w210_residual_source_witness_row(
    clauses: &[Vec<Literal>],
    kind: CircuitSourceFrameValueLedgerKind,
    row: &CircuitSourceFrameValueLedgerRow,
) -> Result<CircuitSourceFrameRow, CircuitW210SourceFrameRowRejection> {
    if row.remaining_clause_ids_1_based.is_empty() {
        return Err(CircuitW210SourceFrameRowRejection::MissingClauseWitness {
            source_row_id: row.source_row_id,
        });
    }
    if !row.present_in_w159_remaining_clause {
        let literal = literal_for_source_frame_value(CircuitSourceFrameValue {
            value: !row.value.value,
            ..row.value
        });
        return Err(
            CircuitW210SourceFrameRowRejection::LiteralMissingFromClause {
                source_row_id: row.source_row_id,
                literal_dimacs: literal.to_dimacs(),
                clause_ids_1_based: row.remaining_clause_ids_1_based.clone(),
            },
        );
    }

    let source_value = CircuitSourceFrameValue {
        value: !row.value.value,
        ..row.value
    };
    let literal = literal_for_source_frame_value(source_value);
    for &clause_id_1_based in &row.remaining_clause_ids_1_based {
        let Some(clause_id) = clause_id_1_based.checked_sub(1) else {
            return Err(CircuitW210SourceFrameRowRejection::ClauseOutOfRange {
                source_row_id: row.source_row_id,
                clause_id_1_based,
            });
        };
        let Some(clause) = clauses.get(clause_id) else {
            return Err(CircuitW210SourceFrameRowRejection::ClauseOutOfRange {
                source_row_id: row.source_row_id,
                clause_id_1_based,
            });
        };
        if clause.contains(&literal) {
            return Ok(CircuitSourceFrameRow {
                source_row_id: row.source_row_id,
                var: source_value.var,
                literal,
                clause_id,
                source_value: source_value.value,
                family: source_value.family,
                kind: source_frame_kind_for_w210_ledger(kind),
            });
        }
    }

    Err(
        CircuitW210SourceFrameRowRejection::LiteralMissingFromClause {
            source_row_id: row.source_row_id,
            literal_dimacs: literal.to_dimacs(),
            clause_ids_1_based: row.remaining_clause_ids_1_based.clone(),
        },
    )
}

fn literal_for_source_frame_value(value: CircuitSourceFrameValue) -> Literal {
    let var = Variable(value.var as u32);
    if value.value {
        Literal::positive(var)
    } else {
        Literal::negative(var)
    }
}

fn source_frame_kind_for_w210_ledger(
    kind: CircuitSourceFrameValueLedgerKind,
) -> CircuitSourceFrameKind {
    match kind {
        CircuitSourceFrameValueLedgerKind::W210Frontier => CircuitSourceFrameKind::FrontierValue,
        CircuitSourceFrameValueLedgerKind::W210SccChoice => CircuitSourceFrameKind::SccChoiceValue,
        CircuitSourceFrameValueLedgerKind::W210ForcedGate => {
            CircuitSourceFrameKind::ForcedGateReplayBridge
        }
    }
}

fn require_w210_ledger_kind(
    role: &'static str,
    expected: CircuitSourceFrameValueLedgerKind,
    actual: CircuitSourceFrameValueLedgerKind,
) -> Result<(), CircuitW210ValueLedgerAuditError> {
    if actual == expected {
        Ok(())
    } else {
        Err(CircuitW210ValueLedgerAuditError::LedgerKindMismatch {
            role,
            expected,
            actual,
        })
    }
}

/// Parse a W210 value-ledger TSV into source-frame values.
///
/// This helper is deliberately data-only: it converts W210's one-based
/// `original_var` to the zero-based variable index used by the solver and
/// rejects any row that claims route eligibility before original-DIMACS model
/// validation.
pub(crate) fn parse_w210_source_frame_value_ledger(
    num_vars: usize,
    kind: CircuitSourceFrameValueLedgerKind,
    tsv: &str,
) -> Result<CircuitParsedSourceFrameValueLedger, CircuitSourceFrameValueLedgerParseError> {
    let mut lines = tsv.lines();
    let header_line = lines
        .next()
        .ok_or(CircuitSourceFrameValueLedgerParseError::EmptyInput)?;
    let header: Vec<_> = header_line.split('\t').collect();

    let ledger_row_id_idx = require_tsv_column(&header, "ledger_row_id")?;
    let original_var_idx = require_tsv_column(&header, "original_var")?;
    let value_idx = require_tsv_column(&header, "value")?;
    let value_int_idx = require_tsv_column(&header, "value_int")?;
    let source_kind_idx = require_tsv_column(&header, "source_kind")?;
    let production_hook_idx = require_tsv_column(&header, "production_hook")?;
    let present_idx = require_tsv_column(&header, "present_in_w159_remaining_clause")?;
    let remaining_clause_ids_idx = require_tsv_column(&header, "remaining_clause_ids")?;
    let route_eligible_idx = require_tsv_column(&header, "route_eligible")?;
    let route_blocker_idx = require_tsv_column(&header, "route_blocker")?;

    let mut stats = CircuitSourceFrameValueLedgerStats::default();
    let mut rows = Vec::new();
    for (line_offset, line) in lines.enumerate() {
        let line_number = line_offset + 2;
        let cells: Vec<_> = line.split('\t').collect();
        if cells.len() != header.len() {
            return Err(CircuitSourceFrameValueLedgerParseError::RowWidthMismatch {
                line: line_number,
                expected: header.len(),
                actual: cells.len(),
            });
        }

        let ledger_row_id = cells[ledger_row_id_idx];
        let source_row_id = parse_w210_ledger_row_id(kind, line_number, ledger_row_id)?;
        let original_var_1_based =
            parse_positive_usize(cells[original_var_idx]).ok_or_else(|| {
                CircuitSourceFrameValueLedgerParseError::InvalidOriginalVar {
                    line: line_number,
                    value: cells[original_var_idx].to_owned(),
                }
            })?;
        if original_var_1_based == 0 || original_var_1_based > num_vars {
            return Err(
                CircuitSourceFrameValueLedgerParseError::OriginalVarOutOfRange {
                    line: line_number,
                    original_var: original_var_1_based,
                    num_vars,
                },
            );
        }

        let value = parse_w210_bool(cells[value_idx], line_number, "value")?;
        let value_int = parse_w210_value_int(cells[value_int_idx], line_number)?;
        if u8::from(value) != value_int {
            return Err(CircuitSourceFrameValueLedgerParseError::ValueIntMismatch {
                line: line_number,
                value,
                value_int,
            });
        }

        if cells[source_kind_idx] != kind.source_kind() {
            return Err(
                CircuitSourceFrameValueLedgerParseError::SourceKindMismatch {
                    line: line_number,
                    expected: kind.source_kind(),
                    actual: cells[source_kind_idx].to_owned(),
                },
            );
        }
        if cells[production_hook_idx] != kind.production_hook() {
            return Err(
                CircuitSourceFrameValueLedgerParseError::ProductionHookMismatch {
                    line: line_number,
                    expected: kind.production_hook(),
                    actual: cells[production_hook_idx].to_owned(),
                },
            );
        }

        let present_in_w159_remaining_clause = parse_w210_bool(
            cells[present_idx],
            line_number,
            "present_in_w159_remaining_clause",
        )?;
        let remaining_clause_ids_1_based = parse_w210_integer_list(
            cells[remaining_clause_ids_idx],
            line_number,
            "remaining_clause_ids",
        )?;
        let route_eligible =
            parse_w210_bool(cells[route_eligible_idx], line_number, "route_eligible")?;
        if route_eligible {
            return Err(
                CircuitSourceFrameValueLedgerParseError::RouteEligibleUnsupported {
                    line: line_number,
                },
            );
        }
        let route_blocker = cells[route_blocker_idx];
        if route_blocker != "original_dimacs_validation_failed" {
            return Err(
                CircuitSourceFrameValueLedgerParseError::RouteBlockerMismatch {
                    line: line_number,
                    actual: route_blocker.to_owned(),
                },
            );
        }

        stats.rows_seen += 1;
        stats.rows_accepted += 1;
        stats.max_original_var_1_based = stats.max_original_var_1_based.max(original_var_1_based);
        stats.present_in_remaining_clause_rows += usize::from(present_in_w159_remaining_clause);
        stats.route_eligible_rows += usize::from(route_eligible);
        stats.route_blocked_rows += 1;

        rows.push(CircuitSourceFrameValueLedgerRow {
            source_row_id,
            ledger_row_id: ledger_row_id.to_owned(),
            value: CircuitSourceFrameValue {
                var: original_var_1_based - 1,
                value,
                family: kind.family(),
            },
            present_in_w159_remaining_clause,
            remaining_clause_ids_1_based,
            route_eligible,
            route_blocker: Some(route_blocker.to_owned()),
        });
    }

    Ok(CircuitParsedSourceFrameValueLedger { kind, rows, stats })
}

fn require_tsv_column(
    header: &[&str],
    column: &'static str,
) -> Result<usize, CircuitSourceFrameValueLedgerParseError> {
    header
        .iter()
        .position(|candidate| *candidate == column)
        .ok_or(CircuitSourceFrameValueLedgerParseError::MissingColumn { column })
}

fn parse_w210_ledger_row_id(
    kind: CircuitSourceFrameValueLedgerKind,
    line: usize,
    value: &str,
) -> Result<u64, CircuitSourceFrameValueLedgerParseError> {
    let Some(suffix) = value.strip_prefix(kind.row_prefix()) else {
        return Err(
            CircuitSourceFrameValueLedgerParseError::InvalidLedgerRowId {
                line,
                value: value.to_owned(),
            },
        );
    };
    suffix
        .parse()
        .ok()
        .filter(|parsed| *parsed > 0)
        .ok_or_else(
            || CircuitSourceFrameValueLedgerParseError::InvalidLedgerRowId {
                line,
                value: value.to_owned(),
            },
        )
}

fn parse_positive_usize(value: &str) -> Option<usize> {
    value.parse().ok()
}

fn parse_w210_bool(
    value: &str,
    line: usize,
    column: &'static str,
) -> Result<bool, CircuitSourceFrameValueLedgerParseError> {
    match value {
        "true" => Ok(true),
        "false" => Ok(false),
        _ => Err(CircuitSourceFrameValueLedgerParseError::InvalidBool {
            line,
            column,
            value: value.to_owned(),
        }),
    }
}

fn parse_w210_value_int(
    value: &str,
    line: usize,
) -> Result<u8, CircuitSourceFrameValueLedgerParseError> {
    match value {
        "0" => Ok(0),
        "1" => Ok(1),
        _ => Err(CircuitSourceFrameValueLedgerParseError::InvalidValueInt {
            line,
            value: value.to_owned(),
        }),
    }
}

fn parse_w210_integer_list(
    value: &str,
    line: usize,
    column: &'static str,
) -> Result<Vec<usize>, CircuitSourceFrameValueLedgerParseError> {
    if value.is_empty() {
        return Ok(Vec::new());
    }
    let mut parsed = Vec::new();
    for cell in value.split_whitespace() {
        let Some(integer) = parse_positive_usize(cell) else {
            return Err(
                CircuitSourceFrameValueLedgerParseError::InvalidIntegerListCell {
                    line,
                    column,
                    value: cell.to_owned(),
                },
            );
        };
        parsed.push(integer);
    }
    Ok(parsed)
}

/// Materialize from audited source-frame values only.
///
/// This is the narrow fail-closed entry point for frontier/SCC fallback work:
/// values from W377-style proxy-only selectors are rejected before replay, and
/// the finished assignment still must satisfy the original DIMACS clauses.
pub(crate) fn materialize_original_dimacs_assignment_from_source_frames(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    source_values: &[CircuitSourceFrameValue],
) -> Result<Vec<bool>, CircuitModelMaterializationError> {
    let mut direct_assignment = vec![None; num_vars];
    for source_value in source_values {
        if !source_value.family.is_materialization_allowed() {
            return Err(
                CircuitModelMaterializationError::RejectedSourceFrameFamily {
                    var: source_value.var,
                    family: source_value.family,
                },
            );
        }
        if source_value.var >= num_vars {
            return Err(CircuitModelMaterializationError::SourceFrameVarOutOfRange {
                var: source_value.var,
            });
        }
        if let Some(existing) = direct_assignment[source_value.var] {
            if existing != source_value.value {
                return Err(
                    CircuitModelMaterializationError::ConflictingSourceFrameValue {
                        var: source_value.var,
                    },
                );
            }
        } else {
            direct_assignment[source_value.var] = Some(source_value.value);
        }
    }
    materialize_original_dimacs_assignment(num_vars, clauses, &direct_assignment)
}

/// Materialize from source-frame rows bound to original clauses.
///
/// This richer default-off helper is still scout-only: it audits the row
/// provenance surface, rejects proxy families, scans the full original CNF, and
/// returns no SAT/model authority.
pub(crate) fn materialize_original_dimacs_assignment_from_source_frame_rows(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    source_rows: &[CircuitSourceFrameRow],
) -> Result<CircuitMaterializedAssignment, CircuitModelMaterializationError> {
    let (mut audit, direct_assignment, first_error) =
        source_frame_rows_to_direct_assignment(num_vars, clauses, source_rows);
    if let Some(error) = first_error {
        return Err(error);
    }

    let assignment = replay_original_dimacs_assignment(num_vars, clauses, &direct_assignment)?;
    audit.missing_source_rows = assignment.iter().filter(|value| value.is_none()).count();
    audit.assignment_complete = audit.missing_source_rows == 0;
    if !audit.assignment_complete {
        let var = assignment
            .iter()
            .position(Option::is_none)
            .expect("missing source row count was nonzero");
        return Err(CircuitModelMaterializationError::MissingDirectValue { var });
    }

    let residual = diagnose_original_dimacs_assignment(num_vars, clauses, &assignment);
    audit.original_clauses_checked = residual.original_clauses_checked;
    audit.residual_falsified_count = residual.residual_falsified_count;
    audit.first_residual_clause = residual.first_residual_clause;
    audit.residual_clause_ids = residual.residual_clause_ids;
    if audit.residual_falsified_count > 0 {
        return Err(
            CircuitModelMaterializationError::SourceFrameResidualNonZero {
                residual_falsified_count: audit.residual_falsified_count,
                first_clause: audit
                    .first_residual_clause
                    .expect("residual count was nonzero"),
            },
        );
    }
    audit.validation_passed = true;
    Ok(CircuitMaterializedAssignment {
        assignment: assignment
            .into_iter()
            .map(|value| value.expect("complete assignment validated"))
            .collect(),
        audit,
    })
}

/// Audit source-frame row bindings without granting model authority.
pub(crate) fn audit_source_frame_rows(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    source_rows: &[CircuitSourceFrameRow],
) -> CircuitSourceFrameAudit {
    let (mut audit, direct_assignment, first_error) =
        source_frame_rows_to_direct_assignment(num_vars, clauses, source_rows);
    if first_error.is_some() {
        return audit;
    }
    let assignment = match replay_original_dimacs_assignment(num_vars, clauses, &direct_assignment)
    {
        Ok(assignment) => assignment,
        Err(_) => {
            let residual =
                diagnose_original_dimacs_assignment(num_vars, clauses, &direct_assignment);
            audit.missing_source_rows = residual.missing_values;
            audit.assignment_complete = residual.assignment_complete;
            audit.original_clauses_checked = residual.original_clauses_checked;
            audit.residual_falsified_count = residual.residual_falsified_count;
            audit.first_residual_clause = residual.first_residual_clause;
            audit.residual_clause_ids = residual.residual_clause_ids;
            audit.validation_passed = false;
            return audit;
        }
    };
    let residual = diagnose_original_dimacs_assignment(num_vars, clauses, &assignment);
    audit.missing_source_rows = residual.missing_values;
    audit.assignment_complete = residual.assignment_complete;
    audit.original_clauses_checked = residual.original_clauses_checked;
    audit.residual_falsified_count = residual.residual_falsified_count;
    audit.first_residual_clause = residual.first_residual_clause;
    audit.residual_clause_ids = residual.residual_clause_ids;
    audit.validation_passed = residual.validation_passed;
    audit
}

/// Audit whether source rows plus checker evidence can authorize an original SAT model.
///
/// The function does not emit a SAT result and does not wire any Main route. It
/// only records whether a caller has a complete materialized assignment and
/// `ay check model --json` style evidence for the original DIMACS formula.
pub(crate) fn audit_original_dimacs_sat_model_authority(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    source_rows: &[CircuitSourceFrameRow],
    retained_artifacts: Option<&CircuitOriginalDimacsModelAuthorityArtifacts>,
    checker_evidence: Option<&CircuitOriginalDimacsModelCheckEvidence>,
) -> CircuitOriginalDimacsSatModelAuthorityAudit {
    let source_frame_audit = audit_source_frame_rows(num_vars, clauses, source_rows);
    let mut audit = CircuitOriginalDimacsSatModelAuthorityAudit {
        source_frame_audit,
        materialized_assignment: None,
        retained_artifacts_supplied: retained_artifacts.is_some(),
        checker_evidence_supplied: checker_evidence.is_some(),
        retained_formula_path: retained_artifacts.map(|artifacts| artifacts.formula.path.clone()),
        retained_formula_sha256: retained_artifacts
            .map(|artifacts| artifacts.formula.sha256.clone()),
        retained_model_stdout_path: retained_artifacts
            .map(|artifacts| artifacts.model_stdout.path.clone()),
        retained_model_stdout_sha256: retained_artifacts
            .map(|artifacts| artifacts.model_stdout.sha256.clone()),
        retained_checker_command: retained_artifacts
            .map(|artifacts| artifacts.checker_command.clone()),
        retained_checker_verdict_sha256: retained_artifacts
            .map(|artifacts| artifacts.checker_verdict_sha256.clone()),
        checker_schema: checker_evidence.map(|evidence| evidence.schema.clone()),
        checker_formula_path: checker_evidence.map(|evidence| evidence.formula.path.clone()),
        checker_formula_sha256: checker_evidence.map(|evidence| evidence.formula.sha256.clone()),
        checker_model_stdout_path: checker_evidence.map(|evidence| evidence.stdout.path.clone()),
        checker_model_stdout_sha256: checker_evidence
            .map(|evidence| evidence.stdout.sha256.clone()),
        checker_model_status: checker_evidence.map(|evidence| evidence.model_status.clone()),
        checker_valid: checker_evidence.map(|evidence| evidence.valid),
        checker_num_vars: checker_evidence.and_then(|evidence| evidence.num_vars),
        checker_clauses_checked: checker_evidence.map(|evidence| evidence.clauses_checked),
        checker_first_unsatisfied_clause: checker_evidence
            .and_then(|evidence| evidence.first_unsatisfied_clause),
        checker_command: checker_evidence.map(|evidence| evidence.checker_command.clone()),
        checker_exit_status: checker_evidence.map(|evidence| evidence.checker_exit_status),
        checker_verdict_sha256: checker_evidence
            .map(|evidence| evidence.checker_verdict_sha256.clone()),
        authority_status: CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
            CircuitOriginalDimacsSatModelAuthorityBlocker::SourceFrameValidationFailed,
        ),
        sat_output_authority: false,
        model_output_authority: false,
        proof_output_authority: false,
        solver_verdict_authority: false,
    };

    if !audit.source_frame_audit.validation_passed {
        return audit;
    }

    let materialized = match materialize_original_dimacs_assignment_from_source_frame_rows(
        num_vars,
        clauses,
        source_rows,
    ) {
        Ok(materialized) => materialized,
        Err(error) => {
            audit.authority_status = CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::MaterializationRejected(error),
            );
            return audit;
        }
    };
    audit.materialized_assignment = Some(materialized.assignment);

    let Some(artifacts) = retained_artifacts else {
        audit.authority_status = CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
            CircuitOriginalDimacsSatModelAuthorityBlocker::RetainedArtifactsMissing,
        );
        return audit;
    };

    let artifact_blocker = if artifacts.formula.path.trim().is_empty() {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::RetainedFormulaPathMissing)
    } else if !is_sha256_hex(&artifacts.formula.sha256) {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::RetainedFormulaHashInvalid)
    } else if artifacts.model_stdout.path.trim().is_empty() {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::RetainedModelStdoutPathMissing)
    } else if !is_sha256_hex(&artifacts.model_stdout.sha256) {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::RetainedModelStdoutHashInvalid)
    } else if artifacts.checker_command.is_empty() {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::RetainedCheckerCommandMissing)
    } else if !is_sha256_hex(&artifacts.checker_verdict_sha256) {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::RetainedCheckerVerdictHashInvalid)
    } else {
        None
    };
    if let Some(blocker) = artifact_blocker {
        audit.authority_status = CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(blocker);
        return audit;
    }

    let Some(evidence) = checker_evidence else {
        audit.authority_status = CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
            CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerEvidenceMissing,
        );
        return audit;
    };

    let blocker = if evidence.schema != ORIGINAL_DIMACS_MODEL_CHECK_SCHEMA {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerSchemaMismatch)
    } else if evidence.formula.path.trim().is_empty() {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerFormulaMissing)
    } else if !is_sha256_hex(&evidence.formula.sha256) {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerFormulaHashInvalid)
    } else if evidence.stdout.path.trim().is_empty() {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerStdoutMissing)
    } else if !is_sha256_hex(&evidence.stdout.sha256) {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerStdoutHashInvalid)
    } else if evidence.checker_command.is_empty() {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerCommandMissing)
    } else if evidence.checker_exit_status != 0 {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerExitStatusNonZero)
    } else if !is_sha256_hex(&evidence.checker_verdict_sha256) {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerVerdictHashInvalid)
    } else if evidence.formula.path != artifacts.formula.path {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::FormulaArtifactPathMismatch)
    } else if evidence.formula.sha256 != artifacts.formula.sha256 {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::FormulaArtifactHashMismatch)
    } else if evidence.stdout.path != artifacts.model_stdout.path {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::ModelStdoutArtifactPathMismatch)
    } else if evidence.stdout.sha256 != artifacts.model_stdout.sha256 {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::ModelStdoutArtifactHashMismatch)
    } else if evidence.checker_command != artifacts.checker_command {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerCommandMismatch)
    } else if evidence.checker_verdict_sha256 != artifacts.checker_verdict_sha256 {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerVerdictHashMismatch)
    } else if evidence.ay_build_id.trim().is_empty() {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerBuildProvenanceMissing)
    } else if evidence.model_status != ORIGINAL_DIMACS_VALID_MODEL_STATUS {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerModelStatusNotValid)
    } else if !evidence.valid {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerVerdictInvalid)
    } else if evidence.num_vars.is_none() {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerNumVarsMissing)
    } else if evidence.num_vars != Some(num_vars) {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerNumVarsMismatch)
    } else if evidence.clauses_checked != clauses.len() as u64 {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerClausesCheckedMismatch)
    } else if evidence.first_unsatisfied_clause.is_some() {
        Some(CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerFirstUnsatisfiedClause)
    } else {
        None
    };

    if let Some(blocker) = blocker {
        audit.authority_status = CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(blocker);
        return audit;
    }

    audit.authority_status = CircuitOriginalDimacsSatModelAuthorityStatus::Admitted;
    audit.sat_output_authority = true;
    audit.model_output_authority = true;
    audit.proof_output_authority = false;
    audit.solver_verdict_authority = true;
    audit
}

/// Bind retained `ay check model --json` output to formula/model artifacts.
///
/// The caller supplies retained bytes, not hashes. This helper computes every
/// SHA-256 identity that the authority audit later compares, so route wiring
/// cannot synthesize authority by filling shape-compatible fields alone.
pub(crate) fn bind_retained_original_dimacs_model_check_evidence(
    retained: CircuitOriginalDimacsRetainedModelCheckArtifacts,
) -> Result<
    CircuitOriginalDimacsBoundModelCheckEvidence,
    CircuitOriginalDimacsModelCheckEvidenceBindingError,
> {
    let formula_sha256 = sha256_hex(&retained.formula_bytes);
    let model_stdout_sha256 = sha256_hex(&retained.model_stdout_bytes);
    let checker_verdict_sha256 = sha256_hex(&retained.checker_verdict_json);
    let payload: Value = serde_json::from_slice(&retained.checker_verdict_json).map_err(|_| {
        CircuitOriginalDimacsModelCheckEvidenceBindingError::CheckerVerdictJsonInvalid
    })?;

    let artifacts = CircuitOriginalDimacsModelAuthorityArtifacts {
        formula: CircuitOriginalDimacsArtifactIdentity {
            path: retained.formula_path,
            sha256: formula_sha256.clone(),
        },
        model_stdout: CircuitOriginalDimacsArtifactIdentity {
            path: retained.model_stdout_path,
            sha256: model_stdout_sha256.clone(),
        },
        checker_command: retained.checker_command.clone(),
        checker_verdict_sha256: checker_verdict_sha256.clone(),
    };

    let checker_evidence = CircuitOriginalDimacsModelCheckEvidence {
        schema: json_required_string(&payload, "schema")?,
        formula: CircuitOriginalDimacsArtifactIdentity {
            path: json_required_string(&payload, "formula")?,
            sha256: formula_sha256,
        },
        stdout: CircuitOriginalDimacsArtifactIdentity {
            path: json_required_string(&payload, "stdout")?,
            sha256: model_stdout_sha256,
        },
        model_status: json_required_string(&payload, "model_status")?,
        valid: json_required_bool(&payload, "valid")?,
        num_vars: json_optional_usize(&payload, "num_vars")?,
        clauses_checked: json_required_u64(&payload, "clauses_checked")?,
        first_unsatisfied_clause: json_optional_u64(&payload, "first_unsatisfied_clause")?,
        checker_command: retained.checker_command,
        checker_exit_status: retained.checker_exit_status,
        checker_verdict_sha256,
        ay_build_id: json_ay_build_id(&payload)?,
    };

    Ok(CircuitOriginalDimacsBoundModelCheckEvidence {
        artifacts,
        checker_evidence,
    })
}

/// Materialize a source-frame assignment and produce retained SAT-model
/// authority artifacts for the existing fail-closed audit.
///
/// This remains route-silent: it emits no SAT result and grants no authority on
/// its own. The checker verdict JSON must come from a retained model-check run;
/// this helper binds that verdict to the AY-produced model stdout instead of
/// synthesizing checker authority. Callers still must pass the returned packet
/// to [`audit_original_dimacs_sat_model_authority`].
pub(crate) fn produce_original_dimacs_sat_model_authority_packet(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    source_rows: &[CircuitSourceFrameRow],
    formula_path: &str,
    model_stdout_path: &str,
    checker_command: Vec<String>,
    checker_exit_status: i32,
    checker_verdict_json: Vec<u8>,
) -> Result<
    CircuitOriginalDimacsSatModelAuthorityPacket,
    CircuitOriginalDimacsSatModelAuthorityProductionError,
> {
    let materialized = materialize_original_dimacs_assignment_from_source_frame_rows(
        num_vars,
        clauses,
        source_rows,
    )
    .map_err(CircuitOriginalDimacsSatModelAuthorityProductionError::Materialization)?;
    let formula_dimacs = render_original_dimacs_cnf(num_vars, clauses).into_bytes();
    let model_stdout = render_satcomp_model_stdout(&materialized.assignment).into_bytes();
    let bound = bind_retained_original_dimacs_model_check_evidence(
        CircuitOriginalDimacsRetainedModelCheckArtifacts {
            formula_path: formula_path.to_owned(),
            formula_bytes: formula_dimacs.clone(),
            model_stdout_path: model_stdout_path.to_owned(),
            model_stdout_bytes: model_stdout.clone(),
            checker_command,
            checker_exit_status,
            checker_verdict_json: checker_verdict_json.clone(),
        },
    )
    .map_err(CircuitOriginalDimacsSatModelAuthorityProductionError::Binding)?;

    Ok(CircuitOriginalDimacsSatModelAuthorityPacket {
        artifacts: bound.artifacts,
        checker_evidence: bound.checker_evidence,
        formula_dimacs,
        model_stdout,
        checker_verdict_json,
    })
}

fn render_original_dimacs_cnf(num_vars: usize, clauses: &[Vec<Literal>]) -> String {
    let mut output = format!("p cnf {num_vars} {}\n", clauses.len());
    for clause in clauses {
        for lit in clause {
            output.push_str(&lit.to_dimacs().to_string());
            output.push(' ');
        }
        output.push_str("0\n");
    }
    output
}

fn render_satcomp_model_stdout(assignment: &[bool]) -> String {
    let mut output = String::from("s SATISFIABLE\nv");
    for (idx, value) in assignment.iter().enumerate() {
        let var = i32::try_from(idx)
            .ok()
            .and_then(|idx| idx.checked_add(1))
            .expect("BUG: model variable index exceeds DIMACS i32 encoding range");
        output.push(' ');
        if *value {
            output.push_str(&var.to_string());
        } else {
            output.push('-');
            output.push_str(&var.to_string());
        }
    }
    output.push_str(" 0\n");
    output
}

fn render_original_dimacs_model_check_json(
    formula_path: &str,
    model_stdout_path: &str,
    num_vars: usize,
    clauses_checked: u64,
    valid: bool,
    ay_build_id: &str,
) -> String {
    let model_status = if valid {
        ORIGINAL_DIMACS_VALID_MODEL_STATUS
    } else {
        "invalid"
    };
    json!({
        "schema": ORIGINAL_DIMACS_MODEL_CHECK_SCHEMA,
        "formula": formula_path,
        "stdout": model_stdout_path,
        "model_status": model_status,
        "valid": valid,
        "num_vars": num_vars,
        "clauses_checked": clauses_checked,
        "first_unsatisfied_clause": Value::Null,
        "elapsed_ms": 0,
        "ay_build": {
            "stamp": ay_build_id,
        },
    })
    .to_string()
}

fn json_required_string(
    payload: &Value,
    key: &'static str,
) -> Result<String, CircuitOriginalDimacsModelCheckEvidenceBindingError> {
    payload
        .get(key)
        .and_then(Value::as_str)
        .map(ToOwned::to_owned)
        .ok_or(CircuitOriginalDimacsModelCheckEvidenceBindingError::JsonStringFieldMissing(key))
}

fn json_required_bool(
    payload: &Value,
    key: &'static str,
) -> Result<bool, CircuitOriginalDimacsModelCheckEvidenceBindingError> {
    payload
        .get(key)
        .and_then(Value::as_bool)
        .ok_or(CircuitOriginalDimacsModelCheckEvidenceBindingError::JsonBoolFieldMissing(key))
}

fn json_required_u64(
    payload: &Value,
    key: &'static str,
) -> Result<u64, CircuitOriginalDimacsModelCheckEvidenceBindingError> {
    payload
        .get(key)
        .and_then(Value::as_u64)
        .ok_or(CircuitOriginalDimacsModelCheckEvidenceBindingError::JsonU64FieldMissing(key))
}

fn json_optional_u64(
    payload: &Value,
    key: &'static str,
) -> Result<Option<u64>, CircuitOriginalDimacsModelCheckEvidenceBindingError> {
    match payload.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(value) => value.as_u64().map(Some).ok_or(
            CircuitOriginalDimacsModelCheckEvidenceBindingError::JsonOptionalU64FieldInvalid(key),
        ),
    }
}

fn json_optional_usize(
    payload: &Value,
    key: &'static str,
) -> Result<Option<usize>, CircuitOriginalDimacsModelCheckEvidenceBindingError> {
    json_optional_u64(payload, key).map(|value| value.and_then(|value| usize::try_from(value).ok()))
}

fn json_ay_build_id(
    payload: &Value,
) -> Result<String, CircuitOriginalDimacsModelCheckEvidenceBindingError> {
    let Some(value) = payload.get("ay_build") else {
        return Err(
            CircuitOriginalDimacsModelCheckEvidenceBindingError::JsonBuildProvenanceMissing,
        );
    };
    if let Some(raw) = value.as_str().filter(|raw| !raw.trim().is_empty()) {
        return Ok(raw.to_owned());
    }
    for key in ["stamp", "commit", "version"] {
        if let Some(raw) = value
            .get(key)
            .and_then(Value::as_str)
            .filter(|raw| !raw.trim().is_empty())
        {
            return Ok(raw.to_owned());
        }
    }
    Err(CircuitOriginalDimacsModelCheckEvidenceBindingError::JsonBuildProvenanceMissing)
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(64);
    for byte in digest {
        output.push_str(&format!("{byte:02x}"));
    }
    output
}

fn is_sha256_hex(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

/// Diagnose completeness and residual original-DIMACS falsification.
pub(crate) fn diagnose_original_dimacs_assignment(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    assignment: &[Option<bool>],
) -> CircuitModelResidualReport {
    let mut report = CircuitModelResidualReport {
        original_model_vars: num_vars,
        assignment_len: assignment.len(),
        original_clauses_checked: clauses.len(),
        ..CircuitModelResidualReport::default()
    };

    if assignment.len() == num_vars {
        for (idx, value) in assignment.iter().enumerate() {
            if value.is_none() {
                report.missing_values += 1;
                report.first_missing_var.get_or_insert(idx);
            }
        }
    } else {
        report.missing_values = num_vars;
        report.first_missing_var = Some(0);
    }
    report.assignment_complete = assignment.len() == num_vars && report.missing_values == 0;

    for (clause_index, clause) in clauses.iter().enumerate() {
        let satisfied = clause.iter().any(|&lit| {
            let var_idx = lit.variable().index();
            assignment
                .get(var_idx)
                .and_then(|value| *value)
                .is_some_and(|value| value == lit.is_positive())
        });
        if !satisfied {
            report.residual_falsified_count += 1;
            report.first_residual_clause.get_or_insert(clause_index);
            report.residual_clause_ids.push(clause_index);
        }
    }
    report.validation_passed = report.assignment_complete && report.residual_falsified_count == 0;
    report
}

fn source_frame_rows_to_direct_assignment(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    source_rows: &[CircuitSourceFrameRow],
) -> (
    CircuitSourceFrameAudit,
    Vec<Option<bool>>,
    Option<CircuitModelMaterializationError>,
) {
    let mut audit = CircuitSourceFrameAudit {
        rows_seen: source_rows.len(),
        ..CircuitSourceFrameAudit::default()
    };
    let mut direct_assignment = vec![None; num_vars];
    let mut first_error = None;

    for row in source_rows {
        let mut reject = |audit: &mut CircuitSourceFrameAudit,
                          error: CircuitModelMaterializationError| {
            audit.rows_rejected += 1;
            if first_error.is_none() {
                first_error = Some(error);
            }
        };

        if !row.family.is_materialization_allowed() {
            audit.unsupported_family += 1;
            reject(
                &mut audit,
                CircuitModelMaterializationError::RejectedSourceFrameFamily {
                    var: row.var,
                    family: row.family,
                },
            );
            continue;
        }
        if row.var >= num_vars {
            audit.var_out_of_range += 1;
            reject(
                &mut audit,
                CircuitModelMaterializationError::SourceFrameVarOutOfRange { var: row.var },
            );
            continue;
        }
        let literal_var = row.literal.variable().index();
        if literal_var != row.var {
            audit.literal_var_mismatch += 1;
            reject(
                &mut audit,
                CircuitModelMaterializationError::SourceFrameLiteralVarMismatch {
                    source_row_id: row.source_row_id,
                    var: row.var,
                    literal_var,
                },
            );
            continue;
        }
        if row.kind == CircuitSourceFrameKind::UnreferencedOriginalValue {
            if original_var_occurs_in_clauses(clauses, row.var) {
                audit.unreferenced_var_occurs += 1;
                reject(
                    &mut audit,
                    CircuitModelMaterializationError::SourceFrameUnreferencedVarOccurs {
                        source_row_id: row.source_row_id,
                        var: row.var,
                    },
                );
                continue;
            }
            if let Some(existing) = direct_assignment[row.var] {
                if existing != row.source_value {
                    audit.conflicts += 1;
                    reject(
                        &mut audit,
                        CircuitModelMaterializationError::ConflictingSourceFrameValue {
                            var: row.var,
                        },
                    );
                    continue;
                }
            } else {
                direct_assignment[row.var] = Some(row.source_value);
            }
            audit.unreferenced_original_var_rows += 1;
            audit.rows_accepted += 1;
            continue;
        }
        let Some(clause) = clauses.get(row.clause_id) else {
            audit.clause_out_of_range += 1;
            reject(
                &mut audit,
                CircuitModelMaterializationError::SourceFrameClauseOutOfRange {
                    source_row_id: row.source_row_id,
                    clause_id: row.clause_id,
                },
            );
            continue;
        };
        if !clause.contains(&row.literal) {
            audit.literal_missing_from_clause += 1;
            reject(
                &mut audit,
                CircuitModelMaterializationError::SourceFrameLiteralMissingFromClause {
                    source_row_id: row.source_row_id,
                    clause_id: row.clause_id,
                    literal: row.literal,
                },
            );
            continue;
        }
        if let Some(existing) = direct_assignment[row.var] {
            if existing != row.source_value {
                audit.conflicts += 1;
                reject(
                    &mut audit,
                    CircuitModelMaterializationError::ConflictingSourceFrameValue { var: row.var },
                );
                continue;
            }
        } else {
            direct_assignment[row.var] = Some(row.source_value);
        }
        audit.rows_accepted += 1;
    }

    (audit, direct_assignment, first_error)
}

fn replay_original_dimacs_assignment(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    direct_assignment: &[Option<bool>],
) -> Result<Vec<Option<bool>>, CircuitModelMaterializationError> {
    if direct_assignment.len() != num_vars {
        return Err(CircuitModelMaterializationError::Validation(
            CircuitModelValidationError::WrongLength {
                expected: num_vars,
                actual: direct_assignment.len(),
            },
        ));
    }

    let gates = recover_gates(num_vars, clauses);
    let replay = analyze_assignment_replay(num_vars, &gates);
    if replay.out_of_range_gate_outputs > 0 {
        return Err(CircuitModelMaterializationError::GateOutputOutOfRange);
    }
    if replay.out_of_range_gate_inputs > 0 {
        return Err(CircuitModelMaterializationError::GateInputOutOfRange);
    }
    if replay.duplicate_gate_output_defs > 0 {
        return Err(CircuitModelMaterializationError::DuplicateGateOutput);
    }

    let mut assignment = direct_assignment.to_vec();
    for gate_idx in replay.replay_order_gate_indices {
        let gate = &gates[gate_idx];
        let output_idx = gate.output.index();
        if !gate_inputs_are_assigned(gate, &assignment) {
            continue;
        }
        let value = evaluate_gate(gate, &assignment)?;
        if let Some(existing) = assignment[output_idx] {
            if existing != value {
                return Err(CircuitModelMaterializationError::ConflictingDirectValue {
                    var: output_idx,
                });
            }
        } else {
            assignment[output_idx] = Some(value);
        }
    }
    Ok(assignment)
}

fn gate_inputs_are_assigned(gate: &Gate, assignment: &[Option<bool>]) -> bool {
    gate.inputs.iter().all(|input| {
        assignment
            .get(input.variable().index())
            .is_some_and(Option::is_some)
    })
}

/// Fail-closed materialization result for the default-off circuit scout.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitModelMaterializationError {
    /// Recovered output variable exceeded the original DIMACS range.
    GateOutputOutOfRange,
    /// Recovered input variable exceeded the original DIMACS range.
    GateInputOutOfRange,
    /// Multiple recovered gates define the same output.
    DuplicateGateOutput,
    /// A recovered gate had unsupported arity or shape.
    MalformedGate,
    /// A replayable recovered gate depended on a value the source frame did not provide.
    MissingReplayInput {
        /// Zero-based recovered gate output variable.
        gate_output_var: usize,
        /// Zero-based missing input variable.
        input_var: usize,
    },
    /// Caller omitted a value that is not replayable from the acyclic plan.
    MissingDirectValue {
        /// Zero-based variable index.
        var: usize,
    },
    /// Caller supplied a direct value inconsistent with replay.
    ConflictingDirectValue {
        /// Zero-based variable index.
        var: usize,
    },
    /// Caller supplied a source-frame family that is not accepted as an
    /// original-DIMACS materialization input.
    RejectedSourceFrameFamily {
        /// Zero-based variable index.
        var: usize,
        /// Rejected source-frame family.
        family: CircuitSourceFrameFamily,
    },
    /// Caller supplied a source-frame value outside the original DIMACS range.
    SourceFrameVarOutOfRange {
        /// Zero-based variable index.
        var: usize,
    },
    /// Caller supplied conflicting values for the same source-frame variable.
    ConflictingSourceFrameValue {
        /// Zero-based variable index.
        var: usize,
    },
    /// Source-frame row literal did not name the row variable.
    SourceFrameLiteralVarMismatch {
        /// Stable source row identifier from the producing packet.
        source_row_id: u64,
        /// Zero-based original DIMACS variable index.
        var: usize,
        /// Zero-based variable named by `literal`.
        literal_var: usize,
    },
    /// Source-frame row named an original clause outside the formula.
    SourceFrameClauseOutOfRange {
        /// Stable source row identifier from the producing packet.
        source_row_id: u64,
        /// Zero-based original clause index.
        clause_id: usize,
    },
    /// Source-frame row literal was absent from the named original clause.
    SourceFrameLiteralMissingFromClause {
        /// Stable source row identifier from the producing packet.
        source_row_id: u64,
        /// Zero-based original clause index.
        clause_id: usize,
        /// Literal expected in the original clause.
        literal: Literal,
    },
    /// Source-frame row claimed an unreferenced original variable that appears
    /// in at least one original DIMACS clause.
    SourceFrameUnreferencedVarOccurs {
        /// Stable source row identifier from the producing packet.
        source_row_id: u64,
        /// Zero-based original DIMACS variable index.
        var: usize,
    },
    /// Full original-DIMACS scan found residual falsified clauses.
    SourceFrameResidualNonZero {
        /// Number of falsified original clauses.
        residual_falsified_count: usize,
        /// First falsified original clause.
        first_clause: usize,
    },
    /// Final original-DIMACS validation failed.
    Validation(CircuitModelValidationError),
}

/// Fail-closed result from original-DIMACS model validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitModelValidationError {
    /// Assignment length did not match the DIMACS header.
    WrongLength {
        /// Expected number of original variables.
        expected: usize,
        /// Actual number of assignment entries.
        actual: usize,
    },
    /// A variable had no assigned truth value.
    Incomplete {
        /// Zero-based variable index.
        var: usize,
    },
    /// At least one original clause was not satisfied.
    UnsatisfiedClause {
        /// Zero-based clause index.
        clause_index: usize,
    },
}

struct CircuitSourceClauseBinding {
    source_clause_index: usize,
    source_clause_id_1_based: u64,
    original_lits: Vec<Literal>,
}

struct SourceClauseArena {
    arena: ClauseArena,
    pos_occs: Vec<Vec<usize>>,
    neg_occs: Vec<Vec<usize>>,
    source_clause_by_offset: DetHashMap<usize, CircuitSourceClauseBinding>,
}

impl SourceClauseArena {
    fn original_clause_id(&self, offset: usize) -> Option<usize> {
        self.source_clause_by_offset
            .get(&offset)
            .map(|binding| binding.source_clause_index)
    }

    fn proof_clause_id_1_based(&self, offset: usize) -> Option<u64> {
        self.source_clause_by_offset
            .get(&offset)
            .map(|binding| binding.source_clause_id_1_based)
    }

    fn literals_for_offset(&self, offset: usize) -> Option<&[Literal]> {
        if !self.arena.indices().any(|candidate| candidate == offset) {
            return None;
        }
        Some(self.arena.literals(offset))
    }
}

fn build_clause_arena(num_vars: usize, clauses: &[Vec<Literal>]) -> SourceClauseArena {
    let literal_hint = clauses.iter().map(Vec::len).sum();
    let mut arena = ClauseArena::with_capacity(clauses.len(), literal_hint);
    let mut pos_occs = vec![Vec::new(); num_vars];
    let mut neg_occs = vec![Vec::new(); num_vars];
    let mut source_clause_by_offset = DetHashMap::default();

    for (source_clause_id, clause) in clauses.iter().enumerate() {
        if clause.is_empty() {
            continue;
        }
        let offset = arena.add(clause, false);
        source_clause_by_offset.insert(
            offset,
            CircuitSourceClauseBinding {
                source_clause_index: source_clause_id,
                source_clause_id_1_based: source_clause_id as u64 + 1,
                original_lits: clause.clone(),
            },
        );
        for &lit in clause {
            let var_idx = lit.variable().index();
            if var_idx >= num_vars {
                continue;
            }
            if lit.is_positive() {
                pos_occs[var_idx].push(offset);
            } else {
                neg_occs[var_idx].push(offset);
            }
        }
    }

    SourceClauseArena {
        arena,
        pos_occs,
        neg_occs,
        source_clause_by_offset,
    }
}

fn audit_gate_source_clause_bindings(
    gates: &[Gate],
    arena: &SourceClauseArena,
    clauses: &[Vec<Literal>],
) -> CircuitSourceClauseBindingReport {
    let mut report = CircuitSourceClauseBindingReport::default();
    for gate in gates {
        let mut seen_offsets = Vec::with_capacity(gate.defining_clauses.len());
        for &offset in &gate.defining_clauses {
            report.gate_clause_references += 1;
            if seen_offsets.contains(&offset) {
                report.duplicate_gate_clause_reference_rows += 1;
                continue;
            } else {
                seen_offsets.push(offset);
            }
            let Some(binding) = arena.source_clause_by_offset.get(&offset) else {
                report.source_clause_binding_missing_rows += 1;
                continue;
            };
            let Some(original_clause) = clauses.get(binding.source_clause_index) else {
                report.source_clause_out_of_range_rows += 1;
                continue;
            };
            let Some(arena_clause) = arena.literals_for_offset(offset) else {
                report.source_clause_binding_missing_rows += 1;
                continue;
            };
            if arena_clause == original_clause.as_slice()
                && binding.original_lits.as_slice() == original_clause.as_slice()
                && binding.source_clause_id_1_based == binding.source_clause_index as u64 + 1
            {
                report.source_clause_bound_rows += 1;
            } else {
                report.source_clause_literal_mismatch_rows += 1;
            }
        }
    }
    report.fail_closed = report.source_clause_binding_missing_rows > 0
        || report.duplicate_gate_clause_reference_rows > 0
        || report.source_clause_out_of_range_rows > 0
        || report.source_clause_literal_mismatch_rows > 0;
    report
}

fn count_gate_kinds(report: &mut CircuitScoutReport, gates: &[Gate]) {
    for gate in gates {
        match gate.gate_type {
            GateType::And => report.gate_and += 1,
            GateType::Xor => report.gate_xor += 1,
            GateType::Ite => report.gate_ite += 1,
            GateType::Equiv => report.gate_equiv += 1,
        }
    }
    report.gates_total = gates.len() as u64;
}

fn build_model_witness_report(
    num_vars: usize,
    gates: &[Gate],
    scout: &CircuitScoutReport,
) -> CircuitModelWitnessReport {
    let mut report = CircuitModelWitnessReport {
        original_model_vars: num_vars,
        equivalence_alias_witnesses: scout
            .equivalence_members
            .saturating_sub(scout.equivalence_classes),
        adder_sum_witnesses: scout.half_adders + scout.full_adders,
        adder_carry_witnesses: scout.adder_carry_links,
        partial_product_witnesses: scout.partial_product_ands,
        ..CircuitModelWitnessReport::default()
    };

    for gate in gates {
        report.gate_output_witnesses += 1;
        match gate.gate_type {
            GateType::And => report.and_output_witnesses += 1,
            GateType::Xor => report.xor_output_witnesses += 1,
            GateType::Ite => report.ite_output_witnesses += 1,
            GateType::Equiv => report.equiv_output_witnesses += 1,
        }
    }

    let replay = analyze_assignment_replay(num_vars, gates);
    report.partial_assignment_required_vars = replay.frontier_vars;
    report.derivable_gate_output_vars = replay.derivable_gate_output_vars;
    report.acyclic_replay_order_len = replay.replay_order_gate_indices.len();
    report.blocked_gate_output_vars = replay.blocked_gate_output_vars;
    report.blocked_by_cycle_output_vars = replay.blocked_by_cycle_output_vars;
    report.blocked_by_duplicate_output_vars = replay.blocked_by_duplicate_output_vars;
    report.blocked_by_malformed_dependency_output_vars =
        replay.blocked_by_malformed_dependency_output_vars;
    report.blocked_by_unresolved_dependency_output_vars =
        replay.blocked_by_unresolved_dependency_output_vars;
    report.blocked_output_dependency_edges = replay.blocked_output_dependency_edges;
    report.duplicate_gate_output_defs = replay.duplicate_gate_output_defs;
    report.out_of_range_gate_outputs = replay.out_of_range_gate_outputs;
    report.out_of_range_gate_inputs = replay.out_of_range_gate_inputs;
    report.complete_original_model_vars = replay.complete_original_model_vars;

    report.rejection = if report.out_of_range_gate_outputs > 0 {
        CircuitModelWitnessRejection::GateOutputOutOfRange
    } else if report.out_of_range_gate_inputs > 0 {
        CircuitModelWitnessRejection::GateInputOutOfRange
    } else if report.duplicate_gate_output_defs > 0 {
        CircuitModelWitnessRejection::DuplicateGateOutput
    } else if report.complete_original_model_vars != report.original_model_vars {
        CircuitModelWitnessRejection::BlockedGateOutput
    } else {
        CircuitModelWitnessRejection::None
    };
    report.fail_closed = report.rejection != CircuitModelWitnessRejection::None;
    report
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct AssignmentReplayReport {
    frontier_vars: usize,
    derivable_gate_output_vars: usize,
    blocked_gate_output_vars: usize,
    blocked_by_cycle_output_vars: usize,
    blocked_by_duplicate_output_vars: usize,
    blocked_by_malformed_dependency_output_vars: usize,
    blocked_by_unresolved_dependency_output_vars: usize,
    blocked_output_dependency_edges: usize,
    duplicate_gate_output_defs: u64,
    out_of_range_gate_outputs: u64,
    out_of_range_gate_inputs: u64,
    complete_original_model_vars: usize,
    replay_order_gate_indices: Vec<usize>,
}

fn analyze_assignment_replay(num_vars: usize, gates: &[Gate]) -> AssignmentReplayReport {
    let mut replay = AssignmentReplayReport::default();
    let mut output_counts = vec![0u16; num_vars];
    let mut output_gate_indices = vec![None; num_vars];
    let mut malformed_output = vec![false; num_vars];

    for (gate_idx, gate) in gates.iter().enumerate() {
        let output_idx = gate.output.index();
        if output_idx >= num_vars {
            replay.out_of_range_gate_outputs += 1;
        } else {
            output_counts[output_idx] = output_counts[output_idx].saturating_add(1);
            output_gate_indices[output_idx] = Some(gate_idx);
        }
        for input in &gate.inputs {
            if input.variable().index() >= num_vars {
                replay.out_of_range_gate_inputs += 1;
                if output_idx < num_vars {
                    malformed_output[output_idx] = true;
                }
            }
        }
    }

    for (idx, count) in output_counts.iter().copied().enumerate() {
        if count > 1 {
            replay.duplicate_gate_output_defs += u64::from(count - 1);
            malformed_output[idx] = true;
        }
    }

    let mut assigned = vec![false; num_vars];
    for (idx, count) in output_counts.iter().copied().enumerate() {
        if count == 0 {
            assigned[idx] = true;
            replay.frontier_vars += 1;
        }
    }

    let mut progress = true;
    while progress {
        progress = false;
        for (gate_idx, gate) in gates.iter().enumerate() {
            let output_idx = gate.output.index();
            if output_idx >= num_vars
                || output_counts[output_idx] != 1
                || assigned[output_idx]
                || !gate.inputs.iter().all(|lit| {
                    lit.variable().index() < num_vars && assigned[lit.variable().index()]
                })
            {
                continue;
            }
            assigned[output_idx] = true;
            replay.derivable_gate_output_vars += 1;
            replay.replay_order_gate_indices.push(gate_idx);
            progress = true;
        }
    }

    let mut blocked_outputs = vec![false; num_vars];
    for (idx, count) in output_counts.iter().copied().enumerate() {
        if count > 0 && !assigned[idx] {
            blocked_outputs[idx] = true;
            replay.blocked_gate_output_vars += 1;
            if count > 1 {
                replay.blocked_by_duplicate_output_vars += 1;
            } else if malformed_output[idx] {
                replay.blocked_by_malformed_dependency_output_vars += 1;
            }
        }
    }
    classify_blocked_dependencies(
        gates,
        &output_counts,
        &output_gate_indices,
        &blocked_outputs,
        &mut replay,
    );
    replay.frontier_vars += replay.blocked_gate_output_vars;
    replay.complete_original_model_vars =
        assigned.iter().filter(|assigned| **assigned).count() + replay.blocked_gate_output_vars;
    replay
}

fn classify_blocked_dependencies(
    gates: &[Gate],
    output_counts: &[u16],
    output_gate_indices: &[Option<usize>],
    blocked_outputs: &[bool],
    replay: &mut AssignmentReplayReport,
) {
    let mut graph = vec![Vec::<usize>::new(); blocked_outputs.len()];
    for (output_idx, is_blocked) in blocked_outputs.iter().copied().enumerate() {
        if !is_blocked || output_counts[output_idx] != 1 {
            continue;
        }
        let Some(gate_idx) = output_gate_indices[output_idx] else {
            replay.blocked_by_unresolved_dependency_output_vars += 1;
            continue;
        };
        for input in &gates[gate_idx].inputs {
            let input_idx = input.variable().index();
            if input_idx < blocked_outputs.len() && blocked_outputs[input_idx] {
                graph[output_idx].push(input_idx);
                replay.blocked_output_dependency_edges += 1;
            }
        }
    }

    let cyclic = cyclic_nodes(&graph, blocked_outputs);
    for (idx, is_blocked) in blocked_outputs.iter().copied().enumerate() {
        if !is_blocked || output_counts[idx] != 1 {
            continue;
        }
        if cyclic[idx] {
            replay.blocked_by_cycle_output_vars += 1;
        } else {
            replay.blocked_by_unresolved_dependency_output_vars += 1;
        }
    }
}

fn cyclic_nodes(graph: &[Vec<usize>], active: &[bool]) -> Vec<bool> {
    let mut state = vec![0u8; graph.len()];
    let mut stack = Vec::new();
    let mut in_stack = vec![false; graph.len()];
    let mut cyclic = vec![false; graph.len()];

    for node in 0..graph.len() {
        if active[node] && state[node] == 0 {
            mark_cycles_dfs(
                node,
                graph,
                active,
                &mut state,
                &mut stack,
                &mut in_stack,
                &mut cyclic,
            );
        }
    }
    cyclic
}

fn mark_cycles_dfs(
    node: usize,
    graph: &[Vec<usize>],
    active: &[bool],
    state: &mut [u8],
    stack: &mut Vec<usize>,
    in_stack: &mut [bool],
    cyclic: &mut [bool],
) {
    state[node] = 1;
    stack.push(node);
    in_stack[node] = true;

    for &next in &graph[node] {
        if !active[next] {
            continue;
        }
        if state[next] == 0 {
            mark_cycles_dfs(next, graph, active, state, stack, in_stack, cyclic);
        } else if in_stack[next] {
            if let Some(pos) = stack.iter().rposition(|&stack_node| stack_node == next) {
                for &cycle_node in &stack[pos..] {
                    cyclic[cycle_node] = true;
                }
            }
        }
    }

    in_stack[node] = false;
    stack.pop();
    state[node] = 2;
}

fn evaluate_gate(
    gate: &Gate,
    assignment: &[Option<bool>],
) -> Result<bool, CircuitModelMaterializationError> {
    let mut input_values = Vec::with_capacity(gate.inputs.len());
    for &input in &gate.inputs {
        input_values.push(literal_assignment_value(input, assignment).ok_or(
            CircuitModelMaterializationError::MissingReplayInput {
                gate_output_var: gate.output.index(),
                input_var: input.variable().index(),
            },
        )?);
    }
    let value = match gate.gate_type {
        GateType::And => input_values.iter().all(|value| *value),
        GateType::Xor => input_values.iter().fold(false, |acc, value| acc ^ *value),
        GateType::Ite => {
            if input_values.len() != 3 {
                return Err(CircuitModelMaterializationError::MalformedGate);
            }
            if input_values[0] {
                input_values[1]
            } else {
                input_values[2]
            }
        }
        GateType::Equiv => {
            if input_values.len() != 1 {
                return Err(CircuitModelMaterializationError::MalformedGate);
            }
            input_values[0]
        }
    };
    Ok(if gate.negated_output { !value } else { value })
}

fn literal_assignment_value(lit: Literal, assignment: &[Option<bool>]) -> Option<bool> {
    let var_value = (*assignment.get(lit.variable().index())?)?;
    Some(if lit.is_positive() {
        var_value
    } else {
        !var_value
    })
}

fn count_equivalence_classes(report: &mut CircuitScoutReport, num_vars: usize, gates: &[Gate]) {
    let mut dsu = LiteralDsu::new(num_vars.saturating_mul(2));
    for gate in gates {
        if gate.gate_type != GateType::Equiv || gate.inputs.len() != 1 {
            continue;
        }
        let output = Literal::positive(gate.output);
        let input = gate.inputs[0];
        dsu.union(output.index(), input.index());
        dsu.union(output.negated().index(), input.negated().index());
    }

    let mut class_sizes: DetHashMap<usize, u64> = DetHashMap::default();
    for var_idx in 0..num_vars {
        let root = dsu.find(Literal::positive(Variable(var_idx as u32)).index());
        *class_sizes.entry(root).or_insert(0) += 1;
    }
    for size in class_sizes.values().copied() {
        if size > 1 {
            report.equivalence_classes += 1;
            report.equivalence_members += size;
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct GateFingerprint {
    kind: u8,
    inputs: Vec<u32>,
    negated_output: bool,
}

fn count_structural_hashes(report: &mut CircuitScoutReport, gates: &[Gate]) {
    let mut fingerprints: DetHashMap<GateFingerprint, u64> = DetHashMap::default();
    for gate in gates {
        let mut inputs: Vec<u32> = gate.inputs.iter().map(|lit| lit.raw()).collect();
        inputs.sort_unstable();
        let fingerprint = GateFingerprint {
            kind: match gate.gate_type {
                GateType::And => 1,
                GateType::Xor => 2,
                GateType::Ite => 3,
                GateType::Equiv => 4,
            },
            inputs,
            negated_output: gate.negated_output,
        };
        *fingerprints.entry(fingerprint).or_insert(0) += 1;
    }
    for count in fingerprints.values().copied() {
        if count > 1 {
            report.structural_hash_groups += 1;
            report.structural_hash_opportunities += count - 1;
        }
    }
}

fn count_adder_and_multiplier_motifs(
    report: &mut CircuitScoutReport,
    num_vars: usize,
    gates: &[Gate],
) {
    let mut gate_outputs = vec![false; num_vars];
    for gate in gates {
        let idx = gate.output.index();
        if idx < gate_outputs.len() {
            gate_outputs[idx] = true;
        }
    }

    let mut and_by_pair: DetHashMap<[u32; 2], Vec<Variable>> = DetHashMap::default();
    let mut xor_by_pair: DetHashMap<[u32; 2], Vec<Variable>> = DetHashMap::default();
    let mut and_pair_present: DetHashMap<[u32; 2], u64> = DetHashMap::default();

    for gate in gates {
        if let Some(pair) = normalized_var_pair(&gate.inputs) {
            match gate.gate_type {
                GateType::And => {
                    and_by_pair.entry(pair).or_default().push(gate.output);
                    *and_pair_present.entry(pair).or_insert(0) += 1;
                    if gate.inputs.iter().all(|lit| {
                        let var_idx = lit.variable().index();
                        var_idx >= gate_outputs.len() || !gate_outputs[var_idx]
                    }) {
                        report.partial_product_ands += 1;
                    }
                }
                GateType::Xor => {
                    xor_by_pair.entry(pair).or_default().push(gate.output);
                }
                GateType::Ite | GateType::Equiv => {}
            }
        }
    }

    for (pair, xor_outputs) in &xor_by_pair {
        if let Some(and_outputs) = and_by_pair.get(pair) {
            report.half_adders += xor_outputs.len().min(and_outputs.len()) as u64;
            report.adder_carry_links += and_outputs.len() as u64;
        }
    }

    let mut chained_full_adders = 0u64;
    for first in gates.iter().filter(|gate| gate.gate_type == GateType::Xor) {
        if first.inputs.len() != 2 {
            continue;
        }
        let Some(first_pair) = normalized_var_pair(&first.inputs) else {
            continue;
        };
        if !and_pair_present.contains_key(&first_pair) {
            continue;
        }
        for second in gates.iter().filter(|gate| gate.gate_type == GateType::Xor) {
            if second.inputs.len() != 2
                || !second
                    .inputs
                    .iter()
                    .any(|lit| lit.variable() == first.output)
            {
                continue;
            }
            let Some(second_pair) = normalized_var_pair(&second.inputs) else {
                continue;
            };
            if and_pair_present.contains_key(&second_pair) {
                chained_full_adders += 1;
                report.adder_carry_links += 2;
            }
        }
    }

    let mut direct_full_adders = 0u64;
    for gate in gates.iter().filter(|gate| gate.gate_type == GateType::Xor) {
        if gate.inputs.len() != 3 {
            continue;
        }
        let mut matching_carry_pairs = 0u64;
        for pair in three_input_pairs(&gate.inputs) {
            if and_pair_present.contains_key(&pair) {
                matching_carry_pairs += 1;
            }
        }
        if matching_carry_pairs >= 2 {
            direct_full_adders += 1;
            report.adder_carry_links += matching_carry_pairs;
        }
    }
    report.full_adders = chained_full_adders + direct_full_adders;

    let adder_cones = report.half_adders + report.full_adders;
    if report.partial_product_ands >= MIN_MULTIPLIER_PARTIAL_PRODUCTS
        && adder_cones >= MIN_MULTIPLIER_ADDER_MOTIFS
    {
        report.multiplier_cones = 1;
    }
}

fn normalized_var_pair(inputs: &[Literal]) -> Option<[u32; 2]> {
    if inputs.len() != 2 {
        return None;
    }
    let mut pair = [inputs[0].variable().id(), inputs[1].variable().id()];
    if pair[0] == pair[1] {
        return None;
    }
    if pair[0] > pair[1] {
        pair.swap(0, 1);
    }
    Some(pair)
}

fn three_input_pairs(inputs: &[Literal]) -> [[u32; 2]; 3] {
    debug_assert_eq!(inputs.len(), 3);
    let vars = [
        inputs[0].variable().id(),
        inputs[1].variable().id(),
        inputs[2].variable().id(),
    ];
    [
        sorted_pair(vars[0], vars[1]),
        sorted_pair(vars[0], vars[2]),
        sorted_pair(vars[1], vars[2]),
    ]
}

fn sorted_pair(a: u32, b: u32) -> [u32; 2] {
    if a <= b {
        [a, b]
    } else {
        [b, a]
    }
}

fn is_dense_clique_shape(features: &SatFeatures) -> bool {
    features.num_vars > 0
        && features.num_vars <= 512
        && features.clause_var_ratio >= 10.0
        && features.frac_binary >= 0.95
        && features.frac_horn >= 0.95
        && features.pos_neg_balance_mean <= 0.15
        && features.clause_size_max >= 8
}

fn is_equivalence_chain_shape(report: &CircuitScoutReport) -> bool {
    report.gate_equiv >= 16
        && report.gate_xor == 0
        && report.gate_and == 0
        && report.half_adders + report.full_adders == 0
}

#[derive(Debug, Clone)]
struct LiteralDsu {
    parent: Vec<usize>,
    rank: Vec<u8>,
}

impl LiteralDsu {
    fn new(size: usize) -> Self {
        Self {
            parent: (0..size).collect(),
            rank: vec![0; size],
        }
    }

    fn find(&mut self, node: usize) -> usize {
        debug_assert!(node < self.parent.len());
        if self.parent[node] != node {
            let root = self.find(self.parent[node]);
            self.parent[node] = root;
        }
        self.parent[node]
    }

    fn union(&mut self, a: usize, b: usize) {
        if a >= self.parent.len() || b >= self.parent.len() {
            return;
        }
        let mut root_a = self.find(a);
        let mut root_b = self.find(b);
        if root_a == root_b {
            return;
        }
        if self.rank[root_a] < self.rank[root_b] {
            std::mem::swap(&mut root_a, &mut root_b);
        }
        self.parent[root_b] = root_a;
        if self.rank[root_a] == self.rank[root_b] {
            self.rank[root_a] += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dimacs::parse_str;
    use crate::test_util::lit;
    use std::collections::{BTreeMap, BTreeSet};
    use std::path::{Path, PathBuf};

    fn and_gate(clauses: &mut Vec<Vec<Literal>>, out: u32, a: u32, b: u32) {
        clauses.push(vec![lit(out, false), lit(a, true)]);
        clauses.push(vec![lit(out, false), lit(b, true)]);
        clauses.push(vec![lit(out, true), lit(a, false), lit(b, false)]);
    }

    fn xor2_gate(clauses: &mut Vec<Vec<Literal>>, out: u32, a: u32, b: u32) {
        clauses.push(vec![lit(out, true), lit(a, false), lit(b, false)]);
        clauses.push(vec![lit(out, true), lit(a, true), lit(b, true)]);
        clauses.push(vec![lit(out, false), lit(a, false), lit(b, true)]);
        clauses.push(vec![lit(out, false), lit(a, true), lit(b, false)]);
    }

    fn equiv_gate(clauses: &mut Vec<Vec<Literal>>, left: u32, right: u32) {
        clauses.push(vec![lit(left, true), lit(right, false)]);
        clauses.push(vec![lit(left, false), lit(right, true)]);
    }

    fn source_row(
        source_row_id: u64,
        var: usize,
        literal: Literal,
        clause_id: usize,
        source_value: bool,
        family: CircuitSourceFrameFamily,
        kind: CircuitSourceFrameKind,
    ) -> CircuitSourceFrameRow {
        CircuitSourceFrameRow {
            source_row_id,
            var,
            literal,
            clause_id,
            source_value,
            family,
            kind,
        }
    }

    const TEST_FORMULA_SHA256: &str =
        "1111111111111111111111111111111111111111111111111111111111111111";
    const TEST_MODEL_STDOUT_SHA256: &str =
        "2222222222222222222222222222222222222222222222222222222222222222";
    const TEST_CHECKER_VERDICT_SHA256: &str =
        "3333333333333333333333333333333333333333333333333333333333333333";

    fn artifact_identity(path: &str, sha256: &str) -> CircuitOriginalDimacsArtifactIdentity {
        CircuitOriginalDimacsArtifactIdentity {
            path: path.to_owned(),
            sha256: sha256.to_owned(),
        }
    }

    fn valid_model_authority_artifacts() -> CircuitOriginalDimacsModelAuthorityArtifacts {
        CircuitOriginalDimacsModelAuthorityArtifacts {
            formula: artifact_identity("original.cnf", TEST_FORMULA_SHA256),
            model_stdout: artifact_identity("ay-model.stdout", TEST_MODEL_STDOUT_SHA256),
            checker_command: vec![
                "ay".to_owned(),
                "check".to_owned(),
                "model".to_owned(),
                "--json".to_owned(),
                "original.cnf".to_owned(),
                "ay-model.stdout".to_owned(),
            ],
            checker_verdict_sha256: TEST_CHECKER_VERDICT_SHA256.to_owned(),
        }
    }

    fn valid_model_check_evidence(
        num_vars: usize,
        clauses_checked: u64,
    ) -> CircuitOriginalDimacsModelCheckEvidence {
        let artifacts = valid_model_authority_artifacts();
        CircuitOriginalDimacsModelCheckEvidence {
            schema: ORIGINAL_DIMACS_MODEL_CHECK_SCHEMA.to_owned(),
            formula: artifacts.formula,
            stdout: artifacts.model_stdout,
            model_status: ORIGINAL_DIMACS_VALID_MODEL_STATUS.to_owned(),
            valid: true,
            num_vars: Some(num_vars),
            clauses_checked,
            first_unsatisfied_clause: None,
            checker_command: artifacts.checker_command,
            checker_exit_status: 0,
            checker_verdict_sha256: artifacts.checker_verdict_sha256,
            ay_build_id: "test-build".to_owned(),
        }
    }

    fn retained_model_check_json(
        formula_path: &str,
        model_stdout_path: &str,
        num_vars: usize,
        clauses_checked: u64,
        valid: bool,
    ) -> Vec<u8> {
        render_original_dimacs_model_check_json(
            formula_path,
            model_stdout_path,
            num_vars,
            clauses_checked,
            valid,
            "test-build-stamp",
        )
        .into_bytes()
    }

    fn report_text(repo_relative: &str) -> String {
        let path = repo_root().join(repo_relative);
        std::fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()))
    }

    fn parsed_value_ledger(
        kind: CircuitSourceFrameValueLedgerKind,
        rows: &[(u64, usize, bool)],
    ) -> CircuitParsedSourceFrameValueLedger {
        CircuitParsedSourceFrameValueLedger {
            kind,
            rows: rows
                .iter()
                .map(
                    |&(source_row_id, var, value)| CircuitSourceFrameValueLedgerRow {
                        source_row_id,
                        ledger_row_id: format!("test_{source_row_id:04}"),
                        value: CircuitSourceFrameValue {
                            var,
                            value,
                            family: kind.family(),
                        },
                        present_in_w159_remaining_clause: false,
                        remaining_clause_ids_1_based: Vec::new(),
                        route_eligible: false,
                        route_blocker: Some("original_dimacs_validation_failed".to_owned()),
                    },
                )
                .collect(),
            stats: CircuitSourceFrameValueLedgerStats {
                rows_seen: rows.len(),
                rows_accepted: rows.len(),
                route_blocked_rows: rows.len(),
                ..CircuitSourceFrameValueLedgerStats::default()
            },
        }
    }

    #[test]
    fn circuit_scout_recovers_half_adder_and_hash_opportunity() {
        let mut clauses = Vec::new();
        xor2_gate(&mut clauses, 2, 0, 1);
        and_gate(&mut clauses, 3, 0, 1);
        and_gate(&mut clauses, 4, 0, 1);

        let report = scout_formula(5, &clauses);

        assert!(report.gate_xor >= 1, "got {report:?}");
        assert!(report.gate_and >= 2, "got {report:?}");
        assert!(report.half_adders >= 1, "got {report:?}");
        assert_eq!(report.multiplier_cones, 0);
        assert!(report.structural_hash_groups >= 1, "got {report:?}");
        assert!(report.structural_hash_opportunities >= 1, "got {report:?}");
        assert!(!report.route_candidate);
        assert_eq!(report.model_witness.complete_original_model_vars, 5);
        assert_eq!(
            report.model_witness.partial_assignment_required_vars
                + report.model_witness.derivable_gate_output_vars,
            5
        );
        assert!(!report.model_witness.fail_closed);
    }

    #[test]
    fn circuit_scout_recovers_equivalence_classes() {
        let mut clauses = Vec::new();
        equiv_gate(&mut clauses, 0, 1);
        equiv_gate(&mut clauses, 1, 2);
        equiv_gate(&mut clauses, 3, 4);

        let report = scout_formula(5, &clauses);

        assert!(report.gate_equiv >= 3, "got {report:?}");
        assert_eq!(report.equivalence_classes, 2);
        assert_eq!(report.equivalence_members, 5);
        assert!(!report.route_candidate);
        assert_eq!(report.rejection, CircuitScoutRejection::MissingGateMix);
        assert_eq!(report.model_witness.equivalence_alias_witnesses, 3);
        assert!(!report.model_witness.fail_closed);
    }

    #[test]
    fn circuit_scout_recovers_chained_full_adder_motif() {
        let mut clauses = Vec::new();
        xor2_gate(&mut clauses, 3, 0, 1);
        xor2_gate(&mut clauses, 4, 3, 2);
        and_gate(&mut clauses, 5, 0, 1);
        and_gate(&mut clauses, 6, 3, 2);

        let report = scout_formula(7, &clauses);

        assert!(report.gate_xor >= 2, "got {report:?}");
        assert!(report.gate_and >= 2, "got {report:?}");
        assert!(report.full_adders >= 1, "got {report:?}");
        assert!(report.adder_carry_links >= 2, "got {report:?}");
        assert!(!report.route_candidate);
        assert_eq!(
            report.rejection,
            CircuitScoutRejection::MissingMultiplierCone
        );
    }

    #[test]
    fn circuit_scout_materializes_acyclic_replay_assignment() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);

        let report = scout_formula(3, &clauses);

        assert_eq!(report.model_witness.derivable_gate_output_vars, 1);
        assert_eq!(report.model_witness.acyclic_replay_order_len, 1);
        assert_eq!(report.model_witness.blocked_gate_output_vars, 0);
        assert_eq!(report.model_witness.blocked_by_cycle_output_vars, 0);

        let direct = vec![Some(true), Some(false), None];
        let materialized = materialize_original_dimacs_assignment(3, &clauses, &direct)
            .expect("primary inputs should replay AND output");
        assert_eq!(materialized, vec![true, false, false]);
    }

    #[test]
    fn circuit_scout_source_clause_binding_preserves_original_rows_with_empty_clauses() {
        let clauses = vec![
            Vec::new(),
            vec![lit(2, false), lit(0, true)],
            Vec::new(),
            vec![lit(2, false), lit(1, true)],
            vec![lit(2, true), lit(0, false), lit(1, false)],
        ];

        let arena = build_clause_arena(3, &clauses);
        let recovered = recover_gates_with_source_bindings(3, &clauses);
        let gate = recovered
            .gates
            .iter()
            .find(|gate| gate.gate_type == GateType::And && gate.output.index() == 2)
            .expect("AND gate should be recovered");
        let mut source_clause_ids: Vec<_> = gate
            .defining_clauses
            .iter()
            .map(|&offset| arena.original_clause_id(offset).expect("source binding"))
            .collect();
        source_clause_ids.sort_unstable();
        let mut proof_clause_ids: Vec<_> = gate
            .defining_clauses
            .iter()
            .map(|&offset| {
                arena
                    .proof_clause_id_1_based(offset)
                    .expect("proof-facing source binding")
            })
            .collect();
        proof_clause_ids.sort_unstable();

        assert_eq!(source_clause_ids, vec![1, 3, 4]);
        assert_eq!(proof_clause_ids, vec![2, 4, 5]);
        assert_eq!(recovered.source_clause_binding.gate_clause_references, 3);
        assert_eq!(recovered.source_clause_binding.source_clause_bound_rows, 3);
        assert_eq!(
            recovered
                .source_clause_binding
                .source_clause_binding_missing_rows,
            0
        );
        assert!(!recovered.source_clause_binding.fail_closed);
    }

    #[test]
    fn circuit_scout_source_clause_binding_counts_missing_offsets_fail_closed() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);

        let gates = recover_gates(3, &clauses);
        let mut arena = build_clause_arena(3, &clauses);
        let removed_offset = gates[0].defining_clauses[0];
        arena.source_clause_by_offset.remove(&removed_offset);

        let report = audit_gate_source_clause_bindings(&gates, &arena, &clauses);

        assert_eq!(report.gate_clause_references, 3);
        assert_eq!(report.source_clause_bound_rows, 2);
        assert_eq!(report.source_clause_binding_missing_rows, 1);
        assert!(report.fail_closed);
    }

    #[test]
    fn circuit_scout_source_clause_binding_counts_literal_drift_fail_closed() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);

        let gates = recover_gates(3, &clauses);
        let arena = build_clause_arena(3, &clauses);
        let mut drifted_clauses = clauses.clone();
        drifted_clauses[0] = vec![lit(0, true)];

        let report = audit_gate_source_clause_bindings(&gates, &arena, &drifted_clauses);

        assert_eq!(report.gate_clause_references, 3);
        assert_eq!(report.source_clause_bound_rows, 2);
        assert_eq!(report.source_clause_literal_mismatch_rows, 1);
        assert!(report.fail_closed);
    }

    #[test]
    fn circuit_scout_source_clause_binding_counts_duplicates_and_bad_rows_fail_closed() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);

        let mut gates = recover_gates(3, &clauses);
        let duplicate_offset = gates[0].defining_clauses[0];
        gates[0].defining_clauses.push(duplicate_offset);
        let mut arena = build_clause_arena(3, &clauses);
        let bad_offset = gates[0].defining_clauses[1];
        arena.source_clause_by_offset.insert(
            bad_offset,
            CircuitSourceClauseBinding {
                source_clause_index: clauses.len(),
                source_clause_id_1_based: clauses.len() as u64 + 1,
                original_lits: clauses[1].clone(),
            },
        );

        let report = audit_gate_source_clause_bindings(&gates, &arena, &clauses);

        assert_eq!(report.gate_clause_references, 4);
        assert_eq!(report.source_clause_bound_rows, 2);
        assert_eq!(report.duplicate_gate_clause_reference_rows, 1);
        assert_eq!(report.source_clause_out_of_range_rows, 1);
        assert!(report.fail_closed);
    }

    #[test]
    fn circuit_scout_materializes_only_allowed_source_frame_families() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);

        let source_values = vec![
            CircuitSourceFrameValue {
                var: 0,
                value: true,
                family: CircuitSourceFrameFamily::W210Frontier,
            },
            CircuitSourceFrameValue {
                var: 1,
                value: false,
                family: CircuitSourceFrameFamily::ForcedGateReplayBridge,
            },
        ];

        let materialized =
            materialize_original_dimacs_assignment_from_source_frames(3, &clauses, &source_values)
                .expect("allowed source-frame families should seed AND replay");
        assert_eq!(materialized, vec![true, false, false]);
    }

    #[test]
    fn circuit_scout_source_frame_row_audit_accepts_allowed_rows() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);
        let source_rows = [
            source_row(
                10,
                0,
                lit(0, true),
                0,
                true,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            ),
            source_row(
                11,
                1,
                lit(1, true),
                1,
                false,
                CircuitSourceFrameFamily::ForcedGateReplayBridge,
                CircuitSourceFrameKind::ForcedGateReplayBridge,
            ),
        ];

        let materialized = materialize_original_dimacs_assignment_from_source_frame_rows(
            3,
            &clauses,
            &source_rows,
        )
        .expect("allowed source-frame rows should seed AND replay");

        assert_eq!(materialized.assignment, vec![true, false, false]);
        assert_eq!(materialized.audit.rows_seen, 2);
        assert_eq!(materialized.audit.rows_accepted, 2);
        assert_eq!(materialized.audit.rows_rejected, 0);
        assert_eq!(materialized.audit.unsupported_family, 0);
        assert_eq!(materialized.audit.var_out_of_range, 0);
        assert_eq!(materialized.audit.literal_var_mismatch, 0);
        assert_eq!(materialized.audit.clause_out_of_range, 0);
        assert_eq!(materialized.audit.literal_missing_from_clause, 0);
        assert_eq!(materialized.audit.conflicts, 0);
        assert_eq!(materialized.audit.original_clauses_checked, 3);
        assert_eq!(materialized.audit.residual_falsified_count, 0);
        assert!(materialized.audit.assignment_complete);
        assert!(materialized.audit.validation_passed);
    }

    #[test]
    fn circuit_scout_original_dimacs_sat_model_authority_accepts_artifact_bound_assignment() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);
        let source_rows = [
            source_row(
                100,
                0,
                lit(0, true),
                0,
                true,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            ),
            source_row(
                101,
                1,
                lit(1, true),
                1,
                false,
                CircuitSourceFrameFamily::W210SccChoice,
                CircuitSourceFrameKind::SccChoiceValue,
            ),
        ];
        let artifacts = valid_model_authority_artifacts();
        let evidence = valid_model_check_evidence(3, 3);

        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&artifacts),
            Some(&evidence),
        );

        assert_eq!(audit.source_frame_audit.rows_seen, 2);
        assert_eq!(audit.source_frame_audit.rows_accepted, 2);
        assert_eq!(audit.source_frame_audit.rows_rejected, 0);
        assert_eq!(audit.source_frame_audit.original_clauses_checked, 3);
        assert_eq!(audit.source_frame_audit.residual_falsified_count, 0);
        assert!(audit.source_frame_audit.assignment_complete);
        assert!(audit.source_frame_audit.validation_passed);
        assert_eq!(
            audit.materialized_assignment,
            Some(vec![true, false, false])
        );
        assert!(audit.retained_artifacts_supplied);
        assert!(audit.checker_evidence_supplied);
        assert_eq!(
            audit.retained_formula_sha256.as_deref(),
            Some(TEST_FORMULA_SHA256)
        );
        assert_eq!(
            audit.retained_model_stdout_sha256.as_deref(),
            Some(TEST_MODEL_STDOUT_SHA256)
        );
        assert_eq!(
            audit.checker_formula_sha256.as_deref(),
            Some(TEST_FORMULA_SHA256)
        );
        assert_eq!(
            audit.checker_model_stdout_sha256.as_deref(),
            Some(TEST_MODEL_STDOUT_SHA256)
        );
        assert_eq!(audit.checker_exit_status, Some(0));
        assert_eq!(
            audit.checker_verdict_sha256.as_deref(),
            Some(TEST_CHECKER_VERDICT_SHA256)
        );
        assert_eq!(
            audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Admitted
        );
        assert!(audit.authority_status.is_admitted());
        assert!(audit.sat_output_authority);
        assert!(audit.model_output_authority);
        assert!(!audit.proof_output_authority);
        assert!(audit.solver_verdict_authority);
    }

    #[test]
    fn circuit_scout_original_dimacs_sat_model_authority_accepts_produced_retained_artifacts() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);
        let source_rows = [
            source_row(
                105,
                0,
                lit(0, true),
                0,
                true,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            ),
            source_row(
                106,
                1,
                lit(1, true),
                1,
                false,
                CircuitSourceFrameFamily::W210SccChoice,
                CircuitSourceFrameKind::SccChoiceValue,
            ),
        ];
        let packet = produce_original_dimacs_sat_model_authority_packet(
            3,
            &clauses,
            &source_rows,
            "retained/original.cnf",
            "retained/ay-model.stdout",
            vec![
                "ay".to_owned(),
                "check".to_owned(),
                "model".to_owned(),
                "--json".to_owned(),
                "retained/original.cnf".to_owned(),
                "retained/ay-model.stdout".to_owned(),
            ],
            0,
            retained_model_check_json(
                "retained/original.cnf",
                "retained/ay-model.stdout",
                3,
                3,
                true,
            ),
        )
        .expect("complete source rows should produce retained artifacts");

        assert_eq!(
            std::str::from_utf8(&packet.formula_dimacs).expect("utf8 dimacs"),
            "p cnf 3 3\n-3 1 0\n-3 2 0\n3 -1 -2 0\n"
        );
        assert_eq!(
            std::str::from_utf8(&packet.model_stdout).expect("utf8 model"),
            "s SATISFIABLE\nv 1 -2 -3 0\n"
        );
        assert_eq!(
            packet.artifacts.formula.sha256,
            sha256_hex(&packet.formula_dimacs)
        );
        assert_eq!(
            packet.artifacts.model_stdout.sha256,
            sha256_hex(&packet.model_stdout)
        );
        assert_eq!(
            packet.artifacts.checker_verdict_sha256,
            sha256_hex(&packet.checker_verdict_json)
        );
        assert_eq!(packet.checker_evidence.num_vars, Some(3));
        assert_eq!(packet.checker_evidence.clauses_checked, 3);
        assert_eq!(packet.checker_evidence.first_unsatisfied_clause, None);
        assert_eq!(packet.checker_evidence.checker_exit_status, 0);
        assert_eq!(
            packet.checker_evidence.ay_build_id.as_str(),
            "test-build-stamp"
        );

        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&packet.artifacts),
            Some(&packet.checker_evidence),
        );

        assert_eq!(
            audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Admitted
        );
        assert!(audit.sat_output_authority);
        assert!(audit.model_output_authority);
        assert!(!audit.proof_output_authority);
        assert!(audit.solver_verdict_authority);
    }

    #[test]
    fn circuit_scout_original_dimacs_sat_model_authority_rejects_retained_artifact_drift() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);
        let source_rows = [
            source_row(
                107,
                0,
                lit(0, true),
                0,
                true,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            ),
            source_row(
                108,
                1,
                lit(1, true),
                1,
                false,
                CircuitSourceFrameFamily::W210SccChoice,
                CircuitSourceFrameKind::SccChoiceValue,
            ),
        ];
        let packet = produce_original_dimacs_sat_model_authority_packet(
            3,
            &clauses,
            &source_rows,
            "retained/original.cnf",
            "retained/ay-model.stdout",
            vec![
                "ay".to_owned(),
                "check".to_owned(),
                "model".to_owned(),
                "--json".to_owned(),
                "retained/original.cnf".to_owned(),
                "retained/ay-model.stdout".to_owned(),
            ],
            0,
            retained_model_check_json(
                "retained/original.cnf",
                "retained/ay-model.stdout",
                3,
                3,
                true,
            ),
        )
        .expect("complete source rows should produce retained artifacts");

        let mut formula_drift = packet.artifacts.clone();
        formula_drift.formula.sha256 = sha256_hex(b"drifted formula");
        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&formula_drift),
            Some(&packet.checker_evidence),
        );
        assert_eq!(
            audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::FormulaArtifactHashMismatch
            )
        );
        assert!(audit.authority_is_absent());

        let mut model_drift = packet.artifacts.clone();
        model_drift.model_stdout.sha256 = sha256_hex(b"drifted model");
        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&model_drift),
            Some(&packet.checker_evidence),
        );
        assert_eq!(
            audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::ModelStdoutArtifactHashMismatch
            )
        );
        assert!(audit.authority_is_absent());

        let mut verdict_drift = packet.artifacts.clone();
        verdict_drift.checker_verdict_sha256 = sha256_hex(b"drifted verdict");
        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&verdict_drift),
            Some(&packet.checker_evidence),
        );
        assert_eq!(
            audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerVerdictHashMismatch
            )
        );
        assert!(audit.authority_is_absent());

        let formula_path_drift = produce_original_dimacs_sat_model_authority_packet(
            3,
            &clauses,
            &source_rows,
            "retained/original.cnf",
            "retained/ay-model.stdout",
            vec![
                "ay".to_owned(),
                "check".to_owned(),
                "model".to_owned(),
                "--json".to_owned(),
                "retained/original.cnf".to_owned(),
                "retained/ay-model.stdout".to_owned(),
            ],
            0,
            retained_model_check_json(
                "retained/drifted.cnf",
                "retained/ay-model.stdout",
                3,
                3,
                true,
            ),
        )
        .expect("path-drift checker verdict should still bind for audit rejection");
        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&formula_path_drift.artifacts),
            Some(&formula_path_drift.checker_evidence),
        );
        assert_eq!(
            audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::FormulaArtifactPathMismatch
            )
        );
        assert!(audit.authority_is_absent());

        let model_path_drift = produce_original_dimacs_sat_model_authority_packet(
            3,
            &clauses,
            &source_rows,
            "retained/original.cnf",
            "retained/ay-model.stdout",
            vec![
                "ay".to_owned(),
                "check".to_owned(),
                "model".to_owned(),
                "--json".to_owned(),
                "retained/original.cnf".to_owned(),
                "retained/ay-model.stdout".to_owned(),
            ],
            0,
            retained_model_check_json(
                "retained/original.cnf",
                "retained/drifted.stdout",
                3,
                3,
                true,
            ),
        )
        .expect("stdout-path-drift checker verdict should still bind for audit rejection");
        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&model_path_drift.artifacts),
            Some(&model_path_drift.checker_evidence),
        );
        assert_eq!(
            audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::ModelStdoutArtifactPathMismatch
            )
        );
        assert!(audit.authority_is_absent());
    }

    #[test]
    fn circuit_scout_original_dimacs_sat_model_authority_requires_checker_validated_produced_model()
    {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);
        let source_rows = [
            source_row(
                109,
                0,
                lit(0, true),
                0,
                true,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            ),
            source_row(
                110,
                1,
                lit(1, true),
                1,
                false,
                CircuitSourceFrameFamily::W210SccChoice,
                CircuitSourceFrameKind::SccChoiceValue,
            ),
        ];
        let invalid_packet = produce_original_dimacs_sat_model_authority_packet(
            3,
            &clauses,
            &source_rows,
            "retained/original.cnf",
            "retained/ay-model.stdout",
            vec![
                "ay".to_owned(),
                "check".to_owned(),
                "model".to_owned(),
                "--json".to_owned(),
                "retained/original.cnf".to_owned(),
                "retained/ay-model.stdout".to_owned(),
            ],
            0,
            retained_model_check_json(
                "retained/original.cnf",
                "retained/ay-model.stdout",
                3,
                3,
                false,
            ),
        )
        .expect("invalid retained checker verdict should bind before audit rejection");

        let missing_checker = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&invalid_packet.artifacts),
            None,
        );
        assert_eq!(
            missing_checker.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerEvidenceMissing
            )
        );
        assert!(missing_checker.authority_is_absent());

        let invalid_checker = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&invalid_packet.artifacts),
            Some(&invalid_packet.checker_evidence),
        );
        assert_eq!(
            invalid_checker.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerModelStatusNotValid
            )
        );
        assert!(invalid_checker.authority_is_absent());
    }

    #[test]
    fn circuit_scout_original_dimacs_sat_model_authority_producer_rejects_bad_materialization() {
        let incomplete = produce_original_dimacs_sat_model_authority_packet(
            2,
            &[vec![lit(0, true)], vec![lit(1, true)]],
            &[source_row(
                125,
                0,
                lit(0, true),
                0,
                true,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            )],
            "retained/original.cnf",
            "retained/ay-model.stdout",
            vec!["ay".to_owned(), "check".to_owned(), "model".to_owned()],
            0,
            retained_model_check_json(
                "retained/original.cnf",
                "retained/ay-model.stdout",
                2,
                2,
                true,
            ),
        );
        assert_eq!(
            incomplete,
            Err(
                CircuitOriginalDimacsSatModelAuthorityProductionError::Materialization(
                    CircuitModelMaterializationError::MissingDirectValue { var: 1 }
                )
            )
        );

        let conflicting = produce_original_dimacs_sat_model_authority_packet(
            1,
            &[vec![lit(0, true), lit(0, false)]],
            &[
                source_row(
                    126,
                    0,
                    lit(0, true),
                    0,
                    true,
                    CircuitSourceFrameFamily::W210Frontier,
                    CircuitSourceFrameKind::FrontierValue,
                ),
                source_row(
                    127,
                    0,
                    lit(0, false),
                    0,
                    false,
                    CircuitSourceFrameFamily::W210SccChoice,
                    CircuitSourceFrameKind::SccChoiceValue,
                ),
            ],
            "retained/original.cnf",
            "retained/ay-model.stdout",
            vec!["ay".to_owned(), "check".to_owned(), "model".to_owned()],
            0,
            retained_model_check_json(
                "retained/original.cnf",
                "retained/ay-model.stdout",
                1,
                1,
                true,
            ),
        );
        assert_eq!(
            conflicting,
            Err(
                CircuitOriginalDimacsSatModelAuthorityProductionError::Materialization(
                    CircuitModelMaterializationError::ConflictingSourceFrameValue { var: 0 }
                )
            )
        );

        let literal_unbound = produce_original_dimacs_sat_model_authority_packet(
            1,
            &[vec![lit(0, true)]],
            &[source_row(
                128,
                0,
                lit(0, false),
                0,
                false,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            )],
            "retained/original.cnf",
            "retained/ay-model.stdout",
            vec!["ay".to_owned(), "check".to_owned(), "model".to_owned()],
            0,
            retained_model_check_json(
                "retained/original.cnf",
                "retained/ay-model.stdout",
                1,
                1,
                true,
            ),
        );
        assert_eq!(
            literal_unbound,
            Err(
                CircuitOriginalDimacsSatModelAuthorityProductionError::Materialization(
                    CircuitModelMaterializationError::SourceFrameLiteralMissingFromClause {
                        source_row_id: 128,
                        clause_id: 0,
                        literal: lit(0, false),
                    }
                )
            )
        );

        let residual = produce_original_dimacs_sat_model_authority_packet(
            1,
            &[vec![lit(0, true)], vec![lit(0, false)]],
            &[source_row(
                129,
                0,
                lit(0, false),
                1,
                false,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            )],
            "retained/original.cnf",
            "retained/ay-model.stdout",
            vec!["ay".to_owned(), "check".to_owned(), "model".to_owned()],
            0,
            retained_model_check_json(
                "retained/original.cnf",
                "retained/ay-model.stdout",
                1,
                2,
                true,
            ),
        );
        assert_eq!(
            residual,
            Err(
                CircuitOriginalDimacsSatModelAuthorityProductionError::Materialization(
                    CircuitModelMaterializationError::SourceFrameResidualNonZero {
                        residual_falsified_count: 1,
                        first_clause: 0,
                    }
                )
            )
        );
    }

    #[test]
    fn circuit_scout_original_dimacs_sat_model_authority_rejects_malformed_checker_json() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);
        let source_rows = [
            source_row(
                130,
                0,
                lit(0, true),
                0,
                true,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            ),
            source_row(
                131,
                1,
                lit(1, true),
                1,
                false,
                CircuitSourceFrameFamily::W210SccChoice,
                CircuitSourceFrameKind::SccChoiceValue,
            ),
        ];
        let malformed = produce_original_dimacs_sat_model_authority_packet(
            3,
            &clauses,
            &source_rows,
            "retained/original.cnf",
            "retained/ay-model.stdout",
            vec!["ay".to_owned(), "check".to_owned(), "model".to_owned()],
            0,
            b"{not json".to_vec(),
        );
        assert_eq!(
            malformed,
            Err(
                CircuitOriginalDimacsSatModelAuthorityProductionError::Binding(
                    CircuitOriginalDimacsModelCheckEvidenceBindingError::CheckerVerdictJsonInvalid
                )
            )
        );
    }

    #[test]
    fn circuit_scout_original_dimacs_sat_model_authority_requires_checker_evidence() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);
        let source_rows = [
            source_row(
                110,
                0,
                lit(0, true),
                0,
                true,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            ),
            source_row(
                111,
                1,
                lit(1, true),
                1,
                false,
                CircuitSourceFrameFamily::W210SccChoice,
                CircuitSourceFrameKind::SccChoiceValue,
            ),
        ];
        let artifacts = valid_model_authority_artifacts();

        let missing = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&artifacts),
            None,
        );

        assert_eq!(
            missing.materialized_assignment,
            Some(vec![true, false, false])
        );
        assert_eq!(
            missing.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerEvidenceMissing
            )
        );
        assert!(missing.authority_is_absent());

        let mut mismatched = valid_model_check_evidence(3, 2);
        let clauses_mismatch = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&artifacts),
            Some(&mismatched),
        );
        assert_eq!(
            clauses_mismatch.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerClausesCheckedMismatch
            )
        );
        assert!(clauses_mismatch.authority_is_absent());

        mismatched.clauses_checked = 3;
        mismatched.valid = false;
        let invalid = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&artifacts),
            Some(&mismatched),
        );
        assert_eq!(
            invalid.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerVerdictInvalid
            )
        );
        assert!(invalid.authority_is_absent());
    }

    #[test]
    fn circuit_scout_original_dimacs_sat_model_authority_rejects_shape_only_evidence() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);
        let source_rows = [
            source_row(
                115,
                0,
                lit(0, true),
                0,
                true,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            ),
            source_row(
                116,
                1,
                lit(1, true),
                1,
                false,
                CircuitSourceFrameFamily::W210SccChoice,
                CircuitSourceFrameKind::SccChoiceValue,
            ),
        ];
        let evidence = valid_model_check_evidence(3, 3);

        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            None,
            Some(&evidence),
        );

        assert_eq!(
            audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::RetainedArtifactsMissing
            )
        );
        assert_eq!(
            audit.materialized_assignment,
            Some(vec![true, false, false])
        );
        assert!(audit.checker_evidence_supplied);
        assert!(audit.authority_is_absent());
    }

    #[test]
    fn circuit_scout_original_dimacs_sat_model_authority_binds_artifact_hashes_and_checker_status()
    {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);
        let source_rows = [
            source_row(
                117,
                0,
                lit(0, true),
                0,
                true,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            ),
            source_row(
                118,
                1,
                lit(1, true),
                1,
                false,
                CircuitSourceFrameFamily::W210SccChoice,
                CircuitSourceFrameKind::SccChoiceValue,
            ),
        ];
        let artifacts = valid_model_authority_artifacts();

        let mut formula_hash_mismatch = valid_model_check_evidence(3, 3);
        formula_hash_mismatch.formula.sha256 =
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_owned();
        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&artifacts),
            Some(&formula_hash_mismatch),
        );
        assert_eq!(
            audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::FormulaArtifactHashMismatch
            )
        );
        assert!(audit.authority_is_absent());

        let mut model_hash_mismatch = valid_model_check_evidence(3, 3);
        model_hash_mismatch.stdout.sha256 =
            "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_owned();
        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&artifacts),
            Some(&model_hash_mismatch),
        );
        assert_eq!(
            audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::ModelStdoutArtifactHashMismatch
            )
        );
        assert!(audit.authority_is_absent());

        let mut checker_failed = valid_model_check_evidence(3, 3);
        checker_failed.checker_exit_status = 1;
        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&artifacts),
            Some(&checker_failed),
        );
        assert_eq!(
            audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerExitStatusNonZero
            )
        );
        assert!(audit.authority_is_absent());

        let mut checker_command_mismatch = valid_model_check_evidence(3, 3);
        checker_command_mismatch
            .checker_command
            .push("--unexpected".to_owned());
        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&artifacts),
            Some(&checker_command_mismatch),
        );
        assert_eq!(
            audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerCommandMismatch
            )
        );
        assert!(audit.authority_is_absent());

        let mut checker_verdict_mismatch = valid_model_check_evidence(3, 3);
        checker_verdict_mismatch.checker_verdict_sha256 =
            "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc".to_owned();
        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&artifacts),
            Some(&checker_verdict_mismatch),
        );
        assert_eq!(
            audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerVerdictHashMismatch
            )
        );
        assert!(audit.authority_is_absent());
    }

    #[test]
    fn circuit_scout_original_dimacs_sat_model_authority_rejects_residual_assignment() {
        let clauses = vec![vec![lit(0, true)], vec![lit(1, true)]];
        let source_rows = [
            source_row(
                120,
                0,
                lit(0, true),
                0,
                false,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            ),
            source_row(
                121,
                1,
                lit(1, true),
                1,
                true,
                CircuitSourceFrameFamily::W210SccChoice,
                CircuitSourceFrameKind::SccChoiceValue,
            ),
        ];
        let artifacts = valid_model_authority_artifacts();
        let evidence = valid_model_check_evidence(2, 2);

        let audit = audit_original_dimacs_sat_model_authority(
            2,
            &clauses,
            &source_rows,
            Some(&artifacts),
            Some(&evidence),
        );

        assert!(audit.checker_evidence_supplied);
        assert_eq!(audit.source_frame_audit.rows_accepted, 2);
        assert!(audit.source_frame_audit.assignment_complete);
        assert!(!audit.source_frame_audit.validation_passed);
        assert_eq!(audit.source_frame_audit.residual_falsified_count, 1);
        assert_eq!(audit.source_frame_audit.residual_clause_ids, vec![0]);
        assert_eq!(audit.materialized_assignment, None);
        assert_eq!(
            audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::SourceFrameValidationFailed
            )
        );
        assert!(audit.authority_is_absent());
    }

    #[test]
    fn circuit_scout_rejects_proxy_only_source_frame_families() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);

        let w377 = [CircuitSourceFrameValue {
            var: 0,
            value: true,
            family: CircuitSourceFrameFamily::W377CombinedSelector,
        }];
        assert_eq!(
            materialize_original_dimacs_assignment_from_source_frames(3, &clauses, &w377),
            Err(
                CircuitModelMaterializationError::RejectedSourceFrameFamily {
                    var: 0,
                    family: CircuitSourceFrameFamily::W377CombinedSelector
                }
            )
        );

        let proxy_only = [CircuitSourceFrameValue {
            var: 1,
            value: false,
            family: CircuitSourceFrameFamily::ProxyOnlySelector,
        }];
        assert_eq!(
            materialize_original_dimacs_assignment_from_source_frames(3, &clauses, &proxy_only),
            Err(
                CircuitModelMaterializationError::RejectedSourceFrameFamily {
                    var: 1,
                    family: CircuitSourceFrameFamily::ProxyOnlySelector
                }
            )
        );
    }

    #[test]
    fn circuit_scout_source_frame_row_audit_rejects_proxy_missing_and_conflicting_rows() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);

        let proxy = [source_row(
            20,
            0,
            lit(0, true),
            0,
            true,
            CircuitSourceFrameFamily::W377CombinedSelector,
            CircuitSourceFrameKind::DirectValue,
        )];
        let proxy_audit = audit_source_frame_rows(3, &clauses, &proxy);
        assert_eq!(proxy_audit.rows_seen, 1);
        assert_eq!(proxy_audit.rows_rejected, 1);
        assert_eq!(proxy_audit.unsupported_family, 1);
        assert!(!proxy_audit.validation_passed);
        assert_eq!(
            materialize_original_dimacs_assignment_from_source_frame_rows(3, &clauses, &proxy),
            Err(
                CircuitModelMaterializationError::RejectedSourceFrameFamily {
                    var: 0,
                    family: CircuitSourceFrameFamily::W377CombinedSelector
                }
            )
        );

        let missing = [source_row(
            21,
            0,
            lit(0, true),
            0,
            true,
            CircuitSourceFrameFamily::W210Frontier,
            CircuitSourceFrameKind::FrontierValue,
        )];
        let missing_audit = audit_source_frame_rows(3, &clauses, &missing);
        assert_eq!(missing_audit.rows_accepted, 1);
        assert_eq!(missing_audit.missing_source_rows, 2);
        assert!(!missing_audit.assignment_complete);
        assert!(!missing_audit.validation_passed);

        let conflicting = [
            source_row(
                22,
                0,
                lit(0, true),
                0,
                true,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            ),
            source_row(
                23,
                0,
                lit(0, true),
                0,
                false,
                CircuitSourceFrameFamily::W210SccChoice,
                CircuitSourceFrameKind::SccChoiceValue,
            ),
        ];
        let conflict_audit = audit_source_frame_rows(3, &clauses, &conflicting);
        assert_eq!(conflict_audit.rows_accepted, 1);
        assert_eq!(conflict_audit.rows_rejected, 1);
        assert_eq!(conflict_audit.conflicts, 1);
        assert_eq!(
            materialize_original_dimacs_assignment_from_source_frame_rows(
                3,
                &clauses,
                &conflicting,
            ),
            Err(CircuitModelMaterializationError::ConflictingSourceFrameValue { var: 0 })
        );
    }

    #[test]
    fn circuit_scout_source_frame_row_audit_rejects_clause_literal_var_mismatches() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);

        let var_mismatch = [source_row(
            30,
            0,
            lit(1, true),
            1,
            true,
            CircuitSourceFrameFamily::W210Frontier,
            CircuitSourceFrameKind::FrontierValue,
        )];
        let var_mismatch_audit = audit_source_frame_rows(3, &clauses, &var_mismatch);
        assert_eq!(var_mismatch_audit.literal_var_mismatch, 1);
        assert_eq!(
            materialize_original_dimacs_assignment_from_source_frame_rows(
                3,
                &clauses,
                &var_mismatch,
            ),
            Err(
                CircuitModelMaterializationError::SourceFrameLiteralVarMismatch {
                    source_row_id: 30,
                    var: 0,
                    literal_var: 1
                }
            )
        );

        let clause_out_of_range = [source_row(
            31,
            0,
            lit(0, true),
            99,
            true,
            CircuitSourceFrameFamily::W210Frontier,
            CircuitSourceFrameKind::FrontierValue,
        )];
        let clause_audit = audit_source_frame_rows(3, &clauses, &clause_out_of_range);
        assert_eq!(clause_audit.clause_out_of_range, 1);
        assert_eq!(
            materialize_original_dimacs_assignment_from_source_frame_rows(
                3,
                &clauses,
                &clause_out_of_range,
            ),
            Err(
                CircuitModelMaterializationError::SourceFrameClauseOutOfRange {
                    source_row_id: 31,
                    clause_id: 99
                }
            )
        );

        let literal_missing = [source_row(
            32,
            0,
            lit(0, true),
            1,
            true,
            CircuitSourceFrameFamily::W210Frontier,
            CircuitSourceFrameKind::FrontierValue,
        )];
        let literal_audit = audit_source_frame_rows(3, &clauses, &literal_missing);
        assert_eq!(literal_audit.literal_missing_from_clause, 1);
        assert_eq!(
            materialize_original_dimacs_assignment_from_source_frame_rows(
                3,
                &clauses,
                &literal_missing,
            ),
            Err(
                CircuitModelMaterializationError::SourceFrameLiteralMissingFromClause {
                    source_row_id: 32,
                    clause_id: 1,
                    literal: lit(0, true)
                }
            )
        );
    }

    #[test]
    fn circuit_scout_source_frame_materializer_is_fail_closed() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);

        let out_of_range = [CircuitSourceFrameValue {
            var: 3,
            value: true,
            family: CircuitSourceFrameFamily::W210SccChoice,
        }];
        assert_eq!(
            materialize_original_dimacs_assignment_from_source_frames(3, &clauses, &out_of_range),
            Err(CircuitModelMaterializationError::SourceFrameVarOutOfRange { var: 3 })
        );

        let conflicting = [
            CircuitSourceFrameValue {
                var: 0,
                value: true,
                family: CircuitSourceFrameFamily::W210Frontier,
            },
            CircuitSourceFrameValue {
                var: 0,
                value: false,
                family: CircuitSourceFrameFamily::W210SccChoice,
            },
        ];
        assert_eq!(
            materialize_original_dimacs_assignment_from_source_frames(3, &clauses, &conflicting),
            Err(CircuitModelMaterializationError::ConflictingSourceFrameValue { var: 0 })
        );
    }

    #[test]
    fn circuit_scout_source_frame_materializer_reports_missing_direct_values_before_replay() {
        let mut clauses = Vec::new();
        and_gate(&mut clauses, 2, 0, 1);
        let source_rows = [source_row(
            34,
            0,
            lit(0, true),
            0,
            true,
            CircuitSourceFrameFamily::W210Frontier,
            CircuitSourceFrameKind::FrontierValue,
        )];

        assert_eq!(
            materialize_original_dimacs_assignment_from_source_frame_rows(
                3,
                &clauses,
                &source_rows,
            ),
            Err(CircuitModelMaterializationError::MissingDirectValue { var: 1 })
        );
    }

    #[test]
    fn circuit_scout_categorizes_cyclic_replay_blockers() {
        let mut clauses = Vec::new();
        equiv_gate(&mut clauses, 0, 1);
        equiv_gate(&mut clauses, 1, 0);

        let report = scout_formula(2, &clauses);

        assert_eq!(report.model_witness.derivable_gate_output_vars, 0);
        assert_eq!(report.model_witness.acyclic_replay_order_len, 0);
        assert_eq!(report.model_witness.blocked_gate_output_vars, 2);
        assert_eq!(report.model_witness.blocked_by_cycle_output_vars, 2);
        assert_eq!(report.model_witness.blocked_output_dependency_edges, 2);
        assert_eq!(
            materialize_original_dimacs_assignment(2, &clauses, &[Some(true), None]),
            Err(CircuitModelMaterializationError::MissingDirectValue { var: 1 })
        );
    }

    /// Synthetic-shape coverage of the clique / equivalence-chain negative
    /// routes. These build dense-clique and equivalence-chain formulas directly
    /// and assert that `scout_formula` rejects them. This is *not* a stand-in
    /// for the real benchmark fixtures: it exercises the rejection logic on
    /// known shapes that always exist regardless of optional benchmark files.
    #[test]
    fn circuit_scout_rejects_synthetic_clique_and_equivalence_chain_shapes() {
        let clique = synthetic_dense_clique_rejection_report();
        assert!(!clique.route_candidate);
        assert_eq!(clique.rejection, CircuitScoutRejection::DenseCliqueShape);

        let fmla = synthetic_equivalence_chain_rejection_report();
        assert!(!fmla.route_candidate);
        assert_ne!(fmla.rejection, CircuitScoutRejection::None);
    }

    /// Real-benchmark coverage of the clique / equivalence-chain negative
    /// routes. Each optional fixture is exercised only when present, but its
    /// absence is reported explicitly via the test harness rather than being
    /// silently replaced with a synthetic formula crafted to pass. This way a
    /// green result never implies the real benchmark ran when it did not.
    #[test]
    fn circuit_scout_keeps_clique_and_fmla_negative_routes() {
        let mut exercised_any = false;

        if let Some(clique) = scout_optional_benchmark(
            "benchmarks/sat/satcomp2024-sample/cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz",
        ) {
            exercised_any = true;
            assert!(!clique.route_candidate);
            assert_eq!(clique.rejection, CircuitScoutRejection::DenseCliqueShape);
        } else {
            eprintln!(
                "circuit_scout_keeps_clique_and_fmla_negative_routes: skipping clique fixture \
                 (benchmarks/sat/satcomp2024-sample/cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz \
                 not present); synthetic-shape coverage runs in \
                 circuit_scout_rejects_synthetic_clique_and_equivalence_chain_shapes"
            );
        }

        if let Some(fmla) = scout_optional_benchmark(
            "benchmarks/sat/satcomp2024-sample/9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf.xz",
        ) {
            exercised_any = true;
            assert!(!fmla.route_candidate);
            assert_ne!(fmla.rejection, CircuitScoutRejection::None);
        } else {
            eprintln!(
                "circuit_scout_keeps_clique_and_fmla_negative_routes: skipping fmla fixture \
                 (benchmarks/sat/satcomp2024-sample/9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf.xz \
                 not present); synthetic-shape coverage runs in \
                 circuit_scout_rejects_synthetic_clique_and_equivalence_chain_shapes"
            );
        }

        if !exercised_any {
            eprintln!(
                "circuit_scout_keeps_clique_and_fmla_negative_routes: no real benchmark fixtures \
                 present; only synthetic-shape coverage applies this run"
            );
        }
    }

    #[test]
    fn circuit_scout_recovers_multiplier22_candidate_structure() {
        let report = scout_required_benchmark(
            "benchmarks/sat/satcomp2024-sample/c5ae0ec49de0959cd14431ce851c14f8-Circuit_multiplier22.cnf.xz",
        );

        assert_eq!(report.num_vars, 1_013);
        assert_eq!(report.num_clauses, 18_793);
        assert!(
            report.gate_and >= 2,
            "Circuit_multiplier22 should expose AND structure, got {report:?}"
        );
        assert!(
            report.gate_xor >= 1,
            "Circuit_multiplier22 should expose XOR structure, got {report:?}"
        );
        assert!(
            report.half_adders + report.full_adders >= 1,
            "Circuit_multiplier22 should expose adder structure, got {report:?}"
        );
        assert!(
            report.route_candidate,
            "Circuit_multiplier22 should be a default-off circuit route candidate, got {report:?}"
        );
        assert_eq!(
            report.model_witness.gate_output_witnesses,
            report.gates_total
        );
        assert_eq!(report.model_witness.xor_output_witnesses, report.gate_xor);
        assert_eq!(report.model_witness.and_output_witnesses, report.gate_and);
        assert_eq!(
            report.model_witness.equiv_output_witnesses,
            report.gate_equiv
        );
        assert_eq!(
            report.model_witness.adder_sum_witnesses,
            report.half_adders + report.full_adders
        );
        assert_eq!(
            report.model_witness.adder_carry_witnesses,
            report.adder_carry_links
        );
        assert_eq!(
            report.model_witness.partial_product_witnesses,
            report.partial_product_ands
        );
        assert_eq!(
            report.model_witness.complete_original_model_vars,
            report.num_vars
        );
        assert_eq!(
            report.model_witness.partial_assignment_required_vars
                + report.model_witness.derivable_gate_output_vars,
            report.num_vars
        );
        assert_eq!(report.model_witness.acyclic_replay_order_len, 2);
        assert_eq!(report.model_witness.blocked_gate_output_vars, 508);
        assert_eq!(report.model_witness.blocked_by_duplicate_output_vars, 0);
        assert_eq!(
            report
                .model_witness
                .blocked_by_malformed_dependency_output_vars,
            0
        );
        assert_eq!(
            report
                .model_witness
                .blocked_by_unresolved_dependency_output_vars,
            report.model_witness.blocked_gate_output_vars
                - report.model_witness.blocked_by_cycle_output_vars
        );
        assert!(
            report.model_witness.blocked_by_cycle_output_vars > 0,
            "Circuit_multiplier22 should expose cyclic blocked-output dependencies, got {report:?}"
        );
        assert_eq!(
            report.model_witness.blocked_by_cycle_output_vars
                + report
                    .model_witness
                    .blocked_by_unresolved_dependency_output_vars
                + report.model_witness.blocked_by_duplicate_output_vars
                + report
                    .model_witness
                    .blocked_by_malformed_dependency_output_vars,
            report.model_witness.blocked_gate_output_vars
        );
        assert!(
            report.model_witness.blocked_output_dependency_edges >= 508,
            "Circuit_multiplier22 should expose blocked-output dependencies, got {report:?}"
        );
        assert!(!report.model_witness.fail_closed, "got {report:?}");
        eprintln!(
            "Circuit_multiplier22 model witness: {:?}",
            report.model_witness
        );
    }

    #[test]
    fn circuit_scout_original_dimacs_validation_is_fail_closed() {
        let clauses = vec![vec![lit(0, true), lit(1, true)], vec![lit(0, false)]];
        let valid = vec![Some(false), Some(true)];
        validate_original_dimacs_assignment(2, &clauses, &valid)
            .expect("assignment should satisfy original clauses");

        let incomplete = vec![Some(false), None];
        assert_eq!(
            validate_original_dimacs_assignment(2, &clauses, &incomplete),
            Err(CircuitModelValidationError::Incomplete { var: 1 })
        );

        let short = vec![Some(false)];
        assert_eq!(
            validate_original_dimacs_assignment(2, &clauses, &short),
            Err(CircuitModelValidationError::WrongLength {
                expected: 2,
                actual: 1
            })
        );

        let invalid = vec![Some(true), Some(false)];
        assert_eq!(
            validate_original_dimacs_assignment(2, &clauses, &invalid),
            Err(CircuitModelValidationError::UnsatisfiedClause { clause_index: 1 })
        );
    }

    #[test]
    fn circuit_scout_original_dimacs_residual_report_lists_all_falsified_clauses() {
        let clauses = vec![vec![lit(0, true)], vec![lit(0, false)], vec![lit(1, true)]];
        let assignment = vec![Some(false), Some(false)];

        let residual = diagnose_original_dimacs_assignment(2, &clauses, &assignment);

        assert!(residual.assignment_complete);
        assert!(!residual.validation_passed);
        assert_eq!(residual.original_clauses_checked, 3);
        assert_eq!(residual.residual_falsified_count, 2);
        assert_eq!(residual.first_residual_clause, Some(0));
        assert_eq!(residual.residual_clause_ids, vec![0, 2]);
    }

    #[test]
    fn circuit_scout_source_frame_audit_reports_residual_ids_without_model_return() {
        let clauses = vec![vec![lit(0, true)], vec![lit(1, true)]];
        let source_rows = [
            source_row(
                40,
                0,
                lit(0, true),
                0,
                false,
                CircuitSourceFrameFamily::W210Frontier,
                CircuitSourceFrameKind::FrontierValue,
            ),
            source_row(
                41,
                1,
                lit(1, true),
                1,
                true,
                CircuitSourceFrameFamily::W210SccChoice,
                CircuitSourceFrameKind::SccChoiceValue,
            ),
        ];

        let audit = audit_source_frame_rows(2, &clauses, &source_rows);

        assert_eq!(audit.rows_seen, 2);
        assert_eq!(audit.rows_accepted, 2);
        assert!(audit.assignment_complete);
        assert!(!audit.validation_passed);
        assert_eq!(audit.original_clauses_checked, 2);
        assert_eq!(audit.residual_falsified_count, 1);
        assert_eq!(audit.residual_clause_ids, vec![0]);
        assert_eq!(
            materialize_original_dimacs_assignment_from_source_frame_rows(
                2,
                &clauses,
                &source_rows,
            ),
            Err(
                CircuitModelMaterializationError::SourceFrameResidualNonZero {
                    residual_falsified_count: 1,
                    first_clause: 0
                }
            )
        );
    }

    #[test]
    fn circuit_scout_w210_value_ledger_parser_converts_one_based_vars() {
        let tsv = concat!(
            "ledger_row_id\tscc_id\toriginal_var\tvalue\tvalue_int\tsource_kind\tproduction_hook\t",
            "scc_size\tbasis_vars\tdefining_clause_ids_0_based\texternal_dependency_vars\t",
            "present_in_w159_remaining_clause\tremaining_clause_ids\troute_eligible\troute_blocker\n",
            "w210_scc_choice_value_0001\t1\t1\ttrue\t1\tcyclic_scc_tie_cegar_best_assignment\t",
            "circuit_global_assignment_search.scc_choice_value_ledger\t2\t1\t2237 11618\t\tfalse\t\tfalse\t",
            "original_dimacs_validation_failed\n",
            "w210_scc_choice_value_0002\t2\t1013\tfalse\t0\tcyclic_scc_tie_cegar_best_assignment\t",
            "circuit_global_assignment_search.scc_choice_value_ledger\t2\t1013\t310 2335\t6 63\ttrue\t1015\tfalse\t",
            "original_dimacs_validation_failed\n"
        );

        let ledger = parse_w210_source_frame_value_ledger(
            1_013,
            CircuitSourceFrameValueLedgerKind::W210SccChoice,
            tsv,
        )
        .unwrap();

        assert_eq!(ledger.rows.len(), 2);
        assert_eq!(ledger.rows[0].source_row_id, 1);
        assert_eq!(ledger.rows[0].value.var, 0);
        assert!(ledger.rows[0].value.value);
        assert_eq!(
            ledger.rows[0].value.family,
            CircuitSourceFrameFamily::W210SccChoice
        );
        assert_eq!(ledger.rows[1].source_row_id, 2);
        assert_eq!(ledger.rows[1].value.var, 1_012);
        assert!(!ledger.rows[1].value.value);
        assert!(ledger.rows[1].present_in_w159_remaining_clause);
        assert_eq!(ledger.rows[1].remaining_clause_ids_1_based, vec![1015]);
        assert_eq!(ledger.stats.rows_seen, 2);
        assert_eq!(ledger.stats.max_original_var_1_based, 1_013);
        assert_eq!(ledger.stats.route_eligible_rows, 0);
        assert_eq!(ledger.stats.route_blocked_rows, 2);
    }

    #[test]
    fn circuit_scout_w210_value_ledger_parser_rejects_bad_rows() {
        let header = concat!(
            "ledger_row_id\toriginal_var\tvalue\tvalue_int\tsource_kind\tproduction_hook\t",
            "present_in_w159_remaining_clause\tremaining_clause_ids\troute_eligible\troute_blocker\n"
        );
        let base_prefix = concat!(
            "w210_frontier_value_0001\t1\ttrue\t1\tfrontier_choice_cegar_best_assignment\t",
            "circuit_global_assignment_search.frontier_value_ledger\tfalse\t\tfalse\t",
            "original_dimacs_validation_failed\n"
        );

        assert_eq!(
            parse_w210_source_frame_value_ledger(
                1_013,
                CircuitSourceFrameValueLedgerKind::W210Frontier,
                &format!(
                    "{header}w210_frontier_value_0001\t0\ttrue\t1\tfrontier_choice_cegar_best_assignment\tcircuit_global_assignment_search.frontier_value_ledger\tfalse\t\tfalse\toriginal_dimacs_validation_failed\n"
                ),
            ),
            Err(
                CircuitSourceFrameValueLedgerParseError::OriginalVarOutOfRange {
                    line: 2,
                    original_var: 0,
                    num_vars: 1_013
                }
            )
        );
        assert_eq!(
            parse_w210_source_frame_value_ledger(
                1_013,
                CircuitSourceFrameValueLedgerKind::W210Frontier,
                &format!(
                    "{header}w210_frontier_value_0001\t1014\ttrue\t1\tfrontier_choice_cegar_best_assignment\tcircuit_global_assignment_search.frontier_value_ledger\tfalse\t\tfalse\toriginal_dimacs_validation_failed\n"
                ),
            ),
            Err(
                CircuitSourceFrameValueLedgerParseError::OriginalVarOutOfRange {
                    line: 2,
                    original_var: 1_014,
                    num_vars: 1_013
                }
            )
        );
        assert_eq!(
            parse_w210_source_frame_value_ledger(
                1_013,
                CircuitSourceFrameValueLedgerKind::W210Frontier,
                &format!(
                    "{header}w210_frontier_value_0001\t1\ttrue\t0\tfrontier_choice_cegar_best_assignment\tcircuit_global_assignment_search.frontier_value_ledger\tfalse\t\tfalse\toriginal_dimacs_validation_failed\n"
                ),
            ),
            Err(CircuitSourceFrameValueLedgerParseError::ValueIntMismatch {
                line: 2,
                value: true,
                value_int: 0
            })
        );
        assert_eq!(
            parse_w210_source_frame_value_ledger(
                1_013,
                CircuitSourceFrameValueLedgerKind::W210Frontier,
                &format!(
                    "{header}w210_frontier_value_0001\t1\ttrue\t1\tfrontier_choice_cegar_best_assignment\tcircuit_global_assignment_search.frontier_value_ledger\tfalse\t\ttrue\toriginal_dimacs_validation_failed\n"
                ),
            ),
            Err(
                CircuitSourceFrameValueLedgerParseError::RouteEligibleUnsupported { line: 2 }
            )
        );
        assert_eq!(
            parse_w210_source_frame_value_ledger(
                1_013,
                CircuitSourceFrameValueLedgerKind::W210Frontier,
                &format!(
                    "{header}w210_frontier_value_0001\t1\ttrue\t1\tfrontier_choice_cegar_best_assignment\tcircuit_global_assignment_search.frontier_value_ledger\tfalse\t\tfalse\t\n"
                ),
            ),
            Err(CircuitSourceFrameValueLedgerParseError::RouteBlockerMismatch {
                line: 2,
                actual: String::new()
            })
        );
        assert!(parse_w210_source_frame_value_ledger(
            1_013,
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &format!("{header}{base_prefix}"),
        )
        .unwrap()
        .rows
        .iter()
        .all(|row| !row.route_eligible));
    }

    #[test]
    fn circuit_scout_w210_source_frame_row_derivation_binds_clause_literals() {
        let clauses = vec![vec![lit(0, true), lit(1, false)], vec![lit(2, false)]];
        let mut frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, true)],
        );
        frontier.rows[0].remaining_clause_ids_1_based = vec![1];
        let mut scc = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210SccChoice,
            &[(22, 1, false)],
        );
        scc.rows[0].remaining_clause_ids_1_based = vec![1];
        let mut forced = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210ForcedGate,
            &[(33, 2, false)],
        );
        forced.rows[0].remaining_clause_ids_1_based = vec![2];

        let derived = derive_w210_source_frame_rows(&clauses, &frontier, &scc, &forced).unwrap();

        assert_eq!(derived.audit.rows_seen, 3);
        assert_eq!(derived.audit.rows_materialized, 3);
        assert_eq!(derived.audit.rows_rejected, 0);
        assert_eq!(derived.rows.len(), 3);
        assert_eq!(derived.rows[0].source_row_id, 11);
        assert_eq!(derived.rows[0].literal.to_dimacs(), 1);
        assert_eq!(derived.rows[0].clause_id, 0);
        assert_eq!(derived.rows[0].kind, CircuitSourceFrameKind::FrontierValue);
        assert_eq!(derived.rows[1].literal.to_dimacs(), -2);
        assert_eq!(derived.rows[1].kind, CircuitSourceFrameKind::SccChoiceValue);
        assert_eq!(derived.rows[2].literal.to_dimacs(), -3);
        assert_eq!(
            derived.rows[2].kind,
            CircuitSourceFrameKind::ForcedGateReplayBridge
        );

        let source_audit = audit_source_frame_rows(3, &clauses, &derived.rows);
        assert_eq!(source_audit.rows_seen, 3);
        assert_eq!(source_audit.rows_accepted, 3);
        assert!(source_audit.assignment_complete);
        assert!(source_audit.validation_passed);
    }

    #[test]
    fn circuit_scout_w210_source_frame_row_derivation_reconstructs_missing_and_rejects_stale_witnesses(
    ) {
        let clauses = vec![vec![lit(0, true)]];
        let frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, true)],
        );
        let mut scc = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210SccChoice,
            &[(22, 1, true)],
        );
        scc.rows[0].remaining_clause_ids_1_based = vec![2];
        let mut forced = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210ForcedGate,
            &[(33, 2, true)],
        );
        forced.rows[0].remaining_clause_ids_1_based = vec![1];

        let derived = derive_w210_source_frame_rows(&clauses, &frontier, &scc, &forced).unwrap();

        assert_eq!(derived.audit.rows_seen, 3);
        assert_eq!(derived.audit.rows_materialized, 1);
        assert_eq!(derived.audit.rows_rejected, 2);
        assert_eq!(derived.audit.missing_clause_witness_rows, 0);
        assert_eq!(derived.audit.reconstructed_clause_witness_rows, 1);
        assert_eq!(derived.audit.stale_clause_witness_rebound_rows, 0);
        assert_eq!(derived.audit.clause_out_of_range_rows, 1);
        assert_eq!(derived.audit.literal_missing_from_clause_rows, 1);
        assert_eq!(derived.rows.len(), 1);
        assert_eq!(derived.rows[0].source_row_id, 11);
        assert_eq!(derived.rows[0].clause_id, 0);
        assert_eq!(derived.rows[0].literal.to_dimacs(), 1);
        assert_eq!(
            derived.audit.first_rejection,
            Some(CircuitW210SourceFrameRowRejection::ClauseOutOfRange {
                source_row_id: 22,
                clause_id_1_based: 2
            })
        );
    }

    #[test]
    fn circuit_scout_w210_source_frame_row_derivation_accepts_only_unreferenced_missing_witnesses()
    {
        let clauses = vec![vec![lit(0, true)]];
        let frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, true), (12, 1, false)],
        );
        let empty_scc = parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[]);
        let empty_forced =
            parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[]);

        let derived =
            derive_w210_source_frame_rows(&clauses, &frontier, &empty_scc, &empty_forced).unwrap();

        assert_eq!(derived.audit.rows_seen, 2);
        assert_eq!(derived.audit.rows_materialized, 2);
        assert_eq!(derived.audit.rows_rejected, 0);
        assert_eq!(derived.audit.reconstructed_clause_witness_rows, 1);
        assert_eq!(derived.audit.stale_clause_witness_rebound_rows, 0);
        assert_eq!(derived.audit.unreferenced_original_var_rows, 1);
        assert_eq!(derived.rows[1].source_row_id, 12);
        assert_eq!(derived.rows[1].clause_id, usize::MAX);
        assert_eq!(
            derived.rows[1].kind,
            CircuitSourceFrameKind::UnreferencedOriginalValue
        );

        let source_audit = audit_source_frame_rows(2, &clauses, &derived.rows);
        assert_eq!(source_audit.rows_seen, 2);
        assert_eq!(source_audit.rows_accepted, 2);
        assert_eq!(source_audit.unreferenced_original_var_rows, 1);
        assert_eq!(source_audit.unreferenced_var_occurs, 0);
        assert!(source_audit.assignment_complete);
        assert!(source_audit.validation_passed);

        let missing_retained =
            audit_original_dimacs_sat_model_authority(2, &clauses, &derived.rows, None, None);
        assert_eq!(
            missing_retained.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::RetainedArtifactsMissing
            )
        );
        assert!(missing_retained.authority_is_absent());

        let bad_unreferenced = [source_row(
            13,
            0,
            lit(0, true),
            usize::MAX,
            true,
            CircuitSourceFrameFamily::W210Frontier,
            CircuitSourceFrameKind::UnreferencedOriginalValue,
        )];
        let bad_audit = audit_source_frame_rows(1, &clauses, &bad_unreferenced);
        assert_eq!(bad_audit.rows_seen, 1);
        assert_eq!(bad_audit.rows_rejected, 1);
        assert_eq!(bad_audit.unreferenced_var_occurs, 1);
        assert_eq!(
            materialize_original_dimacs_assignment_from_source_frame_rows(
                1,
                &clauses,
                &bad_unreferenced,
            ),
            Err(
                CircuitModelMaterializationError::SourceFrameUnreferencedVarOccurs {
                    source_row_id: 13,
                    var: 0
                }
            )
        );
    }

    #[test]
    fn circuit_scout_w210_reconstructed_source_witnesses_still_require_retained_model_check() {
        let clauses = vec![vec![lit(0, true)], vec![lit(1, false)]];
        let frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, true)],
        );
        let mut scc = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210SccChoice,
            &[(22, 1, false)],
        );
        scc.rows[0].remaining_clause_ids_1_based = vec![2];
        let empty_forced =
            parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[]);

        let derived =
            derive_w210_source_frame_rows(&clauses, &frontier, &scc, &empty_forced).unwrap();
        assert_eq!(derived.audit.rows_seen, 2);
        assert_eq!(derived.audit.rows_materialized, 2);
        assert_eq!(derived.audit.rows_rejected, 0);
        assert_eq!(derived.audit.reconstructed_clause_witness_rows, 1);
        assert_eq!(derived.audit.stale_clause_witness_rebound_rows, 0);

        let route_audit =
            audit_w210_route_admission_blocker(2, &clauses, &frontier, &scc, &empty_forced)
                .unwrap();
        assert!(route_audit.original_dimacs_validation_passed);
        assert_eq!(
            route_audit.route_admission_status,
            CircuitW210RouteAdmissionStatus::Blocked(
                CircuitW210RouteAdmissionBlocker::AuthorityAbsent
            )
        );
        assert!(route_audit.authority_is_absent());

        let missing = audit_w210_source_witness_authority(
            2,
            &clauses,
            &frontier,
            &scc,
            &empty_forced,
            CircuitW210OriginalDimacsAuthorityKind::SatModel,
            None,
        )
        .unwrap();
        assert_eq!(
            missing.authority_status,
            CircuitW210SourceWitnessAuthorityStatus::Blocked(
                CircuitW210SourceWitnessAuthorityBlocker::OriginalDimacsAuthorityMissing
            )
        );
        assert!(missing.authority_is_absent());

        let rejected = audit_w210_source_witness_authority(
            2,
            &clauses,
            &frontier,
            &scc,
            &empty_forced,
            CircuitW210OriginalDimacsAuthorityKind::SatModel,
            Some(CircuitW210OriginalDimacsAuthorityVerdict::rejected(
                CircuitW210OriginalDimacsAuthorityKind::SatModel,
            )),
        )
        .unwrap();
        assert_eq!(
            rejected.authority_status,
            CircuitW210SourceWitnessAuthorityStatus::Blocked(
                CircuitW210SourceWitnessAuthorityBlocker::OriginalDimacsAuthorityRejected
            )
        );
        assert!(rejected.authority_is_absent());

        let missing_retained =
            audit_original_dimacs_sat_model_authority(2, &clauses, &derived.rows, None, None);
        assert_eq!(
            missing_retained.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::RetainedArtifactsMissing
            )
        );
        assert!(missing_retained.authority_is_absent());

        let invalid_packet = produce_original_dimacs_sat_model_authority_packet(
            2,
            &clauses,
            &derived.rows,
            "retained/reconstructed.cnf",
            "retained/reconstructed-model.stdout",
            vec![
                "ay".to_owned(),
                "check".to_owned(),
                "model".to_owned(),
                "--json".to_owned(),
                "retained/reconstructed.cnf".to_owned(),
                "retained/reconstructed-model.stdout".to_owned(),
            ],
            0,
            retained_model_check_json(
                "retained/reconstructed.cnf",
                "retained/reconstructed-model.stdout",
                2,
                2,
                false,
            ),
        )
        .expect("source rows should materialize before checker rejection");
        let invalid = audit_original_dimacs_sat_model_authority(
            2,
            &clauses,
            &derived.rows,
            Some(&invalid_packet.artifacts),
            Some(&invalid_packet.checker_evidence),
        );
        assert_eq!(
            invalid.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::CheckerModelStatusNotValid
            )
        );
        assert!(invalid.authority_is_absent());
    }

    #[test]
    fn circuit_scout_w210_strict_source_derivation_rebinds_stale_witness_to_value_literal() {
        let clauses = vec![vec![lit(0, true)], vec![lit(0, false)]];
        let mut frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, true)],
        );
        frontier.rows[0].remaining_clause_ids_1_based = vec![2];
        frontier.rows[0].present_in_w159_remaining_clause = true;
        let empty_scc = parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[]);
        let empty_forced =
            parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[]);

        let strict =
            derive_w210_source_frame_rows(&clauses, &frontier, &empty_scc, &empty_forced).unwrap();
        assert_eq!(strict.audit.rows_seen, 1);
        assert_eq!(strict.audit.rows_materialized, 1);
        assert_eq!(strict.audit.residual_opposite_literal_rows, 0);
        assert_eq!(strict.audit.rows_rejected, 0);
        assert_eq!(strict.audit.reconstructed_clause_witness_rows, 1);
        assert_eq!(strict.audit.stale_clause_witness_rebound_rows, 1);
        assert_eq!(strict.rows.len(), 1);
        assert_eq!(strict.rows[0].literal.to_dimacs(), 1);
        assert_eq!(strict.rows[0].clause_id, 0);
        assert!(strict.rows[0].source_value);

        let residual = derive_w210_residual_source_witness_rows(
            &clauses,
            &frontier,
            &empty_scc,
            &empty_forced,
        )
        .unwrap();
        assert_eq!(residual.audit.rows_seen, 1);
        assert_eq!(residual.audit.rows_materialized, 1);
        assert_eq!(residual.audit.residual_opposite_literal_rows, 1);
        assert_eq!(residual.audit.rows_rejected, 0);
        assert_eq!(residual.rows.len(), 1);
        assert_eq!(residual.rows[0].source_row_id, 11);
        assert_eq!(residual.rows[0].literal.to_dimacs(), -1);
        assert_eq!(residual.rows[0].clause_id, 1);
        assert!(!residual.rows[0].source_value);

        let source_audit = audit_source_frame_rows(1, &clauses, &residual.rows);
        assert_eq!(source_audit.rows_seen, 1);
        assert_eq!(source_audit.rows_accepted, 1);
        assert_eq!(source_audit.rows_rejected, 0);
        assert!(source_audit.assignment_complete);
        assert!(!source_audit.validation_passed);
    }

    #[test]
    fn circuit_scout_w210_strict_source_derivation_rejects_residual_opposite_without_value_literal()
    {
        let clauses = vec![vec![lit(0, false)]];
        let mut frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, true)],
        );
        frontier.rows[0].remaining_clause_ids_1_based = vec![1];
        frontier.rows[0].present_in_w159_remaining_clause = true;
        let empty_scc = parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[]);
        let empty_forced =
            parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[]);

        let strict =
            derive_w210_source_frame_rows(&clauses, &frontier, &empty_scc, &empty_forced).unwrap();
        assert_eq!(strict.audit.rows_seen, 1);
        assert_eq!(strict.audit.rows_materialized, 0);
        assert_eq!(strict.audit.residual_opposite_literal_rows, 0);
        assert_eq!(strict.audit.rows_rejected, 1);
        assert_eq!(strict.audit.literal_missing_from_clause_rows, 1);
        assert_eq!(strict.audit.stale_clause_witness_rebound_rows, 0);
        assert!(strict.rows.is_empty());

        let residual = derive_w210_residual_source_witness_rows(
            &clauses,
            &frontier,
            &empty_scc,
            &empty_forced,
        )
        .unwrap();
        assert_eq!(residual.audit.rows_seen, 1);
        assert_eq!(residual.audit.rows_materialized, 1);
        assert_eq!(residual.audit.residual_opposite_literal_rows, 1);
        assert_eq!(residual.audit.rows_rejected, 0);
        assert_eq!(residual.rows.len(), 1);
        assert_eq!(residual.rows[0].literal.to_dimacs(), -1);
        assert!(!residual.rows[0].source_value);

        let source_audit = audit_source_frame_rows(1, &clauses, &residual.rows);
        assert_eq!(source_audit.rows_seen, 1);
        assert_eq!(source_audit.rows_accepted, 1);
        assert!(source_audit.validation_passed);

        let authority_audit =
            audit_original_dimacs_sat_model_authority(1, &clauses, &residual.rows, None, None);
        assert_eq!(
            authority_audit.authority_status,
            CircuitOriginalDimacsSatModelAuthorityStatus::Blocked(
                CircuitOriginalDimacsSatModelAuthorityBlocker::RetainedArtifactsMissing
            )
        );
        assert!(authority_audit.authority_is_absent());
    }

    #[test]
    fn circuit_scout_w210_residual_source_witness_derivation_rejects_non_residual_opposites() {
        let clauses = vec![vec![lit(0, false)]];
        let mut frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, true)],
        );
        frontier.rows[0].remaining_clause_ids_1_based = vec![1];
        let empty_scc = parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[]);
        let empty_forced =
            parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[]);

        let strict =
            derive_w210_source_frame_rows(&clauses, &frontier, &empty_scc, &empty_forced).unwrap();
        assert_eq!(strict.audit.rows_seen, 1);
        assert_eq!(strict.audit.rows_materialized, 0);
        assert_eq!(strict.audit.residual_opposite_literal_rows, 0);
        assert_eq!(strict.audit.rows_rejected, 1);
        assert_eq!(strict.audit.literal_missing_from_clause_rows, 1);

        let residual = derive_w210_residual_source_witness_rows(
            &clauses,
            &frontier,
            &empty_scc,
            &empty_forced,
        )
        .unwrap();
        assert_eq!(residual.audit.rows_seen, 1);
        assert_eq!(residual.audit.rows_materialized, 0);
        assert_eq!(residual.audit.residual_opposite_literal_rows, 0);
        assert_eq!(residual.audit.rows_rejected, 1);
        assert_eq!(residual.audit.literal_missing_from_clause_rows, 1);
        assert!(residual.rows.is_empty());
    }

    #[test]
    fn circuit_scout_w210_residual_source_witness_replay_validates_only_without_authority() {
        let clauses = vec![vec![lit(0, true)]];
        let mut frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, false)],
        );
        frontier.rows[0].remaining_clause_ids_1_based = vec![1];
        frontier.rows[0].present_in_w159_remaining_clause = true;
        let empty_scc = parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[]);
        let empty_forced =
            parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[]);

        let audit = audit_w210_residual_source_witness_replay(
            1,
            &clauses,
            &frontier,
            &empty_scc,
            &empty_forced,
        )
        .unwrap();

        assert_eq!(audit.value_ledger_audit.residual_falsified_count, 1);
        assert_eq!(audit.residual_source_witness_row_audit.rows_seen, 1);
        assert_eq!(audit.residual_source_witness_row_audit.rows_materialized, 1);
        assert_eq!(
            audit
                .residual_source_witness_row_audit
                .residual_opposite_literal_rows,
            1
        );
        assert_eq!(audit.frontier_rows, 1);
        assert_eq!(audit.scc_choice_rows, 0);
        assert_eq!(audit.forced_gate_rows, 0);
        assert_eq!(audit.overlay_rows_applied, 1);
        assert_eq!(audit.overlay_rows_already_matched, 0);
        assert_eq!(audit.overlay_duplicate_rows, 0);
        assert_eq!(audit.overlay_conflicting_rows, 0);
        assert_eq!(audit.overlay_rows_out_of_range, 0);
        assert_eq!(audit.original_clauses_checked, 1);
        assert_eq!(audit.residual_falsified_count, 0);
        assert_eq!(audit.repaired_original_residual_count, 1);
        assert_eq!(audit.remaining_original_residual_count, 0);
        assert_eq!(audit.new_residual_count, 0);
        assert!(audit.validation_passed);
        assert!(audit.authority_is_absent());
        assert!(!audit.route_admitted);
        assert!(!audit.sat_output_authority);
        assert!(!audit.model_output_authority);
        assert!(!audit.proof_output_authority);
        assert!(!audit.solver_verdict_authority);
    }

    #[test]
    fn circuit_scout_w210_residual_source_witness_replay_blocks_conflicting_overlay_rows() {
        let clauses = vec![
            vec![lit(0, true)],
            vec![lit(0, false), lit(1, true)],
            vec![lit(1, true)],
        ];
        let mut frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, false), (12, 0, false)],
        );
        frontier.rows[0].remaining_clause_ids_1_based = vec![1];
        frontier.rows[0].present_in_w159_remaining_clause = true;
        frontier.rows[1].remaining_clause_ids_1_based = vec![1];
        frontier.rows[1].present_in_w159_remaining_clause = true;
        let mut scc = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210SccChoice,
            &[(22, 0, true)],
        );
        scc.rows[0].remaining_clause_ids_1_based = vec![2];
        scc.rows[0].present_in_w159_remaining_clause = true;
        let forced = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210ForcedGate,
            &[(33, 1, true)],
        );

        let audit =
            audit_w210_residual_source_witness_replay(2, &clauses, &frontier, &scc, &forced)
                .unwrap();

        assert_eq!(audit.value_ledger_audit.duplicate_same_value_rows, 1);
        assert_eq!(audit.value_ledger_audit.conflicting_rows, 1);
        assert_eq!(audit.value_ledger_audit.residual_falsified_count, 1);
        assert_eq!(audit.residual_source_witness_row_audit.rows_seen, 4);
        assert_eq!(audit.residual_source_witness_row_audit.rows_materialized, 3);
        assert_eq!(audit.residual_source_witness_row_audit.rows_rejected, 1);
        assert_eq!(
            audit
                .residual_source_witness_row_audit
                .missing_clause_witness_rows,
            1
        );
        assert_eq!(audit.frontier_rows, 2);
        assert_eq!(audit.scc_choice_rows, 1);
        assert_eq!(audit.forced_gate_rows, 0);
        assert_eq!(audit.overlay_rows_applied, 1);
        assert_eq!(audit.overlay_rows_already_matched, 0);
        assert_eq!(audit.overlay_duplicate_rows, 1);
        assert_eq!(audit.overlay_conflicting_rows, 1);
        assert_eq!(audit.overlay_rows_out_of_range, 0);
        assert_eq!(audit.residual_falsified_count, 0);
        assert_eq!(audit.repaired_original_residual_count, 1);
        assert_eq!(audit.new_residual_count, 0);
        assert!(
            !audit.validation_passed,
            "overlay conflicts must block validation even when the chosen overlay satisfies the CNF"
        );
        assert!(audit.authority_is_absent());
        assert!(!audit.route_admitted);
        assert!(!audit.sat_output_authority);
        assert!(!audit.model_output_authority);
        assert!(!audit.proof_output_authority);
        assert!(!audit.solver_verdict_authority);
    }

    #[test]
    fn circuit_scout_w210_opposite_literal_source_row_cannot_bypass_value_residual_authority() {
        let clauses = vec![vec![lit(0, false)]];
        let mut frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, true)],
        );
        frontier.rows[0].remaining_clause_ids_1_based = vec![1];
        frontier.rows[0].present_in_w159_remaining_clause = true;
        let empty_scc = parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[]);
        let empty_forced =
            parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[]);

        let audit = audit_w210_source_witness_authority(
            1,
            &clauses,
            &frontier,
            &empty_scc,
            &empty_forced,
            CircuitW210OriginalDimacsAuthorityKind::SatModel,
            Some(CircuitW210OriginalDimacsAuthorityVerdict::test_accepted(
                CircuitW210OriginalDimacsAuthorityKind::SatModel,
            )),
        )
        .unwrap();

        assert_eq!(
            audit.authority_status,
            CircuitW210SourceWitnessAuthorityStatus::Blocked(
                CircuitW210SourceWitnessAuthorityBlocker::RouteAdmission(
                    CircuitW210RouteAdmissionBlocker::ValueLedgerResidualNonZero
                )
            )
        );
        assert_eq!(
            audit.route_admission_audit.source_frame_row_audit.rows_seen,
            1
        );
        assert_eq!(
            audit
                .route_admission_audit
                .source_frame_row_audit
                .rows_materialized,
            0
        );
        assert_eq!(
            audit
                .route_admission_audit
                .source_frame_row_audit
                .residual_opposite_literal_rows,
            0
        );
        assert_eq!(
            audit
                .route_admission_audit
                .source_frame_row_audit
                .rows_rejected,
            1
        );
        assert!(!audit.route_admission_audit.source_frame_audit_ran);
        assert!(
            !audit
                .route_admission_audit
                .value_ledger_audit
                .validation_passed
        );
        assert!(
            !audit
                .route_admission_audit
                .original_dimacs_validation_passed
        );
        assert!(audit.authority_is_absent());
    }

    #[test]
    fn circuit_scout_w210_route_admission_blocker_requires_authority_after_validation() {
        let clauses = vec![vec![lit(0, true)], vec![lit(1, false)], vec![lit(2, false)]];
        let mut frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, true)],
        );
        frontier.rows[0].remaining_clause_ids_1_based = vec![1];
        let mut scc = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210SccChoice,
            &[(22, 1, false)],
        );
        scc.rows[0].remaining_clause_ids_1_based = vec![2];
        let mut forced = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210ForcedGate,
            &[(33, 2, false)],
        );
        forced.rows[0].remaining_clause_ids_1_based = vec![3];

        let audit =
            audit_w210_route_admission_blocker(3, &clauses, &frontier, &scc, &forced).unwrap();

        assert_eq!(audit.value_ledger_audit.rows_seen, 3);
        assert!(audit.value_ledger_audit.validation_passed);
        assert_eq!(audit.source_frame_row_audit.rows_seen, 3);
        assert_eq!(audit.source_frame_row_audit.rows_materialized, 3);
        assert_eq!(audit.source_frame_row_audit.rows_rejected, 0);
        assert!(audit.source_frame_audit_ran);
        assert!(audit.source_frame_audit.validation_passed);
        assert!(audit.original_dimacs_validation_passed);
        assert_eq!(
            audit.route_admission_status,
            CircuitW210RouteAdmissionStatus::Blocked(
                CircuitW210RouteAdmissionBlocker::AuthorityAbsent
            )
        );
        assert!(!audit.route_admission_status.is_admitted());
        assert!(audit.authority_is_absent());
        assert!(!audit.route_admitted);
        assert!(!audit.sat_output_authority);
        assert!(!audit.model_output_authority);
        assert!(!audit.proof_output_authority);
        assert!(!audit.solver_verdict_authority);
    }

    #[test]
    fn circuit_scout_w210_source_witness_authority_requires_checker_verdict() {
        let clauses = vec![vec![lit(0, true)]];
        let mut frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, true)],
        );
        frontier.rows[0].remaining_clause_ids_1_based = vec![1];
        let empty_scc = parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[]);
        let empty_forced =
            parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[]);

        let missing = audit_w210_source_witness_authority(
            1,
            &clauses,
            &frontier,
            &empty_scc,
            &empty_forced,
            CircuitW210OriginalDimacsAuthorityKind::SatModel,
            None,
        )
        .unwrap();

        assert!(
            missing
                .route_admission_audit
                .original_dimacs_validation_passed
        );
        assert_eq!(
            missing.route_admission_audit.route_admission_status,
            CircuitW210RouteAdmissionStatus::Blocked(
                CircuitW210RouteAdmissionBlocker::AuthorityAbsent
            )
        );
        assert_eq!(
            missing.authority_status,
            CircuitW210SourceWitnessAuthorityStatus::Blocked(
                CircuitW210SourceWitnessAuthorityBlocker::OriginalDimacsAuthorityMissing
            )
        );
        assert!(!missing.authority_status.is_admitted());
        assert!(missing.authority_is_absent());

        let unchecked = audit_w210_source_witness_authority(
            1,
            &clauses,
            &frontier,
            &empty_scc,
            &empty_forced,
            CircuitW210OriginalDimacsAuthorityKind::SatModel,
            Some(CircuitW210OriginalDimacsAuthorityVerdict::unchecked(
                CircuitW210OriginalDimacsAuthorityKind::SatModel,
            )),
        )
        .unwrap();
        assert_eq!(
            unchecked.authority_status,
            CircuitW210SourceWitnessAuthorityStatus::Blocked(
                CircuitW210SourceWitnessAuthorityBlocker::OriginalDimacsAuthorityUnchecked
            )
        );
        assert!(unchecked.authority_is_absent());

        let rejected = audit_w210_source_witness_authority(
            1,
            &clauses,
            &frontier,
            &empty_scc,
            &empty_forced,
            CircuitW210OriginalDimacsAuthorityKind::SatModel,
            Some(CircuitW210OriginalDimacsAuthorityVerdict::rejected(
                CircuitW210OriginalDimacsAuthorityKind::SatModel,
            )),
        )
        .unwrap();
        assert_eq!(
            rejected.authority_status,
            CircuitW210SourceWitnessAuthorityStatus::Blocked(
                CircuitW210SourceWitnessAuthorityBlocker::OriginalDimacsAuthorityRejected
            )
        );
        assert!(rejected.authority_is_absent());

        let mismatch = audit_w210_source_witness_authority(
            1,
            &clauses,
            &frontier,
            &empty_scc,
            &empty_forced,
            CircuitW210OriginalDimacsAuthorityKind::SatModel,
            Some(CircuitW210OriginalDimacsAuthorityVerdict::test_accepted(
                CircuitW210OriginalDimacsAuthorityKind::UnsatProof,
            )),
        )
        .unwrap();
        assert_eq!(
            mismatch.authority_status,
            CircuitW210SourceWitnessAuthorityStatus::Blocked(
                CircuitW210SourceWitnessAuthorityBlocker::OriginalDimacsAuthorityKindMismatch
            )
        );
        assert!(mismatch.authority_is_absent());

        let accepted = audit_w210_source_witness_authority(
            1,
            &clauses,
            &frontier,
            &empty_scc,
            &empty_forced,
            CircuitW210OriginalDimacsAuthorityKind::SatModel,
            Some(CircuitW210OriginalDimacsAuthorityVerdict::test_accepted(
                CircuitW210OriginalDimacsAuthorityKind::SatModel,
            )),
        )
        .unwrap();
        assert_eq!(
            accepted.authority_status,
            CircuitW210SourceWitnessAuthorityStatus::Admitted(
                CircuitW210OriginalDimacsAuthorityKind::SatModel
            )
        );
        assert!(accepted.authority_status.is_admitted());
        assert!(accepted.route_admitted);
        assert!(accepted.solver_verdict_authority);
        assert!(accepted.sat_output_authority);
        assert!(accepted.model_output_authority);
        assert!(!accepted.unsat_output_authority);
        assert!(!accepted.proof_output_authority);
    }

    #[test]
    fn circuit_scout_w210_residual_repair_candidate_validates_but_grants_no_authority() {
        let clauses = vec![vec![lit(0, true)]];
        let mut frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, false)],
        );
        frontier.rows[0].remaining_clause_ids_1_based = vec![1];
        let empty_scc = parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[]);
        let empty_forced =
            parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[]);

        let audit = audit_w210_residual_repair_candidates(
            1,
            &clauses,
            &frontier,
            &empty_scc,
            &empty_forced,
        )
        .unwrap();

        assert_eq!(audit.value_ledger_audit.residual_falsified_count, 1);
        assert!(!audit.value_ledger_audit.validation_passed);
        assert_eq!(audit.rows_seen, 1);
        assert_eq!(audit.rows_without_clause_witness, 0);
        assert_eq!(audit.rows_without_flip_literal, 0);
        assert_eq!(audit.candidate_rows, 1);
        assert_eq!(audit.improving_candidates, 1);
        assert_eq!(audit.plateau_candidates, 0);
        assert_eq!(audit.worsening_candidates, 0);
        assert_eq!(audit.best_residual_falsified_count, 0);
        assert_eq!(audit.best_repaired_original_residual_count, 1);
        assert_eq!(audit.best_remaining_original_residual_count, 0);
        assert!(audit.validation_passed);
        assert_eq!(
            audit.best_candidate,
            Some(CircuitW210ResidualRepairCandidate {
                ledger_kind: CircuitSourceFrameValueLedgerKind::W210Frontier,
                source_row_id: 11,
                var: 0,
                from_value: false,
                to_value: true,
                clause_id: 0,
                residual_falsified_count: 0,
                repaired_original_residual_count: 1,
                remaining_original_residual_count: 0,
                new_residual_count: 0,
                first_new_residual_clause: None,
                validation_passed: true,
            })
        );
        assert!(audit.authority_is_absent());
        assert!(!audit.route_admitted);
        assert!(!audit.sat_output_authority);
        assert!(!audit.model_output_authority);
        assert!(!audit.proof_output_authority);
        assert!(!audit.solver_verdict_authority);
    }

    #[test]
    fn circuit_scout_w210_residual_repair_pair_validates_but_grants_no_authority() {
        let clauses = vec![vec![lit(0, true)], vec![lit(1, true)]];
        let mut frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, false), (12, 1, false)],
        );
        frontier.rows[0].remaining_clause_ids_1_based = vec![1];
        frontier.rows[1].remaining_clause_ids_1_based = vec![2];
        let empty_scc = parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[]);
        let empty_forced =
            parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[]);

        let audit = audit_w210_residual_repair_pair_candidates(
            2,
            &clauses,
            &frontier,
            &empty_scc,
            &empty_forced,
        )
        .unwrap();

        assert_eq!(audit.value_ledger_audit.residual_falsified_count, 2);
        assert!(!audit.value_ledger_audit.validation_passed);
        assert_eq!(audit.single_candidate_rows, 2);
        assert_eq!(audit.same_var_pairs_skipped, 0);
        assert_eq!(audit.pair_candidates, 1);
        assert_eq!(audit.improving_pairs, 1);
        assert_eq!(audit.plateau_pairs, 0);
        assert_eq!(audit.worsening_pairs, 0);
        assert_eq!(audit.best_residual_falsified_count, 0);
        assert_eq!(audit.best_repaired_original_residual_count, 2);
        assert_eq!(audit.best_remaining_original_residual_count, 0);
        assert_eq!(audit.best_new_residual_count, 0);
        assert!(audit.validation_passed);
        assert_eq!(
            audit.best_pair,
            Some(CircuitW210ResidualRepairPairCandidate {
                first: CircuitW210ResidualRepairFlip {
                    ledger_kind: CircuitSourceFrameValueLedgerKind::W210Frontier,
                    source_row_id: 11,
                    var: 0,
                    from_value: false,
                    to_value: true,
                    clause_id: 0,
                },
                second: CircuitW210ResidualRepairFlip {
                    ledger_kind: CircuitSourceFrameValueLedgerKind::W210Frontier,
                    source_row_id: 12,
                    var: 1,
                    from_value: false,
                    to_value: true,
                    clause_id: 1,
                },
                residual_falsified_count: 0,
                repaired_original_residual_count: 2,
                remaining_original_residual_count: 0,
                new_residual_count: 0,
                first_new_residual_clause: None,
                validation_passed: true,
            })
        );
        assert!(audit.authority_is_absent());
        assert!(!audit.route_admitted);
        assert!(!audit.sat_output_authority);
        assert!(!audit.model_output_authority);
        assert!(!audit.proof_output_authority);
        assert!(!audit.solver_verdict_authority);
    }

    #[test]
    fn circuit_scout_w210_residual_repair_triple_validates_but_grants_no_authority() {
        let clauses = vec![vec![lit(0, true)], vec![lit(1, true)], vec![lit(2, true)]];
        let mut frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, false), (12, 1, false), (13, 2, false)],
        );
        frontier.rows[0].remaining_clause_ids_1_based = vec![1];
        frontier.rows[1].remaining_clause_ids_1_based = vec![2];
        frontier.rows[2].remaining_clause_ids_1_based = vec![3];
        let empty_scc = parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[]);
        let empty_forced =
            parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[]);

        let audit = audit_w210_residual_repair_triple_candidates(
            3,
            &clauses,
            &frontier,
            &empty_scc,
            &empty_forced,
        )
        .unwrap();

        assert_eq!(audit.value_ledger_audit.residual_falsified_count, 3);
        assert!(!audit.value_ledger_audit.validation_passed);
        assert_eq!(audit.single_candidate_rows, 3);
        assert_eq!(audit.same_var_triples_skipped, 0);
        assert_eq!(audit.triple_candidates, 1);
        assert_eq!(audit.improving_triples, 1);
        assert_eq!(audit.plateau_triples, 0);
        assert_eq!(audit.worsening_triples, 0);
        assert_eq!(audit.best_residual_falsified_count, 0);
        assert_eq!(audit.best_repaired_original_residual_count, 3);
        assert_eq!(audit.best_remaining_original_residual_count, 0);
        assert_eq!(audit.best_new_residual_count, 0);
        assert!(audit.validation_passed);
        assert_eq!(
            audit.best_triple,
            Some(CircuitW210ResidualRepairTripleCandidate {
                first: CircuitW210ResidualRepairFlip {
                    ledger_kind: CircuitSourceFrameValueLedgerKind::W210Frontier,
                    source_row_id: 11,
                    var: 0,
                    from_value: false,
                    to_value: true,
                    clause_id: 0,
                },
                second: CircuitW210ResidualRepairFlip {
                    ledger_kind: CircuitSourceFrameValueLedgerKind::W210Frontier,
                    source_row_id: 12,
                    var: 1,
                    from_value: false,
                    to_value: true,
                    clause_id: 1,
                },
                third: CircuitW210ResidualRepairFlip {
                    ledger_kind: CircuitSourceFrameValueLedgerKind::W210Frontier,
                    source_row_id: 13,
                    var: 2,
                    from_value: false,
                    to_value: true,
                    clause_id: 2,
                },
                residual_falsified_count: 0,
                repaired_original_residual_count: 3,
                remaining_original_residual_count: 0,
                new_residual_count: 0,
                first_new_residual_clause: None,
                validation_passed: true,
            })
        );
        assert!(audit.authority_is_absent());
        assert!(!audit.route_admitted);
        assert!(!audit.sat_output_authority);
        assert!(!audit.model_output_authority);
        assert!(!audit.proof_output_authority);
        assert!(!audit.solver_verdict_authority);
    }

    #[test]
    fn circuit_scout_w210_route_admission_blocker_rejects_unbound_source_values() {
        let clauses = vec![vec![lit(0, true)]];
        let frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(11, 0, true)],
        );
        let mut scc = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210SccChoice,
            &[(22, 1, true)],
        );
        scc.rows[0].remaining_clause_ids_1_based = vec![2];
        let mut forced = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210ForcedGate,
            &[(33, 2, true)],
        );
        forced.rows[0].remaining_clause_ids_1_based = vec![1];

        let audit =
            audit_w210_route_admission_blocker(3, &clauses, &frontier, &scc, &forced).unwrap();

        assert!(audit.value_ledger_audit.validation_passed);
        assert_eq!(audit.source_frame_row_audit.rows_seen, 3);
        assert_eq!(audit.source_frame_row_audit.rows_materialized, 1);
        assert_eq!(audit.source_frame_row_audit.rows_rejected, 2);
        assert_eq!(audit.source_frame_row_audit.missing_clause_witness_rows, 0);
        assert_eq!(
            audit
                .source_frame_row_audit
                .reconstructed_clause_witness_rows,
            1
        );
        assert_eq!(
            audit
                .source_frame_row_audit
                .stale_clause_witness_rebound_rows,
            0
        );
        assert_eq!(audit.source_frame_row_audit.clause_out_of_range_rows, 1);
        assert_eq!(
            audit
                .source_frame_row_audit
                .literal_missing_from_clause_rows,
            1
        );
        assert!(!audit.source_frame_audit_ran);
        assert!(!audit.original_dimacs_validation_passed);
        assert_eq!(
            audit.route_admission_status,
            CircuitW210RouteAdmissionStatus::Blocked(
                CircuitW210RouteAdmissionBlocker::SourceFrameDerivationRejected
            )
        );
        assert!(!audit.route_admission_status.is_admitted());
        assert!(audit.authority_is_absent());
    }

    #[test]
    fn circuit_scout_w210_value_ledger_combiner_counts_duplicates_and_conflicts() {
        let clauses = vec![vec![lit(0, false)]];
        let frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(1, 0, true), (2, 0, true)],
        );
        let empty_scc = parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[]);
        let empty_forced =
            parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[]);

        let duplicate_audit = audit_w210_source_frame_value_ledgers(
            1,
            &clauses,
            &frontier,
            &empty_scc,
            &empty_forced,
        )
        .unwrap();

        assert_eq!(duplicate_audit.rows_seen, 2);
        assert_eq!(duplicate_audit.rows_accepted, 1);
        assert_eq!(duplicate_audit.duplicate_same_value_rows, 1);
        assert_eq!(duplicate_audit.conflicting_rows, 0);
        assert_eq!(duplicate_audit.covered_vars, 1);
        assert!(!duplicate_audit.validation_passed);
        assert_eq!(duplicate_audit.residual_falsified_count, 1);

        let conflicting_scc = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210SccChoice,
            &[(3, 0, false)],
        );
        let conflict_audit = audit_w210_source_frame_value_ledgers(
            1,
            &[vec![lit(0, true)]],
            &parsed_value_ledger(
                CircuitSourceFrameValueLedgerKind::W210Frontier,
                &[(1, 0, true)],
            ),
            &conflicting_scc,
            &empty_forced,
        )
        .unwrap();

        assert_eq!(conflict_audit.rows_seen, 2);
        assert_eq!(conflict_audit.rows_accepted, 1);
        assert_eq!(conflict_audit.conflicting_rows, 1);
        assert_eq!(conflict_audit.covered_vars, 1);
        assert!(!conflict_audit.validation_passed);
    }

    #[test]
    fn circuit_scout_w210_value_ledger_combiner_reports_missing_and_wrong_order() {
        let frontier = parsed_value_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(1, 0, true)],
        );
        let empty_scc = parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[]);
        let empty_forced =
            parsed_value_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[]);

        let audit = audit_w210_source_frame_value_ledgers(
            2,
            &[vec![lit(0, true)], vec![lit(1, true)]],
            &frontier,
            &empty_scc,
            &empty_forced,
        )
        .unwrap();

        assert_eq!(audit.rows_seen, 1);
        assert_eq!(audit.rows_accepted, 1);
        assert_eq!(audit.covered_vars, 1);
        assert_eq!(audit.missing_vars, 1);
        assert_eq!(audit.first_missing_var, Some(1));
        assert!(!audit.assignment_complete);
        assert!(!audit.validation_passed);

        assert_eq!(
            audit_w210_source_frame_value_ledgers(
                1,
                &[vec![lit(0, true)]],
                &empty_scc,
                &empty_scc,
                &empty_forced
            ),
            Err(CircuitW210ValueLedgerAuditError::LedgerKindMismatch {
                role: "frontier",
                expected: CircuitSourceFrameValueLedgerKind::W210Frontier,
                actual: CircuitSourceFrameValueLedgerKind::W210SccChoice,
            })
        );
    }

    fn scout_required_benchmark(repo_relative: &str) -> CircuitScoutReport {
        let cnf = decompress_required_benchmark(repo_relative);
        let formula = parse_str(&cnf).expect("benchmark DIMACS should parse");
        scout_formula(formula.num_vars, &formula.clauses)
    }

    fn scout_optional_benchmark(repo_relative: &str) -> Option<CircuitScoutReport> {
        if !repo_root().join(repo_relative).is_file() {
            return None;
        }
        let cnf = crate::test_xz::decompress_repo_xz(repo_relative)?;
        let formula = parse_str(&cnf).expect("optional benchmark DIMACS should parse");
        Some(scout_formula(formula.num_vars, &formula.clauses))
    }

    fn synthetic_dense_clique_rejection_report() -> CircuitScoutReport {
        let num_vars = 10;
        let mut clauses = Vec::new();
        for i in 0..99 {
            clauses.push(vec![
                lit((i % num_vars) as u32, false),
                lit(((i + 1) % num_vars) as u32, false),
            ]);
        }
        clauses.push((0..8).map(|var| lit(var, false)).collect());
        scout_formula(num_vars, &clauses)
    }

    fn synthetic_equivalence_chain_rejection_report() -> CircuitScoutReport {
        let num_vars = 18;
        let mut clauses = Vec::new();
        for var in 0..17 {
            equiv_gate(&mut clauses, var, var + 1);
        }
        scout_formula(num_vars as usize, &clauses)
    }

    fn decompress_required_benchmark(repo_relative: &str) -> String {
        crate::test_xz::decompress_required_repo_xz(repo_relative)
    }

    fn repo_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }
}
