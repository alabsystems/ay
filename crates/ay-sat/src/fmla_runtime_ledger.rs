// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Default-off runtime ledger scaffold for Fmla guarded-equivalence rewrites.
//!
//! This module is a capture-only scaffold. It can record the source-visible
//! fields needed for one guarded-equivalence transaction, but it never mutates
//! clauses, opens proof/model gates, or enables destructive substitution.

use crate::decompose::{
    DecomposeLratDryRunSidecar, DecomposeProofEmitContext, DecomposeProofEmitRecord,
    DecomposeProofOutRecordKind, FmlaGuardedEquivOverlayLratBinaryRow,
    FmlaGuardedEquivOverlayLratSidecar, FmlaGuardedEquivSupportCoverLratSidecar,
};
use crate::fmla_guarded_equiv_scout::{
    FmlaGuardedEquivWitnesses, FmlaGuardedEquivalenceWitness, FmlaOneHotGroupWitness,
};
use crate::literal::Literal;
use crate::proof_manager::{
    LearnedLratDryRunProofArtifactImportReject, LearnedLratMainProofAuthorityReject, ProofManager,
    LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA,
};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

/// Stable schema emitted by the W88 runtime-ledger scaffold exporter.
pub const FMLA_RUNTIME_LEDGER_SCHEMA: &str = "ay.w88-fmla-runtime-ledger-scaffold/v1";

const COMMIT_FIELDS: &[&str] = &[
    "mutation_epoch",
    "pre_mutation_clause_epoch",
    "removed_original_var",
    "retained_original_var",
];
const MODEL_FRAME_FIELDS: &[&str] = &[
    "inactive_guard_fallback_assignment",
    "model_reconstruction_stack_index",
];
const MODEL_CHECK_FIELDS: &[&str] = &[
    "reconstructed_model_checker_command",
    "reconstructed_model_checker_verdict_artifact",
];
const PROOF_REWRITE_FIELDS: &[&str] = &[
    "proof_manager_mode",
    "source_proof_ids",
    "derived_clause_proof_steps",
    "deletion_proof_steps",
    "runtime_decompose_transaction_id",
    "sidecar_context_token",
    "sidecar_row_index",
    "source_row_id",
    "obligation_id",
    "checker_visible_id",
    "proof_writer_io_error",
    "external_checker_verified",
];
const EXTERNAL_PROOF_FIELDS: &[&str] = &[
    "external_proof_checker_command",
    "external_proof_checker_verdict_artifact",
];
const SATCOMP_ROLLUP_FIELDS: &[&str] = &["wrong_count_zero", "invalid_count_zero"];

/// Stable schema for an externally retained Main/LRAT proof-check verdict.
pub const FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_SCHEMA: &str =
    "ay.fmla-main-lrat-external-checker-verdict/v1";
/// Stable schema for evidence-only post-check Fmla admission replay.
pub const FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA: &str =
    "ay.fmla-main-lrat-postcheck-admission-replay/v1";
/// Stable schema for solver-exported learned-LRAT dry-run proof fragments.
pub const FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA: &str =
    LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA;
/// Default-off retained artifact path for solver-exported learned-LRAT dry-run proof fragments.
pub const FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_PATH_ENV: &str =
    "AY_SAT_FMLA_LEARNED_LRAT_DRY_RUN_ARTIFACT";
/// Default-off postcheck replay path that may authorize a checker-backed Fmla Main/LRAT proof.
pub const FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV: &str =
    "AY_SAT_FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY";
/// Current solver proof.out path used to bind a Fmla authority replay to this run.
pub const FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV: &str =
    "AY_SAT_FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT";

/// The exact checker-verdict artifact needed before Main/LRAT route admission.
pub const FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT:
    ExternalProofCheckerVerdictArtifactRequirement =
    ExternalProofCheckerVerdictArtifactRequirement {
        runtime_field: "external_proof_checker_verdict_artifact",
        schema: FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_SCHEMA,
        accepted_verdict: "VERIFIED_UNSAT",
        artifact_file_name: "fmla-main-lrat-external-checker-verdict.json",
        proof_out_file_name: "proof.out",
        checker_exit_code: 0,
    };

/// W83 runtime-required fields that must be represented before promotion.
pub const W83_RUNTIME_REQUIRED_FIELDS: &[&str] = &[
    "mutation_epoch",
    "pre_mutation_clause_epoch",
    "removed_original_var",
    "retained_original_var",
    "inactive_guard_fallback_assignment",
    "model_reconstruction_stack_index",
    "reconstructed_model_checker_command",
    "reconstructed_model_checker_verdict_artifact",
    "proof_manager_mode",
    "source_proof_ids",
    "derived_clause_proof_steps",
    "deletion_proof_steps",
    "external_proof_checker_command",
    "external_proof_checker_verdict_artifact",
    "wrong_count_zero",
    "invalid_count_zero",
];

/// Definition for one W83 runtime ledger record group.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FmlaRuntimeRecordGroupDefinition {
    /// Stable W83 record-group id.
    pub record_group_id: &'static str,
    /// Stable runtime record type name.
    pub runtime_record: &'static str,
    /// Runtime-required fields represented by this record group.
    pub covered_fields: &'static [&'static str],
}

/// W83's six runtime record groups.
pub const W83_RUNTIME_RECORD_GROUPS: &[FmlaRuntimeRecordGroupDefinition] = &[
    FmlaRuntimeRecordGroupDefinition {
        record_group_id: "fmla-guarded-equivalence-commit",
        runtime_record: "FmlaGuardedEquivalenceCommitRecord",
        covered_fields: COMMIT_FIELDS,
    },
    FmlaRuntimeRecordGroupDefinition {
        record_group_id: "fmla-model-reconstruction-frame",
        runtime_record: "FmlaModelReconstructionFrameRecord",
        covered_fields: MODEL_FRAME_FIELDS,
    },
    FmlaRuntimeRecordGroupDefinition {
        record_group_id: "sat-original-model-check",
        runtime_record: "OriginalDimacsModelCheckRecord",
        covered_fields: MODEL_CHECK_FIELDS,
    },
    FmlaRuntimeRecordGroupDefinition {
        record_group_id: "main-proof-rewrite-ledger",
        runtime_record: "MainProofRewriteLedgerRecord",
        covered_fields: PROOF_REWRITE_FIELDS,
    },
    FmlaRuntimeRecordGroupDefinition {
        record_group_id: "external-proof-check",
        runtime_record: "ExternalProofCheckRecord",
        covered_fields: EXTERNAL_PROOF_FIELDS,
    },
    FmlaRuntimeRecordGroupDefinition {
        record_group_id: "satcomp-verdict-rollup",
        runtime_record: "SatCompAcceptanceRollupRecord",
        covered_fields: SATCOMP_ROLLUP_FIELDS,
    },
];

/// Whether a represented runtime field has an observed value or remains gated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FmlaRuntimeFieldStatus {
    /// The capture-only transaction observed a concrete value for this field.
    Captured,
    /// The field is represented by the record, but the value remains blocked.
    Blocked,
}

impl FmlaRuntimeFieldStatus {
    /// Stable status string for reports.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Captured => "captured",
            Self::Blocked => "blocked",
        }
    }
}

/// One represented runtime field in a scaffold record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmlaRuntimeLedgerField {
    /// W83 field name.
    pub name: &'static str,
    /// Capture status for this field.
    pub status: FmlaRuntimeFieldStatus,
    /// Stable detail explaining the value source or blocking condition.
    pub detail: &'static str,
}

/// One emitted capture-only runtime ledger record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmlaRuntimeLedgerRecord {
    /// Capture-only transaction id shared by all six records.
    pub transaction_id: u64,
    /// Stable W83 record-group id.
    pub record_group_id: &'static str,
    /// Stable runtime record type name.
    pub runtime_record: &'static str,
    /// Fields represented by this record.
    pub fields: Vec<FmlaRuntimeLedgerField>,
    /// Whether this record opens its gate. Always false in W88.
    pub gate_open: bool,
}

/// Source dependencies for replaying the guarded-equivalence sample.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmlaRuntimeReplayDependencies {
    /// Guard/lhs/rhs source variables keyed by stable names.
    pub guard_lhs_rhs: BTreeMap<&'static str, i32>,
    /// Source clause ids consumed by the representative transaction.
    pub source_clause_ids: Vec<usize>,
}

/// Source-visible capture for one representative guarded-equivalence transaction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmlaRuntimeTransactionCapture {
    /// Capture-only transaction id.
    pub transaction_id: u64,
    /// Monotonic scaffold epoch assigned before any mutation would be allowed.
    pub mutation_epoch: u64,
    /// Observed clause epoch before mutation. The scaffold never mutates it.
    pub pre_mutation_clause_epoch: u64,
    /// Candidate removed original DIMACS variable.
    pub removed_original_var: i32,
    /// Candidate retained original DIMACS variable.
    pub retained_original_var: i32,
    /// Append-only model reconstruction stack index reserved by the scaffold.
    pub model_reconstruction_stack_index: usize,
    /// One-hot guard-group source witness.
    pub guard_group: FmlaOneHotGroupWitness,
    /// Guarded-equivalence source witness.
    pub guarded_equivalence: FmlaGuardedEquivalenceWitness,
    /// Replay dependencies anchored to the source CNF.
    pub replay_dependencies: FmlaRuntimeReplayDependencies,
    /// Witness checker failures. Empty means the scaffold witness passed.
    pub witness_checker_failures: Vec<String>,
}

/// Aggregate counters for the capture-only runtime ledger.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct FmlaRuntimeLedgerStats {
    /// Whether capture mode was explicitly enabled.
    pub capture_enabled: bool,
    /// Runtime records emitted in the current ledger.
    pub records_emitted: u64,
    /// Distinct record groups emitted in the current ledger.
    pub record_groups_emitted: u64,
    /// W83 runtime-required fields represented exactly once.
    pub runtime_required_fields_represented: u64,
    /// W83 runtime-required fields represented more than once.
    pub duplicate_represented_fields: u64,
    /// Transactions whose source witness passed the scaffold checker.
    pub witness_checker_passed: u64,
    /// Transactions whose source witness failed the scaffold checker.
    pub witness_checker_failed: u64,
    /// Whether SAT model reconstruction is ready. Always false in W88.
    pub model_reconstruction_ready: bool,
    /// Whether UNSAT proof obligations are ready. Always false in W88.
    pub proof_obligation_ready: bool,
    /// Whether destructive transforms are allowed. Always false in W88.
    pub destructive_transform_allowed: bool,
    /// Wrong-answer claims accepted by this scaffold. Always zero.
    pub wrong_count: u64,
    /// Invalid-result claims accepted by this scaffold. Always zero.
    pub invalid_count: u64,
}

/// Default-off controls for decompose LRAT sidecar-to-main proof ledger binding.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct MainProofRewriteLedgerMaterializerConfig {
    /// Enables pure record materialization. Default false keeps the slice inert.
    pub enabled: bool,
    /// Requires an externally bound checker verdict before route admission.
    pub require_external_checker_verdict: bool,
    /// Externally retained proof-check verdict artifact. Default None fail-closes.
    pub external_checker_verdict_artifact: Option<ExternalProofCheckerVerdictArtifactRef>,
}

/// Required checker-verdict artifact shape for a proof-sensitive route.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExternalProofCheckerVerdictArtifactRequirement {
    /// Runtime ledger field that must carry this artifact.
    pub runtime_field: &'static str,
    /// Expected artifact schema.
    pub schema: &'static str,
    /// Normalized external checker verdict required for admission.
    pub accepted_verdict: &'static str,
    /// Required retained checker-verdict artifact basename.
    pub artifact_file_name: &'static str,
    /// Required solver/wrapper proof artifact basename.
    pub proof_out_file_name: &'static str,
    /// Required checker process exit code.
    pub checker_exit_code: i32,
}

/// Concrete reference to an externally produced Main/LRAT checker verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternalProofCheckerVerdictArtifactRef {
    /// Stable schema for the retained verdict artifact.
    pub schema: String,
    /// Runtime ledger field carrying this artifact.
    pub runtime_field: String,
    /// Retained verdict artifact path.
    pub artifact_path: String,
    /// SHA256 of the retained verdict artifact.
    pub artifact_sha256: String,
    /// External checker executable path.
    pub checker_path: String,
    /// SHA256 of the external checker executable.
    pub checker_sha256: String,
    /// Exact checker invocation retained by the wrapper/matrix path.
    pub checker_command: String,
    /// Exact checker argv retained by the wrapper/matrix path.
    pub checker_argv: Vec<String>,
    /// External checker process exit code.
    pub checker_exit_code: i32,
    /// Solver/wrapper-produced proof.out path checked by the external checker.
    pub proof_out_path: String,
    /// SHA256 of the checked proof.out.
    pub proof_out_sha256: String,
    /// Original or legal reconstructed DIMACS checked with proof.out.
    pub checked_dimacs_path: String,
    /// SHA256 of the checked DIMACS.
    pub checked_dimacs_sha256: String,
    /// Normalized external checker verdict.
    pub verdict: String,
}

/// One checker-facing proof rewrite row bound to a retained decompose sidecar.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MainProofRewriteLedgerRecord {
    /// Decompose transaction id retained with the sidecar context.
    pub runtime_decompose_transaction_id: u64,
    /// Stable context token generated for the retained sidecar window.
    pub sidecar_context_token: String,
    /// Retained sidecar row index.
    pub sidecar_row_index: usize,
    /// Stable source row id for the original clause rewrite.
    pub source_row_id: String,
    /// Stable proof obligation id for this sidecar row.
    pub obligation_id: String,
    /// Runtime field represented by this proof row.
    pub proof_field: &'static str,
    /// Add/delete proof output record kind.
    pub proof_out_record_kind: DecomposeProofOutRecordKind,
    /// Checker-visible LRAT id emitted by the proof manager.
    pub checker_visible_id: u64,
    /// Source clause id for deletion rows.
    pub delete_source_id: Option<u64>,
    /// Original DIMACS clause id retained by the dry-run sidecar.
    pub source_clause_id: u64,
    /// Original DIMACS source clause literals retained by the dry-run sidecar.
    pub source_clause_lits: Vec<i64>,
    /// Rewritten clause literals retained by the dry-run sidecar.
    pub rewritten_clause_lits: Vec<i64>,
    /// Clause literals recorded by the scoped proof-manager observer.
    pub clause_lits_dimacs: Vec<i64>,
    /// File-visible LRAT hints recorded by the scoped proof-manager observer.
    pub lrat_hints: Vec<u64>,
    /// Proof manager mode label recorded by the scoped observer.
    pub proof_manager_mode: &'static str,
    /// Whether the scoped proof manager observed a runtime emission.
    pub solver_runtime_emitted: bool,
    /// Whether the proof writer reported IO failure.
    pub proof_writer_io_error: bool,
    /// Whether a retained external checker verdict artifact was accepted.
    pub external_checker_verified: bool,
    /// Externally retained proof-check verdict artifact, when bound.
    pub external_checker_verdict_artifact: Option<ExternalProofCheckerVerdictArtifactRef>,
}

/// Source-bound multiplier/equivalence LRAT row role for #9761/#9725.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SourceBoundMultiplierLratRowKind {
    /// A strengthened original clause emitted as a derived LRAT add row.
    StrengtheningAdd,
    /// A BVE-style resolvent emitted as a derived LRAT add row.
    ResolventAdd,
    /// A source-clause delete row.
    SourceDelete,
    /// A source-bound conservation obligation emitted as a derived add row.
    ConservationAdd,
    /// A directional equivalence obligation emitted as a derived add row.
    EquivalenceAdd,
    /// A final contradiction obligation emitted as a derived add row.
    ContradictionAdd,
}

#[cfg_attr(not(test), allow(dead_code))]
impl SourceBoundMultiplierLratRowKind {
    #[must_use]
    pub(crate) const fn as_str(self) -> &'static str {
        match self {
            Self::StrengtheningAdd => "strengthening-add",
            Self::ResolventAdd => "resolvent-add",
            Self::SourceDelete => "source-delete",
            Self::ConservationAdd => "conservation-add",
            Self::EquivalenceAdd => "equivalence-add",
            Self::ContradictionAdd => "contradiction-add",
        }
    }

    #[must_use]
    const fn proof_out_kind(self) -> DecomposeProofOutRecordKind {
        match self {
            Self::SourceDelete => DecomposeProofOutRecordKind::Delete,
            Self::StrengtheningAdd
            | Self::ResolventAdd
            | Self::ConservationAdd
            | Self::EquivalenceAdd
            | Self::ContradictionAdd => DecomposeProofOutRecordKind::Add,
        }
    }
}

/// One source-bound multiplier/equivalence LRAT row planned by #9761/#9725.
///
/// This is a retained sidecar row only. It does not authorize UNSAT or route
/// admission unless the matching runtime `proof.out` row is present and an
/// external checker artifact binds the exact original DIMACS proof.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SourceBoundMultiplierLratSidecarRow {
    /// Row index in the retained materializer sidecar.
    pub sidecar_row_index: usize,
    /// Stable role for the planned proof row.
    pub row_kind: SourceBoundMultiplierLratRowKind,
    /// Original one-based DIMACS source-clause ID.
    pub source_clause_id: u64,
    /// Original source-clause literals in DIMACS form.
    pub source_clause_lits: Vec<i64>,
    /// Planned checker-visible LRAT add id, or source delete id for deletes.
    pub checker_visible_id: u64,
    /// Delete target for source-delete rows.
    pub delete_source_id: Option<u64>,
    /// Clause literals expected in the runtime proof row.
    pub clause_lits_dimacs: Vec<i64>,
    /// File-visible LRAT hints expected in the runtime proof row.
    pub lrat_hints: Vec<u64>,
}

/// Test-only source-bound BVE/multiplier proof-plan row accepted by the #9761
/// materializer bridge.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SourceBoundMultiplierLratPlanRow {
    /// Stable role for the planned proof row.
    pub row_kind: SourceBoundMultiplierLratRowKind,
    /// Original one-based DIMACS source-clause ID.
    pub source_clause_id: u64,
    /// Original source-clause literals in DIMACS form.
    pub source_clause_lits: Vec<i64>,
    /// Planned checker-visible LRAT add id, or source delete id for deletes.
    pub checker_visible_id: u64,
    /// Delete target for source-delete rows.
    pub delete_source_id: Option<u64>,
    /// Clause literals expected in the runtime proof row.
    pub clause_lits_dimacs: Vec<i64>,
    /// File-visible LRAT hints expected in the runtime proof row.
    pub lrat_hints: Vec<u64>,
}

/// Fail-closed rejection reasons for the test-only source-bound plan bridge.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SourceBoundMultiplierLratPlanBridgeReject {
    /// A required nonzero id was absent.
    ZeroId {
        field: &'static str,
        plan_row_index: usize,
    },
    /// A derived/add row had no LRAT hints.
    AddMissingHints { plan_row_index: usize },
    /// A source delete row did not bind its delete id to the checker-visible id.
    DeleteIdMismatch {
        plan_row_index: usize,
        checker_visible_id: u64,
        delete_source_id: Option<u64>,
    },
    /// A source delete row carried LRAT hints.
    DeleteHintsPresent { plan_row_index: usize },
    /// A DIMACS literal could not be converted to the internal literal type.
    InvalidDimacsLiteral { plan_row_index: usize, literal: i64 },
    /// The fixture proof manager failed while emitting a scoped row.
    ProofManagerEmitFailed { plan_row_index: usize },
    /// The fixture proof manager emitted a different checker-visible id.
    ProofManagerIdMismatch {
        plan_row_index: usize,
        expected: u64,
        observed: u64,
    },
}

/// Test-only output from adapting source-bound BVE/multiplier proof-plan rows.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SourceBoundMultiplierLratPlanAdapterOutput {
    /// Typed sidecars accepted by the proof-row materializer.
    pub sidecars: Vec<SourceBoundMultiplierLratSidecarRow>,
    /// Original-DIMACS binding counters for the accepted sidecars.
    pub source_binding_stats: SourceBoundMultiplierOriginalSourceBindingStats,
}

/// Fail-closed rejection reasons for the test-only source-bound plan adapter.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SourceBoundMultiplierLratPlanAdapterReject {
    /// The plan-row shape itself was invalid.
    PlanBridge(SourceBoundMultiplierLratPlanBridgeReject),
    /// The plan did not bind back to exact original DIMACS source rows.
    OriginalSourceBinding(SourceBoundMultiplierOriginalSourceBindingReject),
}

/// Counters for binding retained source-bound rows to the original DIMACS
/// clause ledger.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct SourceBoundMultiplierOriginalSourceBindingStats {
    /// Sidecar rows checked against the source ledger.
    pub rows_checked: u64,
    /// Unique original source rows referenced by the sidecar rows.
    pub unique_source_rows_checked: u64,
    /// First one-based original source clause referenced, if any.
    pub first_source_clause_id: Option<u64>,
    /// Last one-based original source clause referenced, if any.
    pub last_source_clause_id: Option<u64>,
}

/// Fail-closed rejection reasons for original-DIMACS source binding.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SourceBoundMultiplierOriginalSourceBindingReject {
    /// A sidecar row had source ID zero.
    ZeroSourceClauseId { sidecar_row_index: usize },
    /// A one-based source ID could not be represented as a local index.
    SourceClauseIdOverflow {
        sidecar_row_index: usize,
        source_clause_id: u64,
    },
    /// A source ID did not name an original clause.
    SourceClauseIdOutOfRange {
        sidecar_row_index: usize,
        source_clause_id: u64,
        original_clause_count: usize,
    },
    /// The retained source literals did not match the original DIMACS clause.
    SourceClauseLiteralMismatch {
        sidecar_row_index: usize,
        source_clause_id: u64,
        expected: Vec<i64>,
        observed: Vec<i64>,
    },
    /// A delete row did not delete the source row it claims to bind.
    DeleteSourceIdMismatch {
        sidecar_row_index: usize,
        source_clause_id: u64,
        delete_source_id: Option<u64>,
    },
}

/// Bind source-bound multiplier/equivalence sidecars to the original DIMACS
/// ledger by exact one-based source row and literal sequence.
///
/// This is observation-only. It does not emit proof rows, validate LRAT, admit
/// routes, or infer SAT-COMP correctness. It gives the proof bridge a
/// fail-closed source-literal gate before any checker-facing proof authority is
/// considered.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn validate_source_bound_multiplier_original_source_bindings<'a, I>(
    sidecars: &[SourceBoundMultiplierLratSidecarRow],
    original_clauses: I,
) -> Result<
    SourceBoundMultiplierOriginalSourceBindingStats,
    SourceBoundMultiplierOriginalSourceBindingReject,
>
where
    I: IntoIterator<Item = &'a [Literal]>,
{
    let original_dimacs: Vec<Vec<i64>> = original_clauses
        .into_iter()
        .map(|clause| {
            clause
                .iter()
                .map(|lit| i64::from(lit.to_dimacs()))
                .collect()
        })
        .collect();

    let mut seen_source_ids = BTreeSet::new();
    for row in sidecars {
        if row.source_clause_id == 0 {
            return Err(
                SourceBoundMultiplierOriginalSourceBindingReject::ZeroSourceClauseId {
                    sidecar_row_index: row.sidecar_row_index,
                },
            );
        }
        let zero_based_id = row.source_clause_id - 1;
        let source_index = usize::try_from(zero_based_id).map_err(|_| {
            SourceBoundMultiplierOriginalSourceBindingReject::SourceClauseIdOverflow {
                sidecar_row_index: row.sidecar_row_index,
                source_clause_id: row.source_clause_id,
            }
        })?;
        let Some(observed) = original_dimacs.get(source_index) else {
            return Err(
                SourceBoundMultiplierOriginalSourceBindingReject::SourceClauseIdOutOfRange {
                    sidecar_row_index: row.sidecar_row_index,
                    source_clause_id: row.source_clause_id,
                    original_clause_count: original_dimacs.len(),
                },
            );
        };
        if observed != &row.source_clause_lits {
            return Err(
                SourceBoundMultiplierOriginalSourceBindingReject::SourceClauseLiteralMismatch {
                    sidecar_row_index: row.sidecar_row_index,
                    source_clause_id: row.source_clause_id,
                    expected: row.source_clause_lits.clone(),
                    observed: observed.clone(),
                },
            );
        }
        if row.row_kind.proof_out_kind() == DecomposeProofOutRecordKind::Delete
            && row.delete_source_id != Some(row.source_clause_id)
        {
            return Err(
                SourceBoundMultiplierOriginalSourceBindingReject::DeleteSourceIdMismatch {
                    sidecar_row_index: row.sidecar_row_index,
                    source_clause_id: row.source_clause_id,
                    delete_source_id: row.delete_source_id,
                },
            );
        }
        seen_source_ids.insert(row.source_clause_id);
    }

    Ok(SourceBoundMultiplierOriginalSourceBindingStats {
        rows_checked: sidecars.len() as u64,
        unique_source_rows_checked: seen_source_ids.len() as u64,
        first_source_clause_id: seen_source_ids.first().copied(),
        last_source_clause_id: seen_source_ids.last().copied(),
    })
}

/// Scoped context for one source-bound multiplier/equivalence LRAT row.
#[cfg_attr(not(test), allow(dead_code))]
#[must_use]
pub(crate) fn source_bound_multiplier_lrat_context(
    transaction_id: u64,
    row: &SourceBoundMultiplierLratSidecarRow,
) -> DecomposeProofEmitContext {
    DecomposeProofEmitContext {
        transaction_id,
        sidecar_context_token: format!("source-bound-multiplier-lrat-{transaction_id}"),
        sidecar_row_index: row.sidecar_row_index,
        source_row_id: format!("source-bound-multiplier-source-{}", row.source_clause_id),
        obligation_id: format!(
            "source-bound-multiplier-{transaction_id}-{}-{}",
            row.sidecar_row_index,
            row.row_kind.as_str()
        ),
    }
}

/// Convert retained BVE/multiplier proof-plan rows into typed materializer
/// sidecar rows.
///
/// This is test-only and fail-closed. It does not infer proof validity, emit
/// proof, mutate clauses, or enable any solver route.
#[cfg(test)]
pub(crate) fn source_bound_multiplier_lrat_sidecars_from_plan_rows(
    rows: &[SourceBoundMultiplierLratPlanRow],
) -> Result<Vec<SourceBoundMultiplierLratSidecarRow>, SourceBoundMultiplierLratPlanBridgeReject> {
    rows.iter()
        .enumerate()
        .map(|(sidecar_row_index, row)| {
            validate_source_bound_multiplier_plan_row(sidecar_row_index, row)?;
            Ok(SourceBoundMultiplierLratSidecarRow {
                sidecar_row_index,
                row_kind: row.row_kind,
                source_clause_id: row.source_clause_id,
                source_clause_lits: row.source_clause_lits.clone(),
                checker_visible_id: row.checker_visible_id,
                delete_source_id: row.delete_source_id,
                clause_lits_dimacs: row.clause_lits_dimacs.clone(),
                lrat_hints: row.lrat_hints.clone(),
            })
        })
        .collect()
}

/// Adapt retained source-bound BVE/multiplier proof-plan rows into typed
/// sidecars only after binding every row to the original DIMACS source ledger.
///
/// This is test-only and fail-closed. It does not emit proof, validate LRAT,
/// mutate clauses, or admit a solver route.
#[cfg(test)]
pub(crate) fn source_bound_multiplier_lrat_sidecars_from_original_source_plan_rows<'a, I>(
    rows: &[SourceBoundMultiplierLratPlanRow],
    original_clauses: I,
) -> Result<SourceBoundMultiplierLratPlanAdapterOutput, SourceBoundMultiplierLratPlanAdapterReject>
where
    I: IntoIterator<Item = &'a [Literal]>,
{
    let sidecars = source_bound_multiplier_lrat_sidecars_from_plan_rows(rows)
        .map_err(SourceBoundMultiplierLratPlanAdapterReject::PlanBridge)?;
    let source_binding_stats =
        validate_source_bound_multiplier_original_source_bindings(&sidecars, original_clauses)
            .map_err(SourceBoundMultiplierLratPlanAdapterReject::OriginalSourceBinding)?;
    Ok(SourceBoundMultiplierLratPlanAdapterOutput {
        sidecars,
        source_binding_stats,
    })
}

/// Replay source-bound sidecars through a fixture proof manager and return the
/// resulting decompose-compatible proof observer rows.
///
/// The returned records are suitable for exercising the pure materializer in
/// tests. Production proof rows must still come from `ProofManager` observers.
#[cfg(test)]
pub(crate) fn source_bound_multiplier_lrat_replay_test_proof_records_from_sidecars(
    proof_manager: &mut ProofManager,
    transaction_id: u64,
    sidecars: &[SourceBoundMultiplierLratSidecarRow],
) -> Result<Vec<DecomposeProofEmitRecord>, SourceBoundMultiplierLratPlanBridgeReject> {
    let record_start = proof_manager.scoped_decompose_proof_emit_records().len();
    for row in sidecars {
        let context = source_bound_multiplier_lrat_context(transaction_id, row);
        let clause =
            source_bound_multiplier_dimacs_lits(row.sidecar_row_index, &row.clause_lits_dimacs)?;
        match row.row_kind.proof_out_kind() {
            DecomposeProofOutRecordKind::Add => {
                let observed = proof_manager
                    .emit_add_with_decompose_context(
                        &clause,
                        &row.lrat_hints,
                        crate::proof_manager::ProofAddKind::Derived,
                        &context,
                    )
                    .map_err(|_| {
                        SourceBoundMultiplierLratPlanBridgeReject::ProofManagerEmitFailed {
                            plan_row_index: row.sidecar_row_index,
                        }
                    })?;
                if observed != row.checker_visible_id {
                    return Err(
                        SourceBoundMultiplierLratPlanBridgeReject::ProofManagerIdMismatch {
                            plan_row_index: row.sidecar_row_index,
                            expected: row.checker_visible_id,
                            observed,
                        },
                    );
                }
            }
            DecomposeProofOutRecordKind::Delete => {
                proof_manager
                    .emit_delete_with_decompose_context(&clause, row.checker_visible_id, &context)
                    .map_err(|_| {
                        SourceBoundMultiplierLratPlanBridgeReject::ProofManagerEmitFailed {
                            plan_row_index: row.sidecar_row_index,
                        }
                    })?;
            }
        }
    }

    Ok(proof_manager.scoped_decompose_proof_emit_records()[record_start..].to_vec())
}

#[cfg(test)]
fn source_bound_multiplier_dimacs_lits(
    plan_row_index: usize,
    lits: &[i64],
) -> Result<Vec<Literal>, SourceBoundMultiplierLratPlanBridgeReject> {
    lits.iter()
        .map(|&lit| {
            let dimacs_lit = i32::try_from(lit).map_err(|_| {
                SourceBoundMultiplierLratPlanBridgeReject::InvalidDimacsLiteral {
                    plan_row_index,
                    literal: lit,
                }
            })?;
            if dimacs_lit == 0 {
                return Err(
                    SourceBoundMultiplierLratPlanBridgeReject::InvalidDimacsLiteral {
                        plan_row_index,
                        literal: lit,
                    },
                );
            }
            Ok(Literal::from_dimacs(dimacs_lit))
        })
        .collect()
}

#[cfg(test)]
fn validate_source_bound_multiplier_plan_row(
    plan_row_index: usize,
    row: &SourceBoundMultiplierLratPlanRow,
) -> Result<(), SourceBoundMultiplierLratPlanBridgeReject> {
    validate_plan_nonzero("source_clause_id", row.source_clause_id, plan_row_index)?;
    validate_plan_nonzero("checker_visible_id", row.checker_visible_id, plan_row_index)?;
    match row.row_kind.proof_out_kind() {
        DecomposeProofOutRecordKind::Add => {
            if row.lrat_hints.is_empty() {
                return Err(SourceBoundMultiplierLratPlanBridgeReject::AddMissingHints {
                    plan_row_index,
                });
            }
            if row.delete_source_id.is_some() {
                return Err(
                    SourceBoundMultiplierLratPlanBridgeReject::DeleteIdMismatch {
                        plan_row_index,
                        checker_visible_id: row.checker_visible_id,
                        delete_source_id: row.delete_source_id,
                    },
                );
            }
        }
        DecomposeProofOutRecordKind::Delete => {
            if row.delete_source_id != Some(row.checker_visible_id) {
                return Err(
                    SourceBoundMultiplierLratPlanBridgeReject::DeleteIdMismatch {
                        plan_row_index,
                        checker_visible_id: row.checker_visible_id,
                        delete_source_id: row.delete_source_id,
                    },
                );
            }
            if !row.lrat_hints.is_empty() {
                return Err(
                    SourceBoundMultiplierLratPlanBridgeReject::DeleteHintsPresent {
                        plan_row_index,
                    },
                );
            }
        }
    }
    Ok(())
}

#[cfg(test)]
fn validate_plan_nonzero(
    field: &'static str,
    value: u64,
    plan_row_index: usize,
) -> Result<(), SourceBoundMultiplierLratPlanBridgeReject> {
    if value == 0 {
        return Err(SourceBoundMultiplierLratPlanBridgeReject::ZeroId {
            field,
            plan_row_index,
        });
    }
    Ok(())
}

/// Aggregate counters for the pure proof rewrite ledger materializer.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct MainProofRewriteLedgerMaterializerStats {
    /// Whether the materializer was explicitly enabled.
    pub enabled: bool,
    /// Sidecar rows inspected.
    pub sidecar_rows_seen: u64,
    /// Scoped proof-manager records inspected.
    pub proof_emit_records_seen: u64,
    /// Main proof rewrite ledger rows materialized.
    pub records_materialized: u64,
    /// Derived/addition proof rows materialized.
    pub derived_clause_proof_steps_materialized: u64,
    /// Deletion proof rows materialized.
    pub deletion_proof_steps_materialized: u64,
    /// Materialized rows bound to a retained external checker verdict artifact.
    pub external_checker_verdict_artifact_rows: u64,
    /// Whether materialization failed closed.
    pub fail_closed: bool,
}

/// Solver-side counters needed to replay Fmla admission after proof.out is checked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FmlaPostCheckAdmissionReplayInput {
    /// Solver-side materializer attempts.
    pub materializer_attempts: u64,
    /// Scoped proof-manager rows seen by the solver-side materializer.
    pub materializer_proof_emit_records_seen: u64,
    /// Solver-side rows materialized before fail-closed admission.
    pub materializer_records: u64,
    /// Solver-side materializer fail-closed count.
    pub materializer_fail_closed: u64,
    /// Solver-side missing-runtime-record fail-closed count.
    pub materializer_missing_runtime_records: u64,
    /// Solver-side transaction fail-closed count.
    pub preprocess_tx_fail_closed: u64,
    /// Solver-side committed count before post-check replay.
    pub preprocess_tx_committed: u64,
}

/// Post-solve/post-check Fmla route admission replay record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmlaPostCheckAdmissionReplayRecord {
    /// Stable replay schema.
    pub schema: &'static str,
    /// Replay disposition.
    pub status: &'static str,
    /// Solver-side materialized proof rows.
    pub proof_obligation_rows: u64,
    /// Checker artifact rows visible after replay.
    pub external_checker_verdict_artifact_rows: u64,
    /// Pre-replay solver-side materializer fail-closed count.
    pub pre_replay_materializer_fail_closed: u64,
    /// Pre-replay solver-side transaction fail-closed count.
    pub pre_replay_preprocess_tx_fail_closed: u64,
    /// Post-replay admission commit count for evidence only.
    pub post_replay_preprocess_tx_committed: u64,
    /// Bound checker artifact.
    pub external_checker_verdict_artifact: ExternalProofCheckerVerdictArtifactRef,
}

/// Result of binding a solver-exported learned-LRAT dry-run fragment to a
/// same-run post-check replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmlaLearnedLratMainProofAuthorityReplayRecord {
    /// Authority disposition: `authorized` or `fail_closed`.
    pub status: &'static str,
    /// Stable fail-closed reason when authority is absent.
    pub reason: Option<String>,
    /// Checker-visible learned clause id from the dry-run fragment.
    pub checker_visible_id: Option<u64>,
    /// Retained wrapper proof.out path accepted by the checker artifact.
    pub proof_out_path: Option<String>,
    /// SHA256 of the retained proof.out bytes.
    pub proof_out_sha256: Option<String>,
    /// Whether the external checker verdict was accepted.
    pub external_checker_verified: bool,
    /// Whether proof.out contains the imported LRAT fragment bytes.
    pub proof_out_contains_lrat_fragment: bool,
    /// Whether this record authorizes Main proof.out for the learned fragment.
    pub authorizes_main_proof_out: bool,
}

/// Fail-closed post-check replay rejection reasons.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FmlaPostCheckAdmissionReplayReject {
    /// Solver-side materializer was not exercised.
    MaterializerNotExercised,
    /// Solver-side materializer did not retain proof rows.
    MissingMaterializedRows,
    /// Solver-side materializer failed for missing runtime rows, not checker evidence.
    MissingRuntimeRows,
    /// Solver-side transaction was already committed before post-check replay.
    AlreadyCommitted,
    /// Solver-side transaction did not fail closed before post-check replay.
    NotFailClosed,
    /// No retained checker verdict artifact was supplied after external checking.
    MissingExternalCheckerVerdict,
    /// The retained checker verdict artifact did not satisfy the admission contract.
    ExternalCheckerVerdictNotAccepted {
        /// Checker artifact validation rejection reason.
        reason: &'static str,
    },
}

/// Fail-closed rejection reasons for proof rewrite ledger materialization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MainProofRewriteLedgerMaterializerReject {
    /// The sidecar/context slices are not one-to-one.
    SidecarContextCountMismatch { sidecars: usize, contexts: usize },
    /// A retained context does not bind the expected sidecar row.
    ContextRowMismatch { expected: usize, observed: usize },
    /// Source-bound multiplier/equivalence rows did not bind the original DIMACS ledger.
    OriginalSourceBinding(SourceBoundMultiplierOriginalSourceBindingReject),
    /// A required nonzero id was absent.
    ZeroId {
        field: &'static str,
        sidecar_row_index: usize,
    },
    /// A scoped proof-manager add row was missing.
    MissingAddRecord {
        sidecar_row_index: usize,
        checker_visible_id: u64,
    },
    /// A scoped proof-manager delete row was missing.
    MissingDeleteRecord {
        sidecar_row_index: usize,
        delete_source_id: u64,
    },
    /// A scoped proof row had the wrong proof field or record kind.
    MismatchedProofRecord {
        sidecar_row_index: usize,
        checker_visible_id: u64,
    },
    /// A scoped proof row did not match the retained decompose sidecar payload.
    ProofRecordPayloadMismatch {
        sidecar_row_index: usize,
        checker_visible_id: u64,
        field: &'static str,
    },
    /// A scoped proof row reported runtime proof-writer IO failure.
    ProofWriterIoError {
        sidecar_row_index: usize,
        checker_visible_id: u64,
    },
    /// A scoped proof row was not actually emitted by the solver runtime.
    RuntimeProofRecordNotEmitted {
        sidecar_row_index: usize,
        checker_visible_id: u64,
    },
    /// External checker acceptance was injected before this materializer can bind it.
    ExternalCheckerVerdictNotAccepted {
        sidecar_row_index: usize,
        checker_visible_id: u64,
        reason: &'static str,
    },
    /// Runtime rows were materialized but no external checker verdict was bound.
    MissingExternalCheckerVerdict {
        sidecar_row_index: usize,
        checker_visible_id: u64,
        materialized_records: usize,
        required_artifact: ExternalProofCheckerVerdictArtifactRequirement,
    },
}

/// Pure materialization result for the default-off proof rewrite ledger.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MainProofRewriteLedgerMaterialization {
    /// Materialized main proof rewrite rows.
    pub records: Vec<MainProofRewriteLedgerRecord>,
    /// Counters for the materialization attempt.
    pub stats: MainProofRewriteLedgerMaterializerStats,
}

/// Replay Fmla admission after proof.out has been externally checked.
///
/// This is an evidence-only post-solve replay. It does not emit proof, mutate
/// clauses, reconstruct models, or influence the solver result.
pub fn replay_fmla_postcheck_admission(
    input: FmlaPostCheckAdmissionReplayInput,
    artifact: Option<ExternalProofCheckerVerdictArtifactRef>,
) -> Result<FmlaPostCheckAdmissionReplayRecord, FmlaPostCheckAdmissionReplayReject> {
    if input.materializer_attempts == 0 || input.materializer_proof_emit_records_seen == 0 {
        return Err(FmlaPostCheckAdmissionReplayReject::MaterializerNotExercised);
    }
    if input.materializer_records == 0 {
        return Err(FmlaPostCheckAdmissionReplayReject::MissingMaterializedRows);
    }
    if input.materializer_missing_runtime_records != 0 {
        return Err(FmlaPostCheckAdmissionReplayReject::MissingRuntimeRows);
    }
    if input.preprocess_tx_committed != 0 {
        return Err(FmlaPostCheckAdmissionReplayReject::AlreadyCommitted);
    }
    if input.materializer_fail_closed == 0 || input.preprocess_tx_fail_closed == 0 {
        return Err(FmlaPostCheckAdmissionReplayReject::NotFailClosed);
    }
    let Some(artifact) = artifact else {
        return Err(FmlaPostCheckAdmissionReplayReject::MissingExternalCheckerVerdict);
    };
    if let Err(reason) = validate_external_checker_verdict_artifact(&artifact) {
        return Err(
            FmlaPostCheckAdmissionReplayReject::ExternalCheckerVerdictNotAccepted { reason },
        );
    }
    Ok(FmlaPostCheckAdmissionReplayRecord {
        schema: FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA,
        status: "committed_checker_backed_admission",
        proof_obligation_rows: input.materializer_records,
        external_checker_verdict_artifact_rows: input.materializer_records,
        pre_replay_materializer_fail_closed: input.materializer_fail_closed,
        pre_replay_preprocess_tx_fail_closed: input.preprocess_tx_fail_closed,
        post_replay_preprocess_tx_committed: 1,
        external_checker_verdict_artifact: artifact,
    })
}

/// Validate a solver-exported learned-LRAT dry-run proof artifact against a
/// committed same-run post-check replay and retained proof.out bytes.
///
/// This remains evidence-only. Any malformed, stale, or incomplete dry-run
/// payload returns `fail_closed` and never authorizes Main proof output.
pub fn validate_fmla_learned_lrat_main_proof_authority_from_json_postcheck_replay(
    dry_run_artifact: &Value,
    postcheck_replay: &FmlaPostCheckAdmissionReplayRecord,
    retained_proof_out_path: &str,
    proof_out_bytes: &[u8],
) -> FmlaLearnedLratMainProofAuthorityReplayRecord {
    let envelope =
        match ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_from_json_value(
            dry_run_artifact,
        ) {
            Ok(envelope) => envelope,
            Err(reject) => {
                return learned_lrat_main_proof_authority_fail_closed(
                    learned_lrat_dry_run_import_reject_reason(&reject),
                )
            }
        };
    let dry_run = match ProofManager::import_fmla_learned_lrat_dry_run_proof_artifact(envelope) {
        Ok(dry_run) => dry_run,
        Err(reject) => {
            return learned_lrat_main_proof_authority_fail_closed(
                learned_lrat_dry_run_import_reject_reason(&reject),
            )
        }
    };
    match ProofManager::validate_fmla_learned_lrat_main_proof_authority_from_postcheck_replay(
        &dry_run,
        postcheck_replay,
        retained_proof_out_path,
        proof_out_bytes,
    ) {
        Ok(authority) => FmlaLearnedLratMainProofAuthorityReplayRecord {
            status: "authorized",
            reason: None,
            checker_visible_id: Some(authority.checker_visible_id),
            proof_out_path: Some(authority.proof_out_path),
            proof_out_sha256: Some(authority.proof_out_sha256),
            external_checker_verified: authority.external_checker_verified,
            proof_out_contains_lrat_fragment: authority.proof_out_contains_lrat_fragment,
            authorizes_main_proof_out: authority.authorizes_main_proof_out,
        },
        Err(reject) => learned_lrat_main_proof_authority_fail_closed(
            learned_lrat_main_proof_authority_reject_reason(&reject),
        ),
    }
}

fn learned_lrat_main_proof_authority_fail_closed(
    reason: String,
) -> FmlaLearnedLratMainProofAuthorityReplayRecord {
    FmlaLearnedLratMainProofAuthorityReplayRecord {
        status: "fail_closed",
        reason: Some(reason),
        checker_visible_id: None,
        proof_out_path: None,
        proof_out_sha256: None,
        external_checker_verified: false,
        proof_out_contains_lrat_fragment: false,
        authorizes_main_proof_out: false,
    }
}

fn learned_lrat_dry_run_import_reject_reason(
    reject: &LearnedLratDryRunProofArtifactImportReject,
) -> String {
    match reject {
        LearnedLratDryRunProofArtifactImportReject::MissingField(field) => {
            format!("dry_run_artifact_missing_field:{field}")
        }
        LearnedLratDryRunProofArtifactImportReject::InvalidField(field) => {
            format!("dry_run_artifact_invalid_field:{field}")
        }
        LearnedLratDryRunProofArtifactImportReject::SchemaMismatch { .. } => {
            "dry_run_artifact_schema_mismatch".to_string()
        }
        LearnedLratDryRunProofArtifactImportReject::LratFragmentSha256Mismatch => {
            "dry_run_artifact_lrat_fragment_sha256_mismatch".to_string()
        }
        LearnedLratDryRunProofArtifactImportReject::LratFragmentRowsMismatch => {
            "dry_run_artifact_lrat_fragment_rows_mismatch".to_string()
        }
        LearnedLratDryRunProofArtifactImportReject::InvalidAuthorityState => {
            "dry_run_artifact_invalid_authority_state".to_string()
        }
        LearnedLratDryRunProofArtifactImportReject::InvalidAuthorityReason { .. } => {
            "dry_run_artifact_invalid_authority_reason".to_string()
        }
        LearnedLratDryRunProofArtifactImportReject::ReplayRowsMalformed => {
            "dry_run_artifact_replay_rows_malformed".to_string()
        }
    }
}

fn learned_lrat_main_proof_authority_reject_reason(
    reject: &LearnedLratMainProofAuthorityReject,
) -> String {
    match reject {
        LearnedLratMainProofAuthorityReject::DryRunNotComplete { .. } => {
            "learned_lrat_dry_run_not_complete".to_string()
        }
        LearnedLratMainProofAuthorityReject::DryRunFragmentMissing => {
            "learned_lrat_dry_run_fragment_missing".to_string()
        }
        LearnedLratMainProofAuthorityReject::DryRunInvalidAuthorityState => {
            "learned_lrat_dry_run_invalid_authority_state".to_string()
        }
        LearnedLratMainProofAuthorityReject::ExternalCheckerVerdictNotAccepted { reason } => {
            format!("external_checker_verdict_not_accepted:{reason}")
        }
        LearnedLratMainProofAuthorityReject::ProofOutSha256Mismatch => {
            "proof_out_sha256_mismatch".to_string()
        }
        LearnedLratMainProofAuthorityReject::ProofOutNotUtf8 => "proof_out_not_utf8".to_string(),
        LearnedLratMainProofAuthorityReject::ProofOutMissingDryRunFragment => {
            "proof_out_missing_dry_run_fragment".to_string()
        }
        LearnedLratMainProofAuthorityReject::PostCheckReplayNotCommitted { .. } => {
            "postcheck_replay_not_committed".to_string()
        }
        LearnedLratMainProofAuthorityReject::PostCheckReplayMissingProofRows => {
            "postcheck_replay_missing_proof_rows".to_string()
        }
        LearnedLratMainProofAuthorityReject::PostCheckReplayCheckerRowMismatch { .. } => {
            "postcheck_replay_checker_row_mismatch".to_string()
        }
        LearnedLratMainProofAuthorityReject::ProofOutPathMismatch { .. } => {
            "proof_out_path_mismatch".to_string()
        }
    }
}

/// Bind retained decompose LRAT sidecars to scoped proof-manager add/delete rows.
///
/// This is a pure/default-off data materializer. It does not emit proof,
/// mutate clauses, reconstruct models, admit routes, or assert proof validity.
pub(crate) fn materialize_main_lrat_rewrite_records(
    config: MainProofRewriteLedgerMaterializerConfig,
    sidecars: &[DecomposeLratDryRunSidecar],
    contexts: &[DecomposeProofEmitContext],
    proof_records: &[DecomposeProofEmitRecord],
) -> Result<MainProofRewriteLedgerMaterialization, MainProofRewriteLedgerMaterializerReject> {
    let mut stats = MainProofRewriteLedgerMaterializerStats {
        enabled: config.enabled,
        sidecar_rows_seen: sidecars.len() as u64,
        proof_emit_records_seen: proof_records.len() as u64,
        ..MainProofRewriteLedgerMaterializerStats::default()
    };
    if !config.enabled {
        return Ok(MainProofRewriteLedgerMaterialization {
            records: Vec::new(),
            stats,
        });
    }
    if sidecars.len() != contexts.len() {
        return Err(
            MainProofRewriteLedgerMaterializerReject::SidecarContextCountMismatch {
                sidecars: sidecars.len(),
                contexts: contexts.len(),
            },
        );
    }

    let mut records = Vec::new();
    for (sidecar_row_index, (sidecar, context)) in sidecars.iter().zip(contexts).enumerate() {
        validate_context(sidecar_row_index, context)?;
        validate_nonzero(
            "source_clause_id",
            sidecar.source_clause_id,
            sidecar_row_index,
        )?;
        validate_nonzero(
            "source_delete_id",
            sidecar.source_delete_id,
            sidecar_row_index,
        )?;
        for step in &sidecar.equivalence_steps {
            let lit_to_repr_clause = [step.representative_lit, -step.original_lit];
            push_required_add_record(
                &mut records,
                sidecar,
                context,
                proof_records,
                step.planned_lit_to_repr_add_id,
                &lit_to_repr_clause,
                &step.lit_to_repr_source_ids,
            )?;
            let repr_to_lit_clause = [step.original_lit, -step.representative_lit];
            push_required_add_record(
                &mut records,
                sidecar,
                context,
                proof_records,
                step.planned_repr_to_lit_add_id,
                &repr_to_lit_clause,
                &step.repr_to_lit_source_ids,
            )?;
        }
        push_required_add_record(
            &mut records,
            sidecar,
            context,
            proof_records,
            sidecar.planned_rewrite_add_id,
            &sidecar.rewritten_clause_lits,
            &sidecar.rewrite_hints,
        )?;
        push_required_delete_record(&mut records, sidecar, context, proof_records)?;
    }

    stats.records_materialized = records.len() as u64;
    stats.derived_clause_proof_steps_materialized = records
        .iter()
        .filter(|record| record.proof_field == "derived_clause_proof_steps")
        .count() as u64;
    stats.deletion_proof_steps_materialized = records
        .iter()
        .filter(|record| record.proof_field == "deletion_proof_steps")
        .count() as u64;
    if let Some(artifact) = config.external_checker_verdict_artifact.as_ref() {
        if let Err(reason) = validate_external_checker_verdict_artifact(artifact) {
            let (sidecar_row_index, checker_visible_id) = first_record_identity(&records);
            return Err(
                MainProofRewriteLedgerMaterializerReject::ExternalCheckerVerdictNotAccepted {
                    sidecar_row_index,
                    checker_visible_id,
                    reason,
                },
            );
        }
        for record in &mut records {
            record.external_checker_verified = true;
            record.external_checker_verdict_artifact = Some(artifact.clone());
        }
        stats.external_checker_verdict_artifact_rows = records.len() as u64;
    }
    if config.require_external_checker_verdict {
        if let Some(record) = records
            .iter()
            .find(|record| record.external_checker_verdict_artifact.is_none())
        {
            return Err(
                MainProofRewriteLedgerMaterializerReject::MissingExternalCheckerVerdict {
                    sidecar_row_index: record.sidecar_row_index,
                    checker_visible_id: record.checker_visible_id,
                    materialized_records: records.len(),
                    required_artifact: FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT,
                },
            );
        }
    }
    Ok(MainProofRewriteLedgerMaterialization { records, stats })
}

/// Bind Fmla guarded-equivalence add-only sidecars to scoped proof-manager rows.
///
/// This validates the runtime LRAT rows but does not admit the route without an
/// externally checked UNSAT proof artifact.
pub(crate) fn materialize_fmla_guarded_equiv_lrat_records(
    config: MainProofRewriteLedgerMaterializerConfig,
    transaction_id: u64,
    overlay_sidecars: &[FmlaGuardedEquivOverlayLratSidecar],
    support_sidecars: &[FmlaGuardedEquivSupportCoverLratSidecar],
    proof_records: &[DecomposeProofEmitRecord],
) -> Result<MainProofRewriteLedgerMaterializerStats, MainProofRewriteLedgerMaterializerReject> {
    let mut stats = MainProofRewriteLedgerMaterializerStats {
        enabled: config.enabled,
        sidecar_rows_seen: overlay_sidecars
            .len()
            .saturating_add(support_sidecars.len()) as u64,
        proof_emit_records_seen: proof_records.len() as u64,
        ..MainProofRewriteLedgerMaterializerStats::default()
    };
    if !config.enabled {
        return Ok(stats);
    }

    for (sidecar_row_index, sidecar) in overlay_sidecars.iter().enumerate() {
        push_required_fmla_overlay_add_record(
            transaction_id,
            sidecar_row_index,
            "forward",
            &sidecar.forward_binary,
            proof_records,
        )?;
        stats.records_materialized = stats.records_materialized.saturating_add(1);
        stats.derived_clause_proof_steps_materialized = stats
            .derived_clause_proof_steps_materialized
            .saturating_add(1);

        push_required_fmla_overlay_add_record(
            transaction_id,
            sidecar_row_index,
            "reverse",
            &sidecar.reverse_binary,
            proof_records,
        )?;
        stats.records_materialized = stats.records_materialized.saturating_add(1);
        stats.derived_clause_proof_steps_materialized = stats
            .derived_clause_proof_steps_materialized
            .saturating_add(1);
    }

    for (sidecar_row_index, sidecar) in support_sidecars.iter().enumerate() {
        push_required_fmla_support_add_record(
            transaction_id,
            sidecar_row_index,
            sidecar,
            proof_records,
        )?;
        stats.records_materialized = stats.records_materialized.saturating_add(1);
        stats.derived_clause_proof_steps_materialized = stats
            .derived_clause_proof_steps_materialized
            .saturating_add(1);
    }

    if let Some(artifact) = config.external_checker_verdict_artifact.as_ref() {
        if let Err(reason) = validate_external_checker_verdict_artifact(artifact) {
            let (sidecar_row_index, checker_visible_id) =
                first_fmla_add_record_identity(overlay_sidecars, support_sidecars);
            return Err(
                MainProofRewriteLedgerMaterializerReject::ExternalCheckerVerdictNotAccepted {
                    sidecar_row_index,
                    checker_visible_id,
                    reason,
                },
            );
        }
        stats.external_checker_verdict_artifact_rows = stats.records_materialized;
    }

    if config.require_external_checker_verdict
        && stats.records_materialized > 0
        && stats.external_checker_verdict_artifact_rows != stats.records_materialized
    {
        let (sidecar_row_index, checker_visible_id) =
            first_fmla_add_record_identity(overlay_sidecars, support_sidecars);
        return Err(
            MainProofRewriteLedgerMaterializerReject::MissingExternalCheckerVerdict {
                sidecar_row_index,
                checker_visible_id,
                materialized_records: stats.records_materialized as usize,
                required_artifact: FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT,
            },
        );
    }

    Ok(stats)
}

/// Bind source-bound multiplier/equivalence rows to scoped proof-manager rows.
///
/// This is the #9761/#9725 preflight bridge from source-bound theory/diagnostics to
/// checker-facing LRAT rows. It validates exact row identity and runtime proof
/// emission, then still fail-closes unless a retained external checker verdict
/// binds the original-DIMACS `proof.out`.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn materialize_source_bound_multiplier_lrat_records<'a, I>(
    config: MainProofRewriteLedgerMaterializerConfig,
    transaction_id: u64,
    sidecars: &[SourceBoundMultiplierLratSidecarRow],
    original_clauses: I,
    proof_records: &[DecomposeProofEmitRecord],
) -> Result<MainProofRewriteLedgerMaterialization, MainProofRewriteLedgerMaterializerReject>
where
    I: IntoIterator<Item = &'a [Literal]>,
{
    let mut stats = MainProofRewriteLedgerMaterializerStats {
        enabled: config.enabled,
        sidecar_rows_seen: sidecars.len() as u64,
        proof_emit_records_seen: proof_records.len() as u64,
        ..MainProofRewriteLedgerMaterializerStats::default()
    };
    if !config.enabled {
        return Ok(MainProofRewriteLedgerMaterialization {
            records: Vec::new(),
            stats,
        });
    }

    validate_source_bound_multiplier_original_source_bindings(sidecars, original_clauses)
        .map_err(MainProofRewriteLedgerMaterializerReject::OriginalSourceBinding)?;

    let mut records = Vec::with_capacity(sidecars.len());
    for (expected_index, row) in sidecars.iter().enumerate() {
        if row.sidecar_row_index != expected_index {
            return Err(
                MainProofRewriteLedgerMaterializerReject::ContextRowMismatch {
                    expected: expected_index,
                    observed: row.sidecar_row_index,
                },
            );
        }
        let proof_record =
            push_required_source_bound_multiplier_row(transaction_id, row, proof_records)?;
        records.push(build_multiplier_proof_record(row, proof_record));
        stats.records_materialized = stats.records_materialized.saturating_add(1);
        match row.row_kind.proof_out_kind() {
            DecomposeProofOutRecordKind::Add => {
                stats.derived_clause_proof_steps_materialized = stats
                    .derived_clause_proof_steps_materialized
                    .saturating_add(1);
            }
            DecomposeProofOutRecordKind::Delete => {
                stats.deletion_proof_steps_materialized =
                    stats.deletion_proof_steps_materialized.saturating_add(1);
            }
        }
    }

    if let Some(artifact) = config.external_checker_verdict_artifact.as_ref() {
        if let Err(reason) = validate_external_checker_verdict_artifact(artifact) {
            let (sidecar_row_index, checker_visible_id) =
                first_source_bound_multiplier_identity(sidecars);
            return Err(
                MainProofRewriteLedgerMaterializerReject::ExternalCheckerVerdictNotAccepted {
                    sidecar_row_index,
                    checker_visible_id,
                    reason,
                },
            );
        }
        stats.external_checker_verdict_artifact_rows = stats.records_materialized;
        for record in &mut records {
            record.external_checker_verified = true;
            record.external_checker_verdict_artifact =
                config.external_checker_verdict_artifact.clone();
        }
    }

    if config.require_external_checker_verdict
        && stats.records_materialized > 0
        && stats.external_checker_verdict_artifact_rows != stats.records_materialized
    {
        let (sidecar_row_index, checker_visible_id) =
            first_source_bound_multiplier_identity(sidecars);
        return Err(
            MainProofRewriteLedgerMaterializerReject::MissingExternalCheckerVerdict {
                sidecar_row_index,
                checker_visible_id,
                materialized_records: stats.records_materialized as usize,
                required_artifact: FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT,
            },
        );
    }

    Ok(MainProofRewriteLedgerMaterialization { records, stats })
}

#[cfg_attr(not(test), allow(dead_code))]
fn build_multiplier_proof_record(
    sidecar: &SourceBoundMultiplierLratSidecarRow,
    proof_record: &DecomposeProofEmitRecord,
) -> MainProofRewriteLedgerRecord {
    MainProofRewriteLedgerRecord {
        runtime_decompose_transaction_id: proof_record.context.transaction_id,
        sidecar_context_token: proof_record.context.sidecar_context_token.clone(),
        sidecar_row_index: proof_record.context.sidecar_row_index,
        source_row_id: proof_record.context.source_row_id.clone(),
        obligation_id: proof_record.context.obligation_id.clone(),
        proof_field: proof_record.proof_field,
        proof_out_record_kind: proof_record.proof_out_record_kind,
        checker_visible_id: proof_record.checker_visible_id,
        delete_source_id: proof_record.delete_source_id,
        source_clause_id: sidecar.source_clause_id,
        source_clause_lits: sidecar.source_clause_lits.clone(),
        rewritten_clause_lits: sidecar.clause_lits_dimacs.clone(),
        clause_lits_dimacs: proof_record.clause_lits_dimacs.clone(),
        lrat_hints: proof_record.lrat_hints.clone(),
        proof_manager_mode: proof_record.proof_manager_mode,
        solver_runtime_emitted: proof_record.solver_runtime_emitted,
        proof_writer_io_error: proof_record.proof_writer_io_error,
        external_checker_verified: false,
        external_checker_verdict_artifact: None,
    }
}

fn validate_context(
    expected_row_index: usize,
    context: &DecomposeProofEmitContext,
) -> Result<(), MainProofRewriteLedgerMaterializerReject> {
    if context.sidecar_row_index != expected_row_index {
        return Err(
            MainProofRewriteLedgerMaterializerReject::ContextRowMismatch {
                expected: expected_row_index,
                observed: context.sidecar_row_index,
            },
        );
    }
    Ok(())
}

fn validate_nonzero(
    field: &'static str,
    value: u64,
    sidecar_row_index: usize,
) -> Result<(), MainProofRewriteLedgerMaterializerReject> {
    if value == 0 {
        return Err(MainProofRewriteLedgerMaterializerReject::ZeroId {
            field,
            sidecar_row_index,
        });
    }
    Ok(())
}

#[cfg_attr(not(test), allow(dead_code))]
fn push_required_source_bound_multiplier_row<'a>(
    transaction_id: u64,
    row: &SourceBoundMultiplierLratSidecarRow,
    proof_records: &'a [DecomposeProofEmitRecord],
) -> Result<&'a DecomposeProofEmitRecord, MainProofRewriteLedgerMaterializerReject> {
    validate_nonzero(
        "source_clause_id",
        row.source_clause_id,
        row.sidecar_row_index,
    )?;
    validate_nonzero(
        "checker_visible_id",
        row.checker_visible_id,
        row.sidecar_row_index,
    )?;
    let context = source_bound_multiplier_lrat_context(transaction_id, row);
    match row.row_kind.proof_out_kind() {
        DecomposeProofOutRecordKind::Add => {
            let Some(proof_record) = find_record(
                proof_records,
                &context,
                row.checker_visible_id,
                DecomposeProofOutRecordKind::Add,
            ) else {
                return Err(MainProofRewriteLedgerMaterializerReject::MissingAddRecord {
                    sidecar_row_index: row.sidecar_row_index,
                    checker_visible_id: row.checker_visible_id,
                });
            };
            validate_add_record(
                row.sidecar_row_index,
                proof_record,
                &row.clause_lits_dimacs,
                &row.lrat_hints,
            )?;
            Ok(proof_record)
        }
        DecomposeProofOutRecordKind::Delete => {
            let Some(delete_source_id) = row.delete_source_id else {
                return Err(MainProofRewriteLedgerMaterializerReject::ZeroId {
                    field: "delete_source_id",
                    sidecar_row_index: row.sidecar_row_index,
                });
            };
            validate_nonzero("delete_source_id", delete_source_id, row.sidecar_row_index)?;
            let Some(proof_record) = find_record(
                proof_records,
                &context,
                row.checker_visible_id,
                DecomposeProofOutRecordKind::Delete,
            ) else {
                return Err(
                    MainProofRewriteLedgerMaterializerReject::MissingDeleteRecord {
                        sidecar_row_index: row.sidecar_row_index,
                        delete_source_id,
                    },
                );
            };
            if proof_record.delete_source_id != Some(delete_source_id)
                || proof_record.proof_field != "deletion_proof_steps"
            {
                return Err(
                    MainProofRewriteLedgerMaterializerReject::MismatchedProofRecord {
                        sidecar_row_index: row.sidecar_row_index,
                        checker_visible_id: proof_record.checker_visible_id,
                    },
                );
            }
            validate_record_common(row.sidecar_row_index, proof_record)?;
            validate_record_payload(
                row.sidecar_row_index,
                proof_record,
                &row.clause_lits_dimacs,
                &[],
            )?;
            Ok(proof_record)
        }
    }
}

#[cfg_attr(not(test), allow(dead_code))]
fn first_source_bound_multiplier_identity(
    sidecars: &[SourceBoundMultiplierLratSidecarRow],
) -> (usize, u64) {
    sidecars
        .first()
        .map(|row| (row.sidecar_row_index, row.checker_visible_id))
        .unwrap_or((0, 0))
}

fn push_required_fmla_overlay_add_record(
    transaction_id: u64,
    sidecar_row_index: usize,
    direction: &'static str,
    row: &FmlaGuardedEquivOverlayLratBinaryRow,
    proof_records: &[DecomposeProofEmitRecord],
) -> Result<(), MainProofRewriteLedgerMaterializerReject> {
    validate_nonzero("checker_visible_id", row.planned_add_id, sidecar_row_index)?;
    let context = DecomposeProofEmitContext::from_fmla_guarded_equiv_overlay_binary(
        transaction_id,
        sidecar_row_index,
        direction,
        row,
    );
    let Some(proof_record) = find_record(
        proof_records,
        &context,
        row.planned_add_id,
        DecomposeProofOutRecordKind::Add,
    ) else {
        return Err(MainProofRewriteLedgerMaterializerReject::MissingAddRecord {
            sidecar_row_index,
            checker_visible_id: row.planned_add_id,
        });
    };
    validate_add_record(
        sidecar_row_index,
        proof_record,
        &row.clause_lits_dimacs,
        &row.lrat_hints,
    )
}

fn push_required_fmla_support_add_record(
    transaction_id: u64,
    sidecar_row_index: usize,
    row: &FmlaGuardedEquivSupportCoverLratSidecar,
    proof_records: &[DecomposeProofEmitRecord],
) -> Result<(), MainProofRewriteLedgerMaterializerReject> {
    validate_nonzero("checker_visible_id", row.planned_add_id, sidecar_row_index)?;
    let context = DecomposeProofEmitContext::from_fmla_guarded_equiv_support_cover(
        transaction_id,
        sidecar_row_index,
        row,
    );
    let Some(proof_record) = find_record(
        proof_records,
        &context,
        row.planned_add_id,
        DecomposeProofOutRecordKind::Add,
    ) else {
        return Err(MainProofRewriteLedgerMaterializerReject::MissingAddRecord {
            sidecar_row_index,
            checker_visible_id: row.planned_add_id,
        });
    };
    validate_add_record(
        sidecar_row_index,
        proof_record,
        &row.clause_lits_dimacs,
        &row.lrat_hints,
    )
}

fn first_fmla_add_record_identity(
    overlay_sidecars: &[FmlaGuardedEquivOverlayLratSidecar],
    support_sidecars: &[FmlaGuardedEquivSupportCoverLratSidecar],
) -> (usize, u64) {
    overlay_sidecars
        .first()
        .map(|sidecar| (0, sidecar.forward_binary.planned_add_id))
        .or_else(|| {
            support_sidecars
                .first()
                .map(|sidecar| (0, sidecar.planned_add_id))
        })
        .unwrap_or((0, 0))
}

fn push_required_add_record(
    records: &mut Vec<MainProofRewriteLedgerRecord>,
    sidecar: &DecomposeLratDryRunSidecar,
    context: &DecomposeProofEmitContext,
    proof_records: &[DecomposeProofEmitRecord],
    checker_visible_id: u64,
    expected_clause_lits_dimacs: &[i64],
    expected_lrat_hints: &[u64],
) -> Result<(), MainProofRewriteLedgerMaterializerReject> {
    validate_nonzero(
        "checker_visible_id",
        checker_visible_id,
        context.sidecar_row_index,
    )?;
    let Some(proof_record) = find_record(
        proof_records,
        context,
        checker_visible_id,
        DecomposeProofOutRecordKind::Add,
    ) else {
        return Err(MainProofRewriteLedgerMaterializerReject::MissingAddRecord {
            sidecar_row_index: context.sidecar_row_index,
            checker_visible_id,
        });
    };
    validate_add_record(
        context.sidecar_row_index,
        proof_record,
        expected_clause_lits_dimacs,
        expected_lrat_hints,
    )?;
    records.push(build_main_proof_record(sidecar, proof_record));
    Ok(())
}

fn push_required_delete_record(
    records: &mut Vec<MainProofRewriteLedgerRecord>,
    sidecar: &DecomposeLratDryRunSidecar,
    context: &DecomposeProofEmitContext,
    proof_records: &[DecomposeProofEmitRecord],
) -> Result<(), MainProofRewriteLedgerMaterializerReject> {
    let Some(proof_record) = find_record(
        proof_records,
        context,
        sidecar.source_delete_id,
        DecomposeProofOutRecordKind::Delete,
    ) else {
        return Err(
            MainProofRewriteLedgerMaterializerReject::MissingDeleteRecord {
                sidecar_row_index: context.sidecar_row_index,
                delete_source_id: sidecar.source_delete_id,
            },
        );
    };
    if proof_record.delete_source_id != Some(sidecar.source_delete_id)
        || proof_record.proof_field != "deletion_proof_steps"
    {
        return Err(
            MainProofRewriteLedgerMaterializerReject::MismatchedProofRecord {
                sidecar_row_index: context.sidecar_row_index,
                checker_visible_id: proof_record.checker_visible_id,
            },
        );
    }
    validate_record_common(context.sidecar_row_index, proof_record)?;
    validate_record_payload(
        context.sidecar_row_index,
        proof_record,
        &sidecar.source_clause_lits,
        &[],
    )?;
    records.push(build_main_proof_record(sidecar, proof_record));
    Ok(())
}

fn find_record<'a>(
    proof_records: &'a [DecomposeProofEmitRecord],
    context: &DecomposeProofEmitContext,
    checker_visible_id: u64,
    kind: DecomposeProofOutRecordKind,
) -> Option<&'a DecomposeProofEmitRecord> {
    proof_records.iter().find(|record| {
        record.context == *context
            && record.checker_visible_id == checker_visible_id
            && record.proof_out_record_kind == kind
    })
}

fn validate_add_record(
    sidecar_row_index: usize,
    proof_record: &DecomposeProofEmitRecord,
    expected_clause_lits_dimacs: &[i64],
    expected_lrat_hints: &[u64],
) -> Result<(), MainProofRewriteLedgerMaterializerReject> {
    if proof_record.delete_source_id.is_some()
        || proof_record.proof_field != "derived_clause_proof_steps"
    {
        return Err(
            MainProofRewriteLedgerMaterializerReject::MismatchedProofRecord {
                sidecar_row_index,
                checker_visible_id: proof_record.checker_visible_id,
            },
        );
    }
    validate_record_common(sidecar_row_index, proof_record)?;
    validate_record_payload(
        sidecar_row_index,
        proof_record,
        expected_clause_lits_dimacs,
        expected_lrat_hints,
    )
}

fn validate_record_common(
    sidecar_row_index: usize,
    proof_record: &DecomposeProofEmitRecord,
) -> Result<(), MainProofRewriteLedgerMaterializerReject> {
    validate_nonzero(
        "checker_visible_id",
        proof_record.checker_visible_id,
        sidecar_row_index,
    )?;
    if !proof_record.solver_runtime_emitted {
        return Err(
            MainProofRewriteLedgerMaterializerReject::RuntimeProofRecordNotEmitted {
                sidecar_row_index,
                checker_visible_id: proof_record.checker_visible_id,
            },
        );
    }
    if proof_record.proof_writer_io_error {
        return Err(
            MainProofRewriteLedgerMaterializerReject::ProofWriterIoError {
                sidecar_row_index,
                checker_visible_id: proof_record.checker_visible_id,
            },
        );
    }
    if proof_record.external_checker_verified {
        return Err(
            MainProofRewriteLedgerMaterializerReject::ExternalCheckerVerdictNotAccepted {
                sidecar_row_index,
                checker_visible_id: proof_record.checker_visible_id,
                reason: "proof_record_injected_external_checker_verdict",
            },
        );
    }
    Ok(())
}

fn validate_record_payload(
    sidecar_row_index: usize,
    proof_record: &DecomposeProofEmitRecord,
    expected_clause_lits_dimacs: &[i64],
    expected_lrat_hints: &[u64],
) -> Result<(), MainProofRewriteLedgerMaterializerReject> {
    if proof_record.proof_manager_mode != "lrat" {
        return Err(
            MainProofRewriteLedgerMaterializerReject::ProofRecordPayloadMismatch {
                sidecar_row_index,
                checker_visible_id: proof_record.checker_visible_id,
                field: "proof_manager_mode",
            },
        );
    }
    if proof_record.clause_lits_dimacs.as_slice() != expected_clause_lits_dimacs {
        return Err(
            MainProofRewriteLedgerMaterializerReject::ProofRecordPayloadMismatch {
                sidecar_row_index,
                checker_visible_id: proof_record.checker_visible_id,
                field: "clause_lits_dimacs",
            },
        );
    }
    if proof_record.lrat_hints.as_slice() != expected_lrat_hints {
        return Err(
            MainProofRewriteLedgerMaterializerReject::ProofRecordPayloadMismatch {
                sidecar_row_index,
                checker_visible_id: proof_record.checker_visible_id,
                field: "lrat_hints",
            },
        );
    }
    Ok(())
}

fn build_main_proof_record(
    sidecar: &DecomposeLratDryRunSidecar,
    proof_record: &DecomposeProofEmitRecord,
) -> MainProofRewriteLedgerRecord {
    MainProofRewriteLedgerRecord {
        runtime_decompose_transaction_id: proof_record.context.transaction_id,
        sidecar_context_token: proof_record.context.sidecar_context_token.clone(),
        sidecar_row_index: proof_record.context.sidecar_row_index,
        source_row_id: proof_record.context.source_row_id.clone(),
        obligation_id: proof_record.context.obligation_id.clone(),
        proof_field: proof_record.proof_field,
        proof_out_record_kind: proof_record.proof_out_record_kind,
        checker_visible_id: proof_record.checker_visible_id,
        delete_source_id: proof_record.delete_source_id,
        source_clause_id: sidecar.source_clause_id,
        source_clause_lits: sidecar.source_clause_lits.clone(),
        rewritten_clause_lits: sidecar.rewritten_clause_lits.clone(),
        clause_lits_dimacs: proof_record.clause_lits_dimacs.clone(),
        lrat_hints: proof_record.lrat_hints.clone(),
        proof_manager_mode: proof_record.proof_manager_mode,
        solver_runtime_emitted: proof_record.solver_runtime_emitted,
        proof_writer_io_error: proof_record.proof_writer_io_error,
        external_checker_verified: false,
        external_checker_verdict_artifact: None,
    }
}

fn first_record_identity(records: &[MainProofRewriteLedgerRecord]) -> (usize, u64) {
    records
        .first()
        .map(|record| (record.sidecar_row_index, record.checker_visible_id))
        .unwrap_or((0, 0))
}

pub(crate) fn validate_external_checker_verdict_artifact(
    artifact: &ExternalProofCheckerVerdictArtifactRef,
) -> Result<(), &'static str> {
    if artifact.schema != FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_SCHEMA {
        return Err("external_checker_verdict_schema_mismatch");
    }
    if artifact.runtime_field != FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.runtime_field {
        return Err("external_checker_verdict_runtime_field_mismatch");
    }
    if artifact.verdict != FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.accepted_verdict {
        return Err("external_checker_verdict_not_verified_unsat");
    }
    if path_file_name(&artifact.artifact_path)
        != Some(FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.artifact_file_name)
    {
        return Err("external_checker_verdict_artifact_path_mismatch");
    }
    if artifact.checker_exit_code
        != FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.checker_exit_code
    {
        return Err("external_checker_verdict_nonzero_exit_code");
    }
    if path_file_name(&artifact.proof_out_path)
        != Some(FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.proof_out_file_name)
    {
        return Err("proof_out_path_not_wrapper_proof_out");
    }
    if !artifact
        .checker_command
        .contains(artifact.checked_dimacs_path.as_str())
    {
        return Err("checker_command_missing_checked_dimacs_path");
    }
    if !artifact
        .checker_command
        .contains(artifact.proof_out_path.as_str())
    {
        return Err("checker_command_missing_proof_out_path");
    }
    let expected_argv = [
        artifact.checker_path.as_str(),
        artifact.checked_dimacs_path.as_str(),
        artifact.proof_out_path.as_str(),
    ];
    if artifact.checker_argv.len() != expected_argv.len() {
        return Err("checker_argv_shape_mismatch");
    }
    for (observed, expected) in artifact.checker_argv.iter().zip(expected_argv) {
        if observed != expected {
            return Err("checker_argv_not_bound_to_checked_inputs");
        }
    }
    for (field, value) in [
        ("artifact_path", artifact.artifact_path.as_str()),
        ("checker_path", artifact.checker_path.as_str()),
        ("checker_command", artifact.checker_command.as_str()),
        ("proof_out_path", artifact.proof_out_path.as_str()),
        ("checked_dimacs_path", artifact.checked_dimacs_path.as_str()),
    ] {
        if value.is_empty() {
            return Err(field);
        }
    }
    for (field, value) in [
        ("artifact_sha256", artifact.artifact_sha256.as_str()),
        ("checker_sha256", artifact.checker_sha256.as_str()),
        ("proof_out_sha256", artifact.proof_out_sha256.as_str()),
        (
            "checked_dimacs_sha256",
            artifact.checked_dimacs_sha256.as_str(),
        ),
    ] {
        if !is_sha256_hex(value) {
            return Err(field);
        }
    }
    Ok(())
}

pub(crate) fn validate_external_checker_verdict_artifact_file(
    artifact: &ExternalProofCheckerVerdictArtifactRef,
) -> Result<(), &'static str> {
    validate_external_checker_verdict_artifact(artifact)?;
    let bytes = std::fs::read(&artifact.artifact_path)
        .map_err(|_| "external_checker_verdict_artifact_missing")?;
    if sha256_hex(&bytes) != artifact.artifact_sha256 {
        return Err("external_checker_verdict_artifact_sha256_mismatch");
    }
    Ok(())
}

fn path_file_name(value: &str) -> Option<&str> {
    value.rsplit(['/', '\\']).find(|part| !part.is_empty())
}

fn is_sha256_hex(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write as _;
        let _ = write!(&mut hex, "{byte:02x}");
    }
    hex
}

/// Default-off in-memory ledger for Fmla runtime record scaffolding.
#[derive(Debug, Default)]
pub struct FmlaRuntimeLedger {
    capture_enabled: bool,
    next_transaction_id: u64,
    records: Vec<FmlaRuntimeLedgerRecord>,
    last_transaction: Option<FmlaRuntimeTransactionCapture>,
    stats: FmlaRuntimeLedgerStats,
}

impl FmlaRuntimeLedger {
    /// Construct a disabled ledger. This is the default behavior.
    #[must_use]
    pub fn disabled() -> Self {
        Self::default()
    }

    /// Construct an explicit capture-only ledger for tests and reports.
    #[must_use]
    pub fn capture_only() -> Self {
        let mut ledger = Self {
            capture_enabled: true,
            ..Self::default()
        };
        ledger.stats.capture_enabled = true;
        ledger
    }

    /// Capture one representative guarded-equivalence transaction if enabled.
    ///
    /// The capture reads source clauses and emits six closed records. It never
    /// mutates clauses, writes proofs, reconstructs a model, or enables a route.
    pub fn capture_representative_guarded_equivalence(
        &mut self,
        clauses: &[Vec<Literal>],
    ) -> Option<&FmlaRuntimeTransactionCapture> {
        if !self.capture_enabled {
            return None;
        }

        let witnesses = FmlaGuardedEquivWitnesses::scan(clauses, 1);
        let equivalence = witnesses.guarded_equivalences.first()?.clone();
        let guard_group = witnesses.guard_group_for(equivalence.guard)?.clone();
        let transaction_id = self.next_transaction_id;
        self.next_transaction_id = self.next_transaction_id.saturating_add(1);

        let replay_dependencies = replay_dependencies(&guard_group, &equivalence);
        let mut transaction = FmlaRuntimeTransactionCapture {
            transaction_id,
            mutation_epoch: transaction_id.saturating_add(1),
            pre_mutation_clause_epoch: 0,
            removed_original_var: equivalence.lhs,
            retained_original_var: equivalence.rhs,
            model_reconstruction_stack_index: transaction_id as usize,
            guard_group,
            guarded_equivalence: equivalence,
            replay_dependencies,
            witness_checker_failures: Vec::new(),
        };
        transaction.witness_checker_failures = check_transaction_witness(&transaction);

        self.records.extend(build_closed_records(&transaction));
        self.last_transaction = Some(transaction);
        self.refresh_stats();
        self.last_transaction.as_ref()
    }

    /// Runtime records emitted by the ledger.
    #[must_use]
    pub fn records(&self) -> &[FmlaRuntimeLedgerRecord] {
        &self.records
    }

    /// Last captured representative transaction, if any.
    #[must_use]
    pub fn last_transaction(&self) -> Option<&FmlaRuntimeTransactionCapture> {
        self.last_transaction.as_ref()
    }

    /// Aggregate scaffold counters.
    #[must_use]
    pub fn stats(&self) -> FmlaRuntimeLedgerStats {
        self.stats
    }

    /// Distinct represented W83 field names and their representation counts.
    #[must_use]
    pub fn represented_field_counts(&self) -> BTreeMap<&'static str, usize> {
        let mut counts = BTreeMap::new();
        for record in &self.records {
            for field in &record.fields {
                *counts.entry(field.name).or_insert(0) += 1;
            }
        }
        counts
    }

    fn refresh_stats(&mut self) {
        let counts = self.represented_field_counts();
        let runtime_required_fields_represented = W83_RUNTIME_REQUIRED_FIELDS
            .iter()
            .filter(|field| counts.get(**field) == Some(&1))
            .count() as u64;
        let duplicate_represented_fields = W83_RUNTIME_REQUIRED_FIELDS
            .iter()
            .filter(|field| counts.get(**field).copied().unwrap_or_default() > 1)
            .count() as u64;
        let witness_failed = self
            .last_transaction
            .as_ref()
            .is_some_and(|tx| !tx.witness_checker_failures.is_empty());
        self.stats = FmlaRuntimeLedgerStats {
            capture_enabled: self.capture_enabled,
            records_emitted: self.records.len() as u64,
            record_groups_emitted: self.records.len() as u64,
            runtime_required_fields_represented,
            duplicate_represented_fields,
            witness_checker_passed: u64::from(self.last_transaction.is_some() && !witness_failed),
            witness_checker_failed: u64::from(witness_failed),
            model_reconstruction_ready: false,
            proof_obligation_ready: false,
            destructive_transform_allowed: false,
            wrong_count: 0,
            invalid_count: 0,
        };
    }
}

fn replay_dependencies(
    guard_group: &FmlaOneHotGroupWitness,
    equivalence: &FmlaGuardedEquivalenceWitness,
) -> FmlaRuntimeReplayDependencies {
    let mut guard_lhs_rhs = BTreeMap::new();
    guard_lhs_rhs.insert("guard", equivalence.guard);
    guard_lhs_rhs.insert("lhs", equivalence.lhs);
    guard_lhs_rhs.insert("rhs", equivalence.rhs);

    let mut source_clause_ids = Vec::with_capacity(3 + guard_group.mutex_clause_ids.len());
    source_clause_ids.push(guard_group.support_clause_id);
    source_clause_ids.extend(guard_group.mutex_clause_ids.iter().copied());
    source_clause_ids.push(equivalence.forward_clause_id);
    source_clause_ids.push(equivalence.reverse_clause_id);

    FmlaRuntimeReplayDependencies {
        guard_lhs_rhs,
        source_clause_ids,
    }
}

fn build_closed_records(
    transaction: &FmlaRuntimeTransactionCapture,
) -> Vec<FmlaRuntimeLedgerRecord> {
    vec![
        record(
            transaction.transaction_id,
            &W83_RUNTIME_RECORD_GROUPS[0],
            &[
                captured("mutation_epoch", "capture-only monotonic scaffold epoch"),
                captured(
                    "pre_mutation_clause_epoch",
                    "observed before any destructive clause mutation",
                ),
                captured(
                    "removed_original_var",
                    "candidate removed endpoint variable",
                ),
                captured(
                    "retained_original_var",
                    "candidate retained endpoint variable",
                ),
            ],
        ),
        record(
            transaction.transaction_id,
            &W83_RUNTIME_RECORD_GROUPS[1],
            &[
                blocked(
                    "inactive_guard_fallback_assignment",
                    "blocked until a final SAT model assignment exists",
                ),
                captured(
                    "model_reconstruction_stack_index",
                    "capture-only stack slot reserved without model replay",
                ),
            ],
        ),
        record(
            transaction.transaction_id,
            &W83_RUNTIME_RECORD_GROUPS[2],
            &[
                blocked(
                    "reconstructed_model_checker_command",
                    "blocked until a reconstructed original-DIMACS model is emitted",
                ),
                blocked(
                    "reconstructed_model_checker_verdict_artifact",
                    "blocked until model checker output is retained",
                ),
            ],
        ),
        record(
            transaction.transaction_id,
            &W83_RUNTIME_RECORD_GROUPS[3],
            &[
                blocked(
                    "proof_manager_mode",
                    "blocked until Main proof mode is active",
                ),
                blocked(
                    "source_proof_ids",
                    "blocked until checker-visible source proof ids are assigned",
                ),
                blocked(
                    "derived_clause_proof_steps",
                    "blocked until rewrite derivation proof steps exist",
                ),
                blocked(
                    "deletion_proof_steps",
                    "blocked until source deletion proof steps exist",
                ),
                blocked(
                    "runtime_decompose_transaction_id",
                    "blocked until a decompose sidecar proof context is observed",
                ),
                blocked(
                    "sidecar_context_token",
                    "blocked until decompose sidecar rows are bound to proof writes",
                ),
                blocked(
                    "sidecar_row_index",
                    "blocked until a retained sidecar row is selected",
                ),
                blocked(
                    "source_row_id",
                    "blocked until a retained sidecar source row is selected",
                ),
                blocked(
                    "obligation_id",
                    "blocked until a decompose proof obligation row is selected",
                ),
                blocked(
                    "checker_visible_id",
                    "blocked until ProofManager returns a checker-visible id",
                ),
                blocked(
                    "proof_writer_io_error",
                    "blocked until a scoped proof write is attempted",
                ),
                blocked(
                    "external_checker_verified",
                    "blocked until proof.out is externally accepted",
                ),
            ],
        ),
        record(
            transaction.transaction_id,
            &W83_RUNTIME_RECORD_GROUPS[4],
            &[
                blocked(
                    "external_proof_checker_command",
                    "blocked until an UNSAT proof.out artifact is emitted",
                ),
                blocked(
                    "external_proof_checker_verdict_artifact",
                    "blocked until external proof-check acceptance is retained",
                ),
            ],
        ),
        record(
            transaction.transaction_id,
            &W83_RUNTIME_RECORD_GROUPS[5],
            &[
                captured("wrong_count_zero", "scaffold records no wrong-answer claim"),
                captured(
                    "invalid_count_zero",
                    "scaffold records no invalid-result claim",
                ),
            ],
        ),
    ]
}

fn record(
    transaction_id: u64,
    definition: &FmlaRuntimeRecordGroupDefinition,
    fields: &[FmlaRuntimeLedgerField],
) -> FmlaRuntimeLedgerRecord {
    FmlaRuntimeLedgerRecord {
        transaction_id,
        record_group_id: definition.record_group_id,
        runtime_record: definition.runtime_record,
        fields: fields.to_vec(),
        gate_open: false,
    }
}

fn captured(name: &'static str, detail: &'static str) -> FmlaRuntimeLedgerField {
    FmlaRuntimeLedgerField {
        name,
        status: FmlaRuntimeFieldStatus::Captured,
        detail,
    }
}

fn blocked(name: &'static str, detail: &'static str) -> FmlaRuntimeLedgerField {
    FmlaRuntimeLedgerField {
        name,
        status: FmlaRuntimeFieldStatus::Blocked,
        detail,
    }
}

fn check_transaction_witness(transaction: &FmlaRuntimeTransactionCapture) -> Vec<String> {
    let mut failures = Vec::new();
    let group = &transaction.guard_group;
    let equivalence = &transaction.guarded_equivalence;
    if !group.vars.contains(&equivalence.guard) {
        failures.push("guard variable is not covered by the sampled one-hot group".to_string());
    }
    if group.vars.len() < 2 {
        failures.push("one-hot group has fewer than two variables".to_string());
    }
    let expected_mutexes = group
        .vars
        .len()
        .saturating_mul(group.vars.len().saturating_sub(1))
        / 2;
    if group.mutex_clause_ids.len() != expected_mutexes {
        failures.push(format!(
            "one-hot mutex witness count {} != expected {}",
            group.mutex_clause_ids.len(),
            expected_mutexes
        ));
    }
    if equivalence.guard <= 0 || equivalence.lhs <= 0 || equivalence.rhs <= 0 {
        failures.push("guard/lhs/rhs must be positive DIMACS variables".to_string());
    }
    if equivalence.lhs == equivalence.rhs {
        failures.push("lhs and rhs must be distinct".to_string());
    }
    let expected_forward = [-equivalence.guard, -equivalence.lhs, equivalence.rhs];
    if !same_clause_lits(&equivalence.forward_clause_lits, &expected_forward) {
        failures.push(format!(
            "forward clause {:?} is not a permutation of expected {:?}",
            equivalence.forward_clause_lits, expected_forward
        ));
    }
    let expected_reverse = [-equivalence.guard, -equivalence.rhs, equivalence.lhs];
    if !same_clause_lits(&equivalence.reverse_clause_lits, &expected_reverse) {
        failures.push(format!(
            "reverse clause {:?} is not a permutation of expected {:?}",
            equivalence.reverse_clause_lits, expected_reverse
        ));
    }
    if transaction
        .replay_dependencies
        .source_clause_ids
        .contains(&0)
    {
        failures.push("replay dependencies contain a zero clause id".to_string());
    }
    failures
}

fn same_clause_lits(actual: &[i32], expected: &[i32]) -> bool {
    if actual.len() != expected.len() {
        return false;
    }
    let mut actual = actual.to_vec();
    let mut expected = expected.to_vec();
    actual.sort_unstable();
    expected.sort_unstable();
    actual == expected
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Variable;
    use crate::parse_dimacs;
    use std::path::Path;

    fn pos(var: usize) -> Literal {
        Literal::positive(Variable(var as u32))
    }

    fn neg(var: usize) -> Literal {
        Literal::negative(Variable(var as u32))
    }

    fn guarded_fixture() -> Vec<Vec<Literal>> {
        let mut clauses = vec![(0..6).map(pos).collect()];
        for lhs in 0..6 {
            for rhs in (lhs + 1)..6 {
                clauses.push(vec![neg(lhs), neg(rhs)]);
            }
        }
        clauses.push(vec![neg(0), neg(6), pos(7)]);
        clauses.push(vec![neg(0), neg(7), pos(6)]);
        clauses
    }

    #[test]
    fn default_ledger_is_disabled_and_emits_no_records() {
        let mut ledger = FmlaRuntimeLedger::disabled();

        assert!(ledger
            .capture_representative_guarded_equivalence(&guarded_fixture())
            .is_none());

        let stats = ledger.stats();
        assert!(!stats.capture_enabled);
        assert_eq!(stats.records_emitted, 0);
        assert_eq!(stats.runtime_required_fields_represented, 0);
        assert!(!stats.model_reconstruction_ready);
        assert!(!stats.proof_obligation_ready);
        assert!(!stats.destructive_transform_allowed);
    }

    #[test]
    fn capture_only_ledger_emits_closed_w83_records() {
        let mut ledger = FmlaRuntimeLedger::capture_only();

        let transaction = ledger
            .capture_representative_guarded_equivalence(&guarded_fixture())
            .expect("capture-only fixture transaction");

        assert_eq!(transaction.guarded_equivalence.guard, 1);
        assert_eq!(transaction.guarded_equivalence.lhs, 7);
        assert_eq!(transaction.guarded_equivalence.rhs, 8);
        assert_eq!(transaction.removed_original_var, 7);
        assert_eq!(transaction.retained_original_var, 8);
        assert_eq!(transaction.witness_checker_failures, Vec::<String>::new());
        assert_eq!(
            transaction.replay_dependencies.guard_lhs_rhs.get("guard"),
            Some(&1)
        );

        assert_eq!(ledger.records().len(), 6);
        assert!(ledger.records().iter().all(|record| !record.gate_open));
        let stats = ledger.stats();
        assert!(stats.capture_enabled);
        assert_eq!(stats.records_emitted, 6);
        assert_eq!(stats.record_groups_emitted, 6);
        assert_eq!(stats.runtime_required_fields_represented, 16);
        assert_eq!(stats.duplicate_represented_fields, 0);
        assert_eq!(stats.witness_checker_passed, 1);
        assert_eq!(stats.witness_checker_failed, 0);
        assert!(!stats.model_reconstruction_ready);
        assert!(!stats.proof_obligation_ready);
        assert!(!stats.destructive_transform_allowed);
        assert_eq!(stats.wrong_count, 0);
        assert_eq!(stats.invalid_count, 0);
    }

    #[test]
    fn fmla_capture_locks_w78_sample_but_keeps_gates_closed() {
        let Some(formula) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf.xz",
        ) else {
            return;
        };
        let mut ledger = FmlaRuntimeLedger::capture_only();

        let transaction = ledger
            .capture_representative_guarded_equivalence(&formula.clauses)
            .expect("capture Fmla representative transaction");

        assert_eq!(transaction.guard_group.support_clause_id, 2_593);
        assert_eq!(transaction.guarded_equivalence.guard, 27_217);
        assert_eq!(transaction.guarded_equivalence.lhs, 3_889);
        assert_eq!(transaction.guarded_equivalence.rhs, 5_185);
        assert_eq!(transaction.guarded_equivalence.forward_clause_id, 173_569);
        assert_eq!(transaction.guarded_equivalence.reverse_clause_id, 173_570);
        assert_eq!(
            transaction.guarded_equivalence.forward_clause_lits,
            vec![-27_217, -3_889, 5_185]
        );
        assert_eq!(
            transaction.guarded_equivalence.reverse_clause_lits,
            vec![-27_217, -5_185, 3_889]
        );
        assert!(transaction.witness_checker_failures.is_empty());

        let stats = ledger.stats();
        assert_eq!(stats.records_emitted, 6);
        assert_eq!(stats.runtime_required_fields_represented, 16);
        assert_eq!(stats.duplicate_represented_fields, 0);
        assert_eq!(stats.witness_checker_passed, 1);
        assert!(!stats.model_reconstruction_ready);
        assert!(!stats.proof_obligation_ready);
        assert!(!stats.destructive_transform_allowed);
    }

    fn parse_optional_xz_fixture(relative_path: &str) -> Option<crate::DimacsFormula> {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(relative_path);
        if !path.exists() {
            eprintln!("Fmla runtime ledger fixture missing: {}", path.display());
            return None;
        }
        let content = String::from_utf8(crate::test_xz::decompress_xz_path(&path)?)
            .expect("fixture is UTF-8 DIMACS");
        Some(parse_dimacs(&content).expect("parse DIMACS fixture"))
    }
}
