// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mediator for SAT proof emission and validation.
//!
//! All DRAT/LRAT writes are routed through `ProofManager` so callsites do not
//! manipulate `ProofOutput` directly. In LRAT mode this centralizes hint-ID
//! validation. In debug builds it also wires the online forward checker and
//! the LRAT chain verifier.

use crate::decompose::{
    DecomposeProofEmitContext, DecomposeProofEmitRecord, DecomposeProofOutRecordKind,
};
use crate::fmla_runtime_ledger::{
    validate_external_checker_verdict_artifact, validate_external_checker_verdict_artifact_file,
    ExternalProofCheckerVerdictArtifactRef, FmlaPostCheckAdmissionReplayRecord,
    FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA,
};
#[cfg(debug_assertions)]
use crate::forward_checker::ForwardChecker;
use crate::kani_compat::{det_hash_set_new, det_hash_set_with_capacity, DetHashSet};
#[cfg(debug_assertions)]
use crate::lrat_checker::LratChecker;
use crate::proof::ProofOutput;
use crate::Literal;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fmt::Write as _;
use std::io;

mod live_id_set;
use live_id_set::LiveIdSet;

#[cfg(test)]
mod tests;

pub(crate) const LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_REQUIRED: &str =
    "external_checker_required";
pub(crate) const LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_VERIFIED: &str =
    "external_checker_verified";
pub(crate) const LEARNED_LRAT_AUTHORITY_FAIL_CLOSED: &str = "fail_closed";
pub(crate) const LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA: &str =
    "ay.fmla-learned-lrat-dry-run-proof-artifact/v1";
const LEARNED_LRAT_DRY_RUN_MAX_FAIL_CLOSED_MATERIALIZER_ROWS: usize = 1024;

/// Classification for emitted proof additions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ProofAddKind {
    /// Derived clause that should be RUP-checkable under current state.
    Derived,
    /// Trusted axiom step (for example, a theory lemma) that bypasses RUP check.
    Axiom,
    /// Trusted inprocessing transform that bypasses the full RUP check but
    /// still runs the forward checker's consistency verification (#4609).
    ///
    /// Unlike `Axiom` (which adds to the checker as original with no validation),
    /// `TrustedTransform` verifies the clause is well-formed: non-empty,
    /// non-tautological, and not already falsified under the current assignment.
    /// This catches the most common inprocessing bugs (emitting a clause that
    /// is immediately falsified) without requiring full RUP derivability.
    TrustedTransform,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PlannedForwardAddReject {
    NotLrat,
    LratBlocked,
    IoFailed,
    PendingDeletions,
    OutputIdMismatch,
    InvalidClause,
    SuppressedAxiom,
    UnverifiedTrustedTransform,
    DerivedMissingHints,
    ZeroHint,
    DuplicateHint,
    UnknownHint,
    TrustedHint,
    BackwardReservedHint,
    IdOverflow,
}

/// Scalar summary of the most recent proof addition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LastAdd {
    id: u64,
    len: usize,
    is_empty: bool,
}

impl LastAdd {
    #[inline]
    fn new(id: u64, clause: &[Literal]) -> Self {
        Self {
            id,
            len: clause.len(),
            is_empty: clause.is_empty(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LearnedLratAuthorityStatus {
    FailClosedMaterializer,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LearnedLratAuthorityRecord {
    pub checker_visible_id: u64,
    pub clause_lits_dimacs: Vec<i64>,
    pub raw_resolution_chain: Vec<u64>,
    pub lrat_hints: Vec<u64>,
    pub materializer_dependency_ids: Vec<u64>,
    pub source_clause_dependency_ids: Vec<u64>,
    pub proof_manager_mode: &'static str,
    pub proof_out_emitted: bool,
    pub proof_writer_io_error: bool,
    pub authority_status: LearnedLratAuthorityStatus,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LearnedLratMaterializationStatus {
    RetainedDependenciesComplete,
    FailClosedNoLearnedLratAuthorityRecords,
    FailClosedMissingMaterializerDependency,
    FailClosedIncompleteLearnedDependency,
    FailClosedIncompleteMaterializerDependency,
    FailClosedMalformedReplayRows,
    FailClosedProofWriterIoError,
    FailClosedProofOutAlreadyEmitted,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LearnedLratMaterializerDependencyExport {
    pub context: DecomposeProofEmitContext,
    pub checker_visible_id: u64,
    pub clause_lits_dimacs: Vec<i64>,
    pub checker_visible_lrat_hints: Vec<u64>,
    pub solver_runtime_emitted: bool,
    pub proof_writer_io_error: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LearnedLratMaterializationExport {
    pub checker_visible_id: u64,
    pub clause_lits_dimacs: Vec<i64>,
    pub raw_resolution_chain: Vec<u64>,
    pub checker_visible_lrat_hints: Vec<u64>,
    pub materializer_rows: Vec<LearnedLratMaterializerDependencyExport>,
    pub proof_out_emitted: bool,
    pub proof_writer_io_error: bool,
    pub authority_status: LearnedLratAuthorityStatus,
    pub materialization_status: LearnedLratMaterializationStatus,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LearnedLratReplayRowKind {
    MaterializerAdd,
    LearnedAdd,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LearnedLratReplayRow {
    pub kind: LearnedLratReplayRowKind,
    pub checker_visible_id: u64,
    pub clause_lits_dimacs: Vec<i64>,
    pub checker_visible_lrat_hints: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LearnedLratMaterializationReplay {
    pub checker_visible_id: u64,
    pub materialization_status: LearnedLratMaterializationStatus,
    pub rows: Vec<LearnedLratReplayRow>,
    pub proof_out_emitted: bool,
    pub proof_writer_io_error: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LearnedLratDryRunProofRow {
    pub kind: LearnedLratReplayRowKind,
    pub checker_visible_id: u64,
    pub clause_lits_dimacs: Vec<i64>,
    pub checker_visible_lrat_hints: Vec<u64>,
    pub lrat_line: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LearnedLratDryRunProofArtifact {
    pub checker_visible_id: u64,
    pub materialization_status: LearnedLratMaterializationStatus,
    pub rows: Vec<LearnedLratDryRunProofRow>,
    pub lrat_fragment: String,
    pub proof_out_emitted: bool,
    pub proof_writer_io_error: bool,
    pub external_checker_required: bool,
    pub external_checker_verified: bool,
    pub main_proof_authority_reason: &'static str,
    pub authorizes_main_proof_out: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LearnedLratDryRunProofArtifactEnvelope {
    pub schema: String,
    pub checker_visible_id: u64,
    pub materialization_status: LearnedLratMaterializationStatus,
    pub rows: Vec<LearnedLratDryRunProofRow>,
    pub lrat_fragment: String,
    pub lrat_fragment_sha256: String,
    pub proof_out_emitted: bool,
    pub proof_writer_io_error: bool,
    pub external_checker_required: bool,
    pub external_checker_verified: bool,
    pub main_proof_authority_reason: String,
    pub authorizes_main_proof_out: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum LearnedLratDryRunProofArtifactImportReject {
    MissingField(&'static str),
    InvalidField(&'static str),
    SchemaMismatch { observed: String },
    LratFragmentSha256Mismatch,
    LratFragmentRowsMismatch,
    InvalidAuthorityState,
    InvalidAuthorityReason { observed: String },
    ReplayRowsMalformed,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LearnedLratMainProofAuthorityArtifact {
    pub checker_visible_id: u64,
    pub materialization_status: LearnedLratMaterializationStatus,
    pub proof_out_path: String,
    pub proof_out_sha256: String,
    pub external_checker_verified: bool,
    pub proof_out_contains_lrat_fragment: bool,
    pub main_proof_authority_reason: &'static str,
    pub authorizes_main_proof_out: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum LearnedLratMainProofAuthorityReject {
    DryRunNotComplete {
        materialization_status: LearnedLratMaterializationStatus,
    },
    DryRunFragmentMissing,
    DryRunInvalidAuthorityState,
    ExternalCheckerVerdictNotAccepted {
        reason: &'static str,
    },
    ProofOutSha256Mismatch,
    ProofOutNotUtf8,
    ProofOutMissingDryRunFragment,
    PostCheckReplayNotCommitted {
        schema: &'static str,
        status: &'static str,
    },
    PostCheckReplayMissingProofRows,
    PostCheckReplayCheckerRowMismatch {
        proof_obligation_rows: u64,
        external_checker_verdict_artifact_rows: u64,
    },
    ProofOutPathMismatch {
        retained_proof_out_path: String,
        checker_proof_out_path: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum LearnedLratProofOutAppendReject {
    NotLrat,
    NoCompleteDryRun,
    DryRunInvalidAuthorityState,
    ReplayRowsMalformed,
    ReplayNotCommitted,
    ReplayRowsMismatch,
    ReplayNotAuthorized,
    ProofOutPathMismatch {
        retained_proof_out_path: String,
        checker_proof_out_path: String,
    },
    ExternalCheckerVerdictNotAccepted {
        reason: &'static str,
    },
    InvalidLiteral,
    MaterializerRowNotLive {
        checker_visible_id: u64,
    },
    LearnedRowNotReserved {
        checker_visible_id: u64,
    },
    PlannedAddRejected(PlannedForwardAddReject),
    ProofWriterIoError,
    NoLearnedRows,
}

/// Single mediator for SAT proof emission.
pub(crate) struct ProofManager {
    output: ProofOutput,
    lrat_mode: bool,
    /// Default-off scoped observer rows for decompose proof-emission experiments.
    scoped_decompose_proof_emit_records: Vec<DecomposeProofEmitRecord>,
    /// Observational learned-clause LRAT authority records for Fmla fail-closed routes.
    learned_lrat_authority_records: Vec<LearnedLratAuthorityRecord>,
    /// Fail-close guard: once theory lemmas are seen in SMT mode, do not emit
    /// LRAT additions/deletions because they are not SAT-resolution derivations.
    lrat_blocked_by_theory_lemmas: bool,
    /// LRAT IDs known to the mediator (original + emitted additions).
    /// Always-on in LRAT mode: enables structural chain integrity checks
    /// in all builds (#5005). Empty in DRAT mode.
    ///
    /// Uses a presence bitmap (`LiveIdSet`) rather than `HashSet<u64>`:
    /// LRAT IDs are monotonically issued so a 1-bit-per-slot
    /// representation delivers ~64× memory reduction on long proofs
    /// without any change to LRAT file output bytes (#8599).
    known_lrat_ids: LiveIdSet,
    /// Count of proof-visible LRAT IDs removed from `known_lrat_ids` since
    /// the previous shrink. This gates expensive bitmap rebuilds after
    /// reductions that did not actually delete proof-visible IDs.
    known_lrat_ids_deleted_since_shrink: usize,
    /// LRAT IDs for TrustedTransform clauses that are NOT written to the
    /// LRAT proof file (#6270). These IDs are reserved in the ID space
    /// (known to the solver) but invisible to external checkers. Downstream
    /// hint chains must filter out these IDs before writing to the LRAT file.
    trusted_lrat_ids: DetHashSet<u64>,
    /// LRAT IDs reserved for backward reconstruction (#8448).
    ///
    /// Populated by `reserve_lrat_id_for_backward` (learned clauses in LRAT
    /// backward mode). IDs in this set have NO proof line written during
    /// solving -- `emit_backward_step` writes them post-UNSAT and removes
    /// each successfully emitted ID. During backward emission, remaining IDs
    /// are still pending and must not appear in file-visible hint chains.
    ///
    /// IDs NOT in this set (e.g., BVE resolvents emitted via `emit_add`)
    /// already have proof lines and must NOT be re-emitted by backward
    /// reconstruction. `emit_backward_step` checks this set and skips
    /// IDs that were forward-emitted.
    ///
    /// Uses `LiveIdSet` (bitmap) rather than `HashSet<u64>` for the same
    /// memory-density reasons as `known_lrat_ids` (#8599).
    backward_reserved_ids: LiveIdSet,
    /// Reusable buffer for LRAT hint chains after file-output filtering.
    file_hints_buf: Vec<u64>,
    /// Reusable set for first-occurrence LRAT hint deduplication.
    file_hints_seen: DetHashSet<u64>,
    /// Next LRAT ID expected from the writer.
    /// Always-on in LRAT mode for hint validation (#5005).
    next_lrat_id: u64,
    #[cfg(debug_assertions)]
    checker: ForwardChecker,
    /// Online LRAT chain verifier (debug-only, active only in LRAT mode).
    #[cfg(debug_assertions)]
    lrat_checker: Option<LratChecker>,
    /// Buffer for original clauses awaiting their LRAT clause ID.
    /// The solver calls `register_original_clause` before `register_clause_id`
    /// for original clauses. Learned clauses skip `register_original_clause`,
    /// so only original clauses produce pending entries.
    #[cfg(debug_assertions)]
    pending_originals: Vec<Vec<Literal>>,
    /// Last emitted addition metadata for UNSAT finalization checks (#4561).
    last_add: Option<LastAdd>,
    /// Fail-close latch for LRAT structural proof gaps. This is separate from
    /// writer I/O failures, but finalization treats both as proof failure.
    lrat_structural_failure: bool,
    /// Fail-close latch for proof-authority gaps that must downgrade UNSAT at
    /// finalization without tripping mid-solve proof I/O boundary asserts.
    lrat_authority_fail_closed: bool,
    /// Debug: track IDs that have been deleted from known_lrat_ids, to
    /// distinguish "never registered" from "already deleted" on panic.
    #[cfg(debug_assertions)]
    deleted_lrat_ids: DetHashSet<u64>,
}

impl ProofManager {
    /// Build a new proof manager around an existing proof output.
    pub(crate) fn new(output: ProofOutput, num_vars: usize) -> Self {
        let lrat_mode = matches!(&output, ProofOutput::Lrat(_));
        let _ = &num_vars;
        let next_lrat_id = match &output {
            ProofOutput::Drat(_) => 1,
            ProofOutput::Lrat(writer) => writer.next_id(),
        };

        Self {
            output,
            lrat_mode,
            scoped_decompose_proof_emit_records: Vec::new(),
            learned_lrat_authority_records: Vec::new(),
            lrat_blocked_by_theory_lemmas: false,
            known_lrat_ids: LiveIdSet::new(),
            known_lrat_ids_deleted_since_shrink: 0,
            trusted_lrat_ids: det_hash_set_new(),
            backward_reserved_ids: LiveIdSet::new(),
            file_hints_buf: Vec::new(),
            file_hints_seen: det_hash_set_new(),
            next_lrat_id,
            #[cfg(debug_assertions)]
            checker: ForwardChecker::new(num_vars),
            #[cfg(debug_assertions)]
            lrat_checker: if lrat_mode {
                Some(LratChecker::new(num_vars))
            } else {
                None
            },
            #[cfg(debug_assertions)]
            pending_originals: Vec::new(),
            last_add: None,
            lrat_structural_failure: false,
            lrat_authority_fail_closed: false,
            #[cfg(debug_assertions)]
            deleted_lrat_ids: det_hash_set_new(),
        }
    }

    #[inline]
    pub(crate) fn is_lrat(&self) -> bool {
        self.lrat_mode
    }

    #[inline]
    pub(crate) fn lrat_id_visible_in_file(&self, clause_id: u64) -> bool {
        self.lrat_id_usable_as_hint(clause_id)
    }

    #[inline]
    pub(crate) fn lrat_id_usable_as_hint(&self, clause_id: u64) -> bool {
        if clause_id == 0 {
            return false;
        }
        !self.lrat_mode
            || (self.known_lrat_ids.contains(clause_id)
                && !self.trusted_lrat_ids.contains(&clause_id)
                && !self.backward_reserved_ids.contains(clause_id))
    }

    #[inline]
    pub(crate) fn block_lrat_for_theory_lemmas(&mut self) {
        if self.lrat_mode {
            self.lrat_blocked_by_theory_lemmas = true;
        }
    }

    #[inline]
    pub(crate) fn lrat_blocked_by_theory_lemmas(&self) -> bool {
        self.lrat_mode && self.lrat_blocked_by_theory_lemmas
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn scoped_decompose_proof_emit_records(&self) -> &[DecomposeProofEmitRecord] {
        &self.scoped_decompose_proof_emit_records
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn learned_lrat_authority_records(&self) -> &[LearnedLratAuthorityRecord] {
        &self.learned_lrat_authority_records
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn materialize_fmla_learned_lrat_authority_exports(
        &self,
    ) -> Vec<LearnedLratMaterializationExport> {
        self.learned_lrat_authority_records
            .iter()
            .map(|record| self.materialize_fmla_learned_lrat_authority_record(record))
            .collect()
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn checked_fmla_learned_lrat_materialization_replays(
        &self,
    ) -> Vec<LearnedLratMaterializationReplay> {
        self.materialize_fmla_learned_lrat_authority_exports()
            .into_iter()
            .map(Self::checked_fmla_learned_lrat_materialization_replay)
            .collect()
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn dry_run_fmla_learned_lrat_materialization_fragments(
        &self,
    ) -> Vec<LearnedLratDryRunProofArtifact> {
        self.checked_fmla_learned_lrat_materialization_replays()
            .iter()
            .map(Self::dry_run_fmla_learned_lrat_materialization_fragment_from_replay)
            .collect()
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        replay: &LearnedLratMaterializationReplay,
    ) -> LearnedLratDryRunProofArtifact {
        if replay.materialization_status
            != LearnedLratMaterializationStatus::RetainedDependenciesComplete
        {
            if !replay.rows.is_empty() {
                if Self::learned_lrat_status_allows_fail_closed_materializer_fragment(
                    replay.materialization_status,
                ) && Self::learned_lrat_materializer_replay_rows_are_checker_consistent(replay)
                {
                    return Self::fail_closed_learned_lrat_dry_run_artifact_with_rows(
                        replay,
                        replay.materialization_status,
                    );
                }
                return Self::fail_closed_learned_lrat_dry_run_artifact(
                    replay,
                    LearnedLratMaterializationStatus::FailClosedMalformedReplayRows,
                );
            }
            return Self::fail_closed_learned_lrat_dry_run_artifact(
                replay,
                replay.materialization_status,
            );
        }
        if replay.proof_writer_io_error {
            return Self::fail_closed_learned_lrat_dry_run_artifact(
                replay,
                LearnedLratMaterializationStatus::FailClosedProofWriterIoError,
            );
        }
        if replay.proof_out_emitted {
            return Self::fail_closed_learned_lrat_dry_run_artifact(
                replay,
                LearnedLratMaterializationStatus::FailClosedProofOutAlreadyEmitted,
            );
        }
        if !Self::learned_lrat_replay_rows_are_checker_consistent(replay) {
            return Self::fail_closed_learned_lrat_dry_run_artifact(
                replay,
                LearnedLratMaterializationStatus::FailClosedMalformedReplayRows,
            );
        }

        let rows: Vec<_> = replay
            .rows
            .iter()
            .map(|row| LearnedLratDryRunProofRow {
                kind: row.kind,
                checker_visible_id: row.checker_visible_id,
                clause_lits_dimacs: row.clause_lits_dimacs.clone(),
                checker_visible_lrat_hints: row.checker_visible_lrat_hints.clone(),
                lrat_line: Self::serialize_lrat_add_line(row),
            })
            .collect();
        let lrat_fragment: String = rows.iter().map(|row| row.lrat_line.as_str()).collect();

        LearnedLratDryRunProofArtifact {
            checker_visible_id: replay.checker_visible_id,
            materialization_status: LearnedLratMaterializationStatus::RetainedDependenciesComplete,
            rows,
            lrat_fragment,
            proof_out_emitted: false,
            proof_writer_io_error: false,
            external_checker_required: true,
            external_checker_verified: false,
            main_proof_authority_reason: LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_REQUIRED,
            authorizes_main_proof_out: false,
        }
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn export_fmla_learned_lrat_dry_run_proof_artifact(
        dry_run: &LearnedLratDryRunProofArtifact,
    ) -> LearnedLratDryRunProofArtifactEnvelope {
        LearnedLratDryRunProofArtifactEnvelope {
            schema: LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA.to_string(),
            checker_visible_id: dry_run.checker_visible_id,
            materialization_status: dry_run.materialization_status,
            rows: dry_run.rows.clone(),
            lrat_fragment: dry_run.lrat_fragment.clone(),
            lrat_fragment_sha256: Self::sha256_hex(dry_run.lrat_fragment.as_bytes()),
            proof_out_emitted: dry_run.proof_out_emitted,
            proof_writer_io_error: dry_run.proof_writer_io_error,
            external_checker_required: dry_run.external_checker_required,
            external_checker_verified: dry_run.external_checker_verified,
            main_proof_authority_reason: dry_run.main_proof_authority_reason.to_string(),
            authorizes_main_proof_out: dry_run.authorizes_main_proof_out,
        }
    }

    pub(crate) fn fail_closed_no_fmla_learned_lrat_dry_run_proof_artifact(
    ) -> LearnedLratDryRunProofArtifact {
        LearnedLratDryRunProofArtifact {
            checker_visible_id: 0,
            materialization_status:
                LearnedLratMaterializationStatus::FailClosedNoLearnedLratAuthorityRecords,
            rows: Vec::new(),
            lrat_fragment: String::new(),
            proof_out_emitted: false,
            proof_writer_io_error: false,
            external_checker_required: false,
            external_checker_verified: false,
            main_proof_authority_reason: LEARNED_LRAT_AUTHORITY_FAIL_CLOSED,
            authorizes_main_proof_out: false,
        }
    }

    pub(crate) fn fail_closed_missing_fmla_materializer_dependency_artifact(
        checker_visible_id: u64,
    ) -> LearnedLratDryRunProofArtifact {
        LearnedLratDryRunProofArtifact {
            checker_visible_id,
            materialization_status:
                LearnedLratMaterializationStatus::FailClosedMissingMaterializerDependency,
            rows: Vec::new(),
            lrat_fragment: String::new(),
            proof_out_emitted: false,
            proof_writer_io_error: false,
            external_checker_required: false,
            external_checker_verified: false,
            main_proof_authority_reason: LEARNED_LRAT_AUTHORITY_FAIL_CLOSED,
            authorizes_main_proof_out: false,
        }
    }

    pub(crate) fn fail_closed_fmla_materializer_rows_diagnostic_artifact(
        &self,
        checker_visible_id: u64,
    ) -> Option<LearnedLratDryRunProofArtifact> {
        let mut rows = Vec::new();
        for source_record in &self.scoped_decompose_proof_emit_records {
            if source_record.proof_out_record_kind != DecomposeProofOutRecordKind::Add
                || source_record.checker_visible_id == 0
                || source_record.proof_manager_mode != "lrat"
                || !source_record.solver_runtime_emitted
                || source_record.proof_writer_io_error
                || source_record.lrat_hints.is_empty()
            {
                continue;
            }

            let checker_visible_hints = Self::fail_closed_materializer_lrat_hints(source_record);
            if checker_visible_hints.is_empty() {
                continue;
            }

            rows.push(LearnedLratReplayRow {
                kind: LearnedLratReplayRowKind::MaterializerAdd,
                checker_visible_id: source_record.checker_visible_id,
                clause_lits_dimacs: source_record.clause_lits_dimacs.clone(),
                checker_visible_lrat_hints: checker_visible_hints,
            });
            if rows.len() >= LEARNED_LRAT_DRY_RUN_MAX_FAIL_CLOSED_MATERIALIZER_ROWS {
                break;
            }
        }

        if rows.is_empty() {
            return None;
        }

        let replay = LearnedLratMaterializationReplay {
            checker_visible_id,
            materialization_status:
                LearnedLratMaterializationStatus::FailClosedNoLearnedLratAuthorityRecords,
            rows,
            proof_out_emitted: false,
            proof_writer_io_error: false,
        };
        Some(Self::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(&replay))
    }

    fn fail_closed_materializer_lrat_hints(record: &DecomposeProofEmitRecord) -> Vec<u64> {
        let mut hints = Vec::with_capacity(record.lrat_hints.len());
        let mut seen = det_hash_set_with_capacity(record.lrat_hints.len());
        for &hint in &record.lrat_hints {
            if hint != 0 && seen.insert(hint) {
                hints.push(hint);
            }
        }
        hints
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn import_fmla_learned_lrat_dry_run_proof_artifact(
        envelope: LearnedLratDryRunProofArtifactEnvelope,
    ) -> Result<LearnedLratDryRunProofArtifact, LearnedLratDryRunProofArtifactImportReject> {
        if envelope.schema != LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA {
            return Err(LearnedLratDryRunProofArtifactImportReject::SchemaMismatch {
                observed: envelope.schema,
            });
        }
        if envelope.authorizes_main_proof_out || envelope.external_checker_verified {
            return Err(LearnedLratDryRunProofArtifactImportReject::InvalidAuthorityState);
        }
        if !Self::sha256_hex(envelope.lrat_fragment.as_bytes())
            .eq_ignore_ascii_case(&envelope.lrat_fragment_sha256)
        {
            return Err(LearnedLratDryRunProofArtifactImportReject::LratFragmentSha256Mismatch);
        }

        let reason = match envelope.main_proof_authority_reason.as_str() {
            LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_REQUIRED => {
                LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_REQUIRED
            }
            LEARNED_LRAT_AUTHORITY_FAIL_CLOSED => LEARNED_LRAT_AUTHORITY_FAIL_CLOSED,
            observed => {
                return Err(
                    LearnedLratDryRunProofArtifactImportReject::InvalidAuthorityReason {
                        observed: observed.to_string(),
                    },
                )
            }
        };

        let row_fragment: String = envelope
            .rows
            .iter()
            .map(|row| row.lrat_line.as_str())
            .collect();
        if row_fragment != envelope.lrat_fragment {
            return Err(LearnedLratDryRunProofArtifactImportReject::LratFragmentRowsMismatch);
        }
        if envelope
            .rows
            .iter()
            .any(|row| !Self::learned_lrat_dry_run_row_lrat_line_matches_fields(row))
        {
            return Err(LearnedLratDryRunProofArtifactImportReject::LratFragmentRowsMismatch);
        }

        if envelope.materialization_status
            == LearnedLratMaterializationStatus::RetainedDependenciesComplete
        {
            if envelope.rows.is_empty()
                || envelope.lrat_fragment.is_empty()
                || !envelope.external_checker_required
                || envelope.proof_out_emitted
                || envelope.proof_writer_io_error
                || reason != LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_REQUIRED
            {
                return Err(LearnedLratDryRunProofArtifactImportReject::InvalidAuthorityState);
            }
            let replay = LearnedLratMaterializationReplay {
                checker_visible_id: envelope.checker_visible_id,
                materialization_status: envelope.materialization_status,
                rows: envelope
                    .rows
                    .iter()
                    .map(|row| LearnedLratReplayRow {
                        kind: row.kind,
                        checker_visible_id: row.checker_visible_id,
                        clause_lits_dimacs: row.clause_lits_dimacs.clone(),
                        checker_visible_lrat_hints: row.checker_visible_lrat_hints.clone(),
                    })
                    .collect(),
                proof_out_emitted: envelope.proof_out_emitted,
                proof_writer_io_error: envelope.proof_writer_io_error,
            };
            if !Self::learned_lrat_replay_rows_are_checker_consistent(&replay) {
                return Err(LearnedLratDryRunProofArtifactImportReject::ReplayRowsMalformed);
            }
        } else {
            if envelope.external_checker_required || reason != LEARNED_LRAT_AUTHORITY_FAIL_CLOSED {
                return Err(LearnedLratDryRunProofArtifactImportReject::InvalidAuthorityState);
            }
            if !envelope.rows.is_empty() {
                if !Self::learned_lrat_status_allows_fail_closed_materializer_fragment(
                    envelope.materialization_status,
                ) {
                    return Err(LearnedLratDryRunProofArtifactImportReject::InvalidAuthorityState);
                }
                let replay = LearnedLratMaterializationReplay {
                    checker_visible_id: envelope.checker_visible_id,
                    materialization_status: envelope.materialization_status,
                    rows: envelope
                        .rows
                        .iter()
                        .map(|row| LearnedLratReplayRow {
                            kind: row.kind,
                            checker_visible_id: row.checker_visible_id,
                            clause_lits_dimacs: row.clause_lits_dimacs.clone(),
                            checker_visible_lrat_hints: row.checker_visible_lrat_hints.clone(),
                        })
                        .collect(),
                    proof_out_emitted: envelope.proof_out_emitted,
                    proof_writer_io_error: envelope.proof_writer_io_error,
                };
                if !Self::learned_lrat_materializer_replay_rows_are_checker_consistent(&replay) {
                    return Err(LearnedLratDryRunProofArtifactImportReject::ReplayRowsMalformed);
                }
            } else if !envelope.lrat_fragment.is_empty() {
                return Err(LearnedLratDryRunProofArtifactImportReject::LratFragmentRowsMismatch);
            }
        }

        Ok(LearnedLratDryRunProofArtifact {
            checker_visible_id: envelope.checker_visible_id,
            materialization_status: envelope.materialization_status,
            rows: envelope.rows,
            lrat_fragment: envelope.lrat_fragment,
            proof_out_emitted: envelope.proof_out_emitted,
            proof_writer_io_error: envelope.proof_writer_io_error,
            external_checker_required: envelope.external_checker_required,
            external_checker_verified: false,
            main_proof_authority_reason: reason,
            authorizes_main_proof_out: false,
        })
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn fmla_learned_lrat_dry_run_proof_artifact_envelope_to_json_value(
        envelope: &LearnedLratDryRunProofArtifactEnvelope,
    ) -> Value {
        let rows: Vec<_> = envelope
            .rows
            .iter()
            .map(|row| {
                json!({
                    "kind": Self::learned_lrat_replay_row_kind_to_str(row.kind),
                    "checker_visible_id": row.checker_visible_id,
                    "clause_lits_dimacs": &row.clause_lits_dimacs,
                    "checker_visible_lrat_hints": &row.checker_visible_lrat_hints,
                    "lrat_line": &row.lrat_line,
                })
            })
            .collect();
        json!({
            "schema": envelope.schema,
            "checker_visible_id": envelope.checker_visible_id,
            "materialization_status": Self::learned_lrat_materialization_status_to_str(
                envelope.materialization_status
            ),
            "rows": rows,
            "lrat_fragment": envelope.lrat_fragment,
            "lrat_fragment_sha256": envelope.lrat_fragment_sha256,
            "proof_out_emitted": envelope.proof_out_emitted,
            "proof_writer_io_error": envelope.proof_writer_io_error,
            "external_checker_required": envelope.external_checker_required,
            "external_checker_verified": envelope.external_checker_verified,
            "main_proof_authority_reason": envelope.main_proof_authority_reason,
            "authorizes_main_proof_out": envelope.authorizes_main_proof_out,
        })
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn fmla_learned_lrat_dry_run_proof_artifact_envelope_from_json_value(
        value: &Value,
    ) -> Result<LearnedLratDryRunProofArtifactEnvelope, LearnedLratDryRunProofArtifactImportReject>
    {
        let schema = Self::json_required_str(value, "schema")?.to_string();
        let checker_visible_id = Self::json_required_u64(value, "checker_visible_id")?;
        let status = Self::learned_lrat_materialization_status_from_str(Self::json_required_str(
            value,
            "materialization_status",
        )?)
        .ok_or(LearnedLratDryRunProofArtifactImportReject::InvalidField(
            "materialization_status",
        ))?;
        let row_values = value
            .get("rows")
            .ok_or(LearnedLratDryRunProofArtifactImportReject::MissingField(
                "rows",
            ))?
            .as_array()
            .ok_or(LearnedLratDryRunProofArtifactImportReject::InvalidField(
                "rows",
            ))?;
        let mut rows = Vec::with_capacity(row_values.len());
        for row_value in row_values {
            let kind = Self::learned_lrat_replay_row_kind_from_str(Self::json_required_str(
                row_value, "kind",
            )?)
            .ok_or(LearnedLratDryRunProofArtifactImportReject::InvalidField(
                "kind",
            ))?;
            rows.push(LearnedLratDryRunProofRow {
                kind,
                checker_visible_id: Self::json_required_u64(row_value, "checker_visible_id")?,
                clause_lits_dimacs: Self::json_required_i64_array(row_value, "clause_lits_dimacs")?,
                checker_visible_lrat_hints: Self::json_required_u64_array(
                    row_value,
                    "checker_visible_lrat_hints",
                )?,
                lrat_line: Self::json_required_str(row_value, "lrat_line")?.to_string(),
            });
        }

        Ok(LearnedLratDryRunProofArtifactEnvelope {
            schema,
            checker_visible_id,
            materialization_status: status,
            rows,
            lrat_fragment: Self::json_required_str(value, "lrat_fragment")?.to_string(),
            lrat_fragment_sha256: Self::json_required_str(value, "lrat_fragment_sha256")?
                .to_string(),
            proof_out_emitted: Self::json_required_bool(value, "proof_out_emitted")?,
            proof_writer_io_error: Self::json_required_bool(value, "proof_writer_io_error")?,
            external_checker_required: Self::json_required_bool(
                value,
                "external_checker_required",
            )?,
            external_checker_verified: Self::json_required_bool(
                value,
                "external_checker_verified",
            )?,
            main_proof_authority_reason: Self::json_required_str(
                value,
                "main_proof_authority_reason",
            )?
            .to_string(),
            authorizes_main_proof_out: Self::json_required_bool(
                value,
                "authorizes_main_proof_out",
            )?,
        })
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn validate_fmla_learned_lrat_main_proof_authority(
        dry_run: &LearnedLratDryRunProofArtifact,
        checker_verdict: &ExternalProofCheckerVerdictArtifactRef,
        proof_out_bytes: &[u8],
    ) -> Result<LearnedLratMainProofAuthorityArtifact, LearnedLratMainProofAuthorityReject> {
        if dry_run.materialization_status
            != LearnedLratMaterializationStatus::RetainedDependenciesComplete
        {
            return Err(LearnedLratMainProofAuthorityReject::DryRunNotComplete {
                materialization_status: dry_run.materialization_status,
            });
        }
        if dry_run.lrat_fragment.is_empty() || dry_run.rows.is_empty() {
            return Err(LearnedLratMainProofAuthorityReject::DryRunFragmentMissing);
        }
        if !dry_run.external_checker_required
            || dry_run.external_checker_verified
            || dry_run.authorizes_main_proof_out
            || dry_run.main_proof_authority_reason
                != LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_REQUIRED
        {
            return Err(LearnedLratMainProofAuthorityReject::DryRunInvalidAuthorityState);
        }
        if let Err(reason) = validate_external_checker_verdict_artifact(checker_verdict) {
            return Err(
                LearnedLratMainProofAuthorityReject::ExternalCheckerVerdictNotAccepted { reason },
            );
        }

        let observed_proof_out_sha256 = Self::sha256_hex(proof_out_bytes);
        if !observed_proof_out_sha256.eq_ignore_ascii_case(&checker_verdict.proof_out_sha256) {
            return Err(LearnedLratMainProofAuthorityReject::ProofOutSha256Mismatch);
        }
        let proof_out_text = std::str::from_utf8(proof_out_bytes)
            .map_err(|_| LearnedLratMainProofAuthorityReject::ProofOutNotUtf8)?;
        if !proof_out_text.contains(dry_run.lrat_fragment.as_str()) {
            return Err(LearnedLratMainProofAuthorityReject::ProofOutMissingDryRunFragment);
        }

        Ok(LearnedLratMainProofAuthorityArtifact {
            checker_visible_id: dry_run.checker_visible_id,
            materialization_status: dry_run.materialization_status,
            proof_out_path: checker_verdict.proof_out_path.clone(),
            proof_out_sha256: observed_proof_out_sha256,
            external_checker_verified: true,
            proof_out_contains_lrat_fragment: true,
            main_proof_authority_reason: LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_VERIFIED,
            authorizes_main_proof_out: true,
        })
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn validate_fmla_learned_lrat_main_proof_authority_from_postcheck_replay(
        dry_run: &LearnedLratDryRunProofArtifact,
        postcheck_replay: &FmlaPostCheckAdmissionReplayRecord,
        retained_proof_out_path: &str,
        proof_out_bytes: &[u8],
    ) -> Result<LearnedLratMainProofAuthorityArtifact, LearnedLratMainProofAuthorityReject> {
        if postcheck_replay.schema != FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA
            || postcheck_replay.status != "committed_checker_backed_admission"
        {
            return Err(
                LearnedLratMainProofAuthorityReject::PostCheckReplayNotCommitted {
                    schema: postcheck_replay.schema,
                    status: postcheck_replay.status,
                },
            );
        }
        if postcheck_replay.proof_obligation_rows == 0 {
            return Err(LearnedLratMainProofAuthorityReject::PostCheckReplayMissingProofRows);
        }
        if postcheck_replay.external_checker_verdict_artifact_rows
            != postcheck_replay.proof_obligation_rows
        {
            return Err(
                LearnedLratMainProofAuthorityReject::PostCheckReplayCheckerRowMismatch {
                    proof_obligation_rows: postcheck_replay.proof_obligation_rows,
                    external_checker_verdict_artifact_rows: postcheck_replay
                        .external_checker_verdict_artifact_rows,
                },
            );
        }
        let checker_proof_out_path = postcheck_replay
            .external_checker_verdict_artifact
            .proof_out_path
            .as_str();
        if retained_proof_out_path != checker_proof_out_path {
            return Err(LearnedLratMainProofAuthorityReject::ProofOutPathMismatch {
                retained_proof_out_path: retained_proof_out_path.to_string(),
                checker_proof_out_path: checker_proof_out_path.to_string(),
            });
        }

        Self::validate_fmla_learned_lrat_main_proof_authority(
            dry_run,
            &postcheck_replay.external_checker_verdict_artifact,
            proof_out_bytes,
        )
    }

    pub(crate) fn append_authorized_fmla_learned_lrat_fragment_from_replay_json(
        &mut self,
        replay: &Value,
        current_proof_out_path: &str,
    ) -> Result<usize, LearnedLratProofOutAppendReject> {
        if !self.lrat_mode {
            return Err(LearnedLratProofOutAppendReject::NotLrat);
        }

        let dry_run = self
            .dry_run_fmla_learned_lrat_materialization_fragments()
            .into_iter()
            .find(|artifact| {
                artifact.materialization_status
                    == LearnedLratMaterializationStatus::RetainedDependenciesComplete
                    && artifact.external_checker_required
                    && !artifact.external_checker_verified
                    && !artifact.authorizes_main_proof_out
                    && !artifact.proof_out_emitted
                    && !artifact.proof_writer_io_error
                    && !artifact.rows.is_empty()
                    && !artifact.lrat_fragment.is_empty()
            })
            .ok_or(LearnedLratProofOutAppendReject::NoCompleteDryRun)?;

        if dry_run.main_proof_authority_reason != LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_REQUIRED {
            return Err(LearnedLratProofOutAppendReject::DryRunInvalidAuthorityState);
        }

        let replay_rows: Vec<_> = dry_run
            .rows
            .iter()
            .map(|row| LearnedLratReplayRow {
                kind: row.kind,
                checker_visible_id: row.checker_visible_id,
                clause_lits_dimacs: row.clause_lits_dimacs.clone(),
                checker_visible_lrat_hints: row.checker_visible_lrat_hints.clone(),
            })
            .collect();
        let materialization_replay = LearnedLratMaterializationReplay {
            checker_visible_id: dry_run.checker_visible_id,
            materialization_status: dry_run.materialization_status,
            rows: replay_rows,
            proof_out_emitted: dry_run.proof_out_emitted,
            proof_writer_io_error: dry_run.proof_writer_io_error,
        };
        if !Self::learned_lrat_replay_rows_are_checker_consistent(&materialization_replay) {
            return Err(LearnedLratProofOutAppendReject::ReplayRowsMalformed);
        }

        Self::validate_fmla_learned_lrat_append_authority_replay_json(
            replay,
            current_proof_out_path,
            dry_run.rows.len() as u64,
        )?;

        let mut emitted = 0usize;
        for row in &dry_run.rows {
            match row.kind {
                LearnedLratReplayRowKind::MaterializerAdd => {
                    if !self.lrat_id_usable_as_hint(row.checker_visible_id) {
                        return Err(LearnedLratProofOutAppendReject::MaterializerRowNotLive {
                            checker_visible_id: row.checker_visible_id,
                        });
                    }
                }
                LearnedLratReplayRowKind::LearnedAdd => {
                    self.append_authorized_fmla_learned_lrat_row(row)?;
                    emitted += 1;
                }
            }
        }

        if emitted == 0 {
            return Err(LearnedLratProofOutAppendReject::NoLearnedRows);
        }
        Ok(emitted)
    }

    fn validate_fmla_learned_lrat_append_authority_replay_json(
        value: &Value,
        current_proof_out_path: &str,
        proof_rows: u64,
    ) -> Result<(), LearnedLratProofOutAppendReject> {
        if value.get("schema").and_then(Value::as_str)
            != Some(FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA)
            || value.get("status").and_then(Value::as_str)
                != Some("committed_checker_backed_admission")
        {
            return Err(LearnedLratProofOutAppendReject::ReplayNotCommitted);
        }
        if proof_rows == 0
            || value.get("proof_obligation_rows").and_then(Value::as_u64) != Some(proof_rows)
            || value
                .get("external_proof_checker_verdict_artifact_rows")
                .and_then(Value::as_u64)
                != Some(proof_rows)
        {
            return Err(LearnedLratProofOutAppendReject::ReplayRowsMismatch);
        }
        if value
            .get("learned_lrat_main_proof_authority_status")
            .and_then(Value::as_str)
            != Some("authorized")
            || value
                .get("learned_lrat_main_proof_authority_external_checker_verified")
                .and_then(Value::as_bool)
                != Some(true)
            || value
                .get("learned_lrat_main_proof_authority_proof_out_contains_lrat_fragment")
                .and_then(Value::as_bool)
                != Some(true)
            || value
                .get("learned_lrat_main_proof_authority_authorizes_main_proof_out")
                .and_then(Value::as_bool)
                != Some(true)
            || value
                .get("external_proof_checker_verdict")
                .and_then(Value::as_str)
                != Some("VERIFIED_UNSAT")
            || value.get("checker_exit_code").and_then(Value::as_i64) != Some(0)
        {
            return Err(LearnedLratProofOutAppendReject::ReplayNotAuthorized);
        }

        let Some(authority_proof_out_path) = value
            .get("learned_lrat_main_proof_authority_proof_out_path")
            .and_then(Value::as_str)
        else {
            return Err(LearnedLratProofOutAppendReject::ReplayNotAuthorized);
        };
        if authority_proof_out_path != current_proof_out_path {
            return Err(LearnedLratProofOutAppendReject::ProofOutPathMismatch {
                retained_proof_out_path: current_proof_out_path.to_string(),
                checker_proof_out_path: authority_proof_out_path.to_string(),
            });
        }
        let Some(expected_sha256) = value
            .get("learned_lrat_main_proof_authority_proof_out_sha256")
            .and_then(Value::as_str)
        else {
            return Err(LearnedLratProofOutAppendReject::ReplayNotAuthorized);
        };
        let Some(checker_artifact) = Self::fmla_external_checker_verdict_artifact_from_replay_json(
            value,
            authority_proof_out_path,
            expected_sha256,
        ) else {
            return Err(LearnedLratProofOutAppendReject::ReplayNotAuthorized);
        };
        validate_external_checker_verdict_artifact_file(&checker_artifact).map_err(|reason| {
            LearnedLratProofOutAppendReject::ExternalCheckerVerdictNotAccepted { reason }
        })
    }

    fn fmla_external_checker_verdict_artifact_from_replay_json(
        value: &Value,
        proof_out_path: &str,
        proof_out_sha256: &str,
    ) -> Option<ExternalProofCheckerVerdictArtifactRef> {
        Some(ExternalProofCheckerVerdictArtifactRef {
            schema: Self::json_string(value, "external_proof_checker_verdict_artifact_schema")?,
            runtime_field: Self::json_string(
                value,
                "external_proof_checker_verdict_artifact_runtime_field",
            )?,
            artifact_path: Self::json_string(value, "external_proof_checker_verdict_artifact")?,
            artifact_sha256: Self::json_string(
                value,
                "external_proof_checker_verdict_artifact_sha256",
            )?,
            checker_path: Self::json_string(value, "external_proof_checker_path")?,
            checker_sha256: Self::json_string(value, "external_proof_checker_sha256")?,
            checker_command: Self::json_string(value, "external_proof_checker_command")?,
            checker_argv: Self::json_string_array(value, "external_proof_checker_argv")?,
            checker_exit_code: value.get("checker_exit_code")?.as_i64()?.try_into().ok()?,
            proof_out_path: proof_out_path.to_string(),
            proof_out_sha256: proof_out_sha256.to_string(),
            checked_dimacs_path: Self::json_string(value, "external_proof_checker_dimacs_path")?,
            checked_dimacs_sha256: Self::json_string(
                value,
                "external_proof_checker_dimacs_sha256",
            )?,
            verdict: Self::json_string(value, "external_proof_checker_verdict")?,
        })
    }

    fn append_authorized_fmla_learned_lrat_row(
        &mut self,
        row: &LearnedLratDryRunProofRow,
    ) -> Result<(), LearnedLratProofOutAppendReject> {
        if !self.backward_reserved_ids.contains(row.checker_visible_id) {
            return Err(LearnedLratProofOutAppendReject::LearnedRowNotReserved {
                checker_visible_id: row.checker_visible_id,
            });
        }
        let clause = Self::clause_from_dimacs_i64(&row.clause_lits_dimacs)?;
        self.preflight_forward_lrat_add_with_planned_ids(
            &clause,
            &row.checker_visible_lrat_hints,
            ProofAddKind::Derived,
            &[],
        )
        .map_err(LearnedLratProofOutAppendReject::PlannedAddRejected)?;
        self.output
            .add_with_id(
                row.checker_visible_id,
                &clause,
                &row.checker_visible_lrat_hints,
            )
            .map_err(|_| LearnedLratProofOutAppendReject::ProofWriterIoError)?;
        self.backward_reserved_ids.remove(row.checker_visible_id);
        self.last_add = Some(LastAdd::new(row.checker_visible_id, &clause));
        if let Some(record) = self
            .learned_lrat_authority_records
            .iter_mut()
            .find(|record| record.checker_visible_id == row.checker_visible_id)
        {
            record.proof_out_emitted = true;
        }
        #[cfg(debug_assertions)]
        if let Some(ref mut lrat) = self.lrat_checker {
            lrat.add_original(row.checker_visible_id, &clause);
        }
        Ok(())
    }

    fn fail_closed_learned_lrat_dry_run_artifact(
        replay: &LearnedLratMaterializationReplay,
        materialization_status: LearnedLratMaterializationStatus,
    ) -> LearnedLratDryRunProofArtifact {
        LearnedLratDryRunProofArtifact {
            checker_visible_id: replay.checker_visible_id,
            materialization_status,
            rows: Vec::new(),
            lrat_fragment: String::new(),
            proof_out_emitted: replay.proof_out_emitted,
            proof_writer_io_error: replay.proof_writer_io_error,
            external_checker_required: false,
            external_checker_verified: false,
            main_proof_authority_reason: LEARNED_LRAT_AUTHORITY_FAIL_CLOSED,
            authorizes_main_proof_out: false,
        }
    }

    fn fail_closed_learned_lrat_dry_run_artifact_with_rows(
        replay: &LearnedLratMaterializationReplay,
        materialization_status: LearnedLratMaterializationStatus,
    ) -> LearnedLratDryRunProofArtifact {
        let rows: Vec<_> = replay
            .rows
            .iter()
            .map(|row| LearnedLratDryRunProofRow {
                kind: row.kind,
                checker_visible_id: row.checker_visible_id,
                clause_lits_dimacs: row.clause_lits_dimacs.clone(),
                checker_visible_lrat_hints: row.checker_visible_lrat_hints.clone(),
                lrat_line: Self::serialize_lrat_add_line(row),
            })
            .collect();
        let lrat_fragment: String = rows.iter().map(|row| row.lrat_line.as_str()).collect();

        LearnedLratDryRunProofArtifact {
            checker_visible_id: replay.checker_visible_id,
            materialization_status,
            rows,
            lrat_fragment,
            proof_out_emitted: replay.proof_out_emitted,
            proof_writer_io_error: replay.proof_writer_io_error,
            external_checker_required: false,
            external_checker_verified: false,
            main_proof_authority_reason: LEARNED_LRAT_AUTHORITY_FAIL_CLOSED,
            authorizes_main_proof_out: false,
        }
    }

    fn learned_lrat_dry_run_row_lrat_line_matches_fields(row: &LearnedLratDryRunProofRow) -> bool {
        let replay_row = LearnedLratReplayRow {
            kind: row.kind,
            checker_visible_id: row.checker_visible_id,
            clause_lits_dimacs: row.clause_lits_dimacs.clone(),
            checker_visible_lrat_hints: row.checker_visible_lrat_hints.clone(),
        };
        row.lrat_line == Self::serialize_lrat_add_line(&replay_row)
    }

    fn learned_lrat_status_allows_fail_closed_materializer_fragment(
        status: LearnedLratMaterializationStatus,
    ) -> bool {
        matches!(
            status,
            LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency
                | LearnedLratMaterializationStatus::FailClosedNoLearnedLratAuthorityRecords
                | LearnedLratMaterializationStatus::FailClosedIncompleteMaterializerDependency
        )
    }

    fn learned_lrat_materializer_replay_rows_are_checker_consistent(
        replay: &LearnedLratMaterializationReplay,
    ) -> bool {
        if replay.rows.is_empty()
            || replay.rows.len() > LEARNED_LRAT_DRY_RUN_MAX_FAIL_CLOSED_MATERIALIZER_ROWS
        {
            return false;
        }

        let mut all_replay_ids = det_hash_set_with_capacity(replay.rows.len());
        for row in &replay.rows {
            if row.kind != LearnedLratReplayRowKind::MaterializerAdd
                || row.checker_visible_id == 0
                || !all_replay_ids.insert(row.checker_visible_id)
            {
                return false;
            }
        }

        let mut seen_replay_ids = det_hash_set_with_capacity(replay.rows.len());
        for row in &replay.rows {
            if row.checker_visible_lrat_hints.is_empty() {
                return false;
            }
            let mut row_hints = det_hash_set_with_capacity(row.checker_visible_lrat_hints.len());
            for &hint in &row.checker_visible_lrat_hints {
                if hint == 0 || hint == row.checker_visible_id || !row_hints.insert(hint) {
                    return false;
                }
                if all_replay_ids.contains(&hint) && !seen_replay_ids.contains(&hint) {
                    return false;
                }
            }
            seen_replay_ids.insert(row.checker_visible_id);
        }

        true
    }

    fn learned_lrat_replay_rows_are_checker_consistent(
        replay: &LearnedLratMaterializationReplay,
    ) -> bool {
        if replay.rows.len() < 2 {
            return false;
        }
        let Some(last) = replay.rows.last() else {
            return false;
        };
        if last.kind != LearnedLratReplayRowKind::LearnedAdd
            || last.checker_visible_id != replay.checker_visible_id
        {
            return false;
        }
        if replay.rows[..replay.rows.len() - 1]
            .iter()
            .any(|row| row.kind != LearnedLratReplayRowKind::MaterializerAdd)
        {
            return false;
        }

        let mut all_replay_ids = det_hash_set_with_capacity(replay.rows.len());
        for row in &replay.rows {
            if row.checker_visible_id == 0 || !all_replay_ids.insert(row.checker_visible_id) {
                return false;
            }
        }

        let mut seen_replay_ids = det_hash_set_with_capacity(replay.rows.len());
        let mut materializer_ids = det_hash_set_with_capacity(replay.rows.len().saturating_sub(1));
        let mut learned_row_seen = false;
        let mut learned_depends_on_materializer = false;

        for row in &replay.rows {
            if row.checker_visible_lrat_hints.is_empty() {
                return false;
            }
            if row.kind == LearnedLratReplayRowKind::LearnedAdd {
                if learned_row_seen {
                    return false;
                }
                learned_row_seen = true;
            }

            let mut row_hints = det_hash_set_with_capacity(row.checker_visible_lrat_hints.len());
            for &hint in &row.checker_visible_lrat_hints {
                if hint == 0 || hint == row.checker_visible_id || !row_hints.insert(hint) {
                    return false;
                }
                if all_replay_ids.contains(&hint) && !seen_replay_ids.contains(&hint) {
                    return false;
                }
                if row.kind == LearnedLratReplayRowKind::LearnedAdd
                    && materializer_ids.contains(&hint)
                {
                    learned_depends_on_materializer = true;
                }
            }

            seen_replay_ids.insert(row.checker_visible_id);
            if row.kind == LearnedLratReplayRowKind::MaterializerAdd {
                materializer_ids.insert(row.checker_visible_id);
            }
        }

        learned_row_seen && learned_depends_on_materializer
    }

    fn serialize_lrat_add_line(row: &LearnedLratReplayRow) -> String {
        let mut line = row.checker_visible_id.to_string();
        for lit in &row.clause_lits_dimacs {
            line.push(' ');
            line.push_str(&lit.to_string());
        }
        line.push_str(" 0");
        for hint in &row.checker_visible_lrat_hints {
            line.push(' ');
            line.push_str(&hint.to_string());
        }
        line.push_str(" 0\n");
        line
    }

    fn learned_lrat_replay_row_kind_to_str(kind: LearnedLratReplayRowKind) -> &'static str {
        match kind {
            LearnedLratReplayRowKind::MaterializerAdd => "materializer_add",
            LearnedLratReplayRowKind::LearnedAdd => "learned_add",
        }
    }

    fn learned_lrat_replay_row_kind_from_str(value: &str) -> Option<LearnedLratReplayRowKind> {
        match value {
            "materializer_add" => Some(LearnedLratReplayRowKind::MaterializerAdd),
            "learned_add" => Some(LearnedLratReplayRowKind::LearnedAdd),
            _ => None,
        }
    }

    fn learned_lrat_materialization_status_to_str(
        status: LearnedLratMaterializationStatus,
    ) -> &'static str {
        match status {
            LearnedLratMaterializationStatus::RetainedDependenciesComplete => {
                "retained_dependencies_complete"
            }
            LearnedLratMaterializationStatus::FailClosedNoLearnedLratAuthorityRecords => {
                "fail_closed_no_learned_lrat_authority_records"
            }
            LearnedLratMaterializationStatus::FailClosedMissingMaterializerDependency => {
                "fail_closed_missing_materializer_dependency"
            }
            LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency => {
                "fail_closed_incomplete_learned_dependency"
            }
            LearnedLratMaterializationStatus::FailClosedIncompleteMaterializerDependency => {
                "fail_closed_incomplete_materializer_dependency"
            }
            LearnedLratMaterializationStatus::FailClosedMalformedReplayRows => {
                "fail_closed_malformed_replay_rows"
            }
            LearnedLratMaterializationStatus::FailClosedProofWriterIoError => {
                "fail_closed_proof_writer_io_error"
            }
            LearnedLratMaterializationStatus::FailClosedProofOutAlreadyEmitted => {
                "fail_closed_proof_out_already_emitted"
            }
        }
    }

    fn learned_lrat_materialization_status_from_str(
        value: &str,
    ) -> Option<LearnedLratMaterializationStatus> {
        match value {
            "retained_dependencies_complete" => {
                Some(LearnedLratMaterializationStatus::RetainedDependenciesComplete)
            }
            "fail_closed_no_learned_lrat_authority_records" => {
                Some(LearnedLratMaterializationStatus::FailClosedNoLearnedLratAuthorityRecords)
            }
            "fail_closed_missing_materializer_dependency" => {
                Some(LearnedLratMaterializationStatus::FailClosedMissingMaterializerDependency)
            }
            "fail_closed_incomplete_learned_dependency" => {
                Some(LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency)
            }
            "fail_closed_incomplete_materializer_dependency" => {
                Some(LearnedLratMaterializationStatus::FailClosedIncompleteMaterializerDependency)
            }
            "fail_closed_malformed_replay_rows" => {
                Some(LearnedLratMaterializationStatus::FailClosedMalformedReplayRows)
            }
            "fail_closed_proof_writer_io_error" => {
                Some(LearnedLratMaterializationStatus::FailClosedProofWriterIoError)
            }
            "fail_closed_proof_out_already_emitted" => {
                Some(LearnedLratMaterializationStatus::FailClosedProofOutAlreadyEmitted)
            }
            _ => None,
        }
    }

    fn json_required_str<'a>(
        value: &'a Value,
        field: &'static str,
    ) -> Result<&'a str, LearnedLratDryRunProofArtifactImportReject> {
        value
            .get(field)
            .ok_or(LearnedLratDryRunProofArtifactImportReject::MissingField(
                field,
            ))?
            .as_str()
            .ok_or(LearnedLratDryRunProofArtifactImportReject::InvalidField(
                field,
            ))
    }

    fn json_required_u64(
        value: &Value,
        field: &'static str,
    ) -> Result<u64, LearnedLratDryRunProofArtifactImportReject> {
        value
            .get(field)
            .ok_or(LearnedLratDryRunProofArtifactImportReject::MissingField(
                field,
            ))?
            .as_u64()
            .ok_or(LearnedLratDryRunProofArtifactImportReject::InvalidField(
                field,
            ))
    }

    fn json_required_bool(
        value: &Value,
        field: &'static str,
    ) -> Result<bool, LearnedLratDryRunProofArtifactImportReject> {
        value
            .get(field)
            .ok_or(LearnedLratDryRunProofArtifactImportReject::MissingField(
                field,
            ))?
            .as_bool()
            .ok_or(LearnedLratDryRunProofArtifactImportReject::InvalidField(
                field,
            ))
    }

    fn json_required_i64_array(
        value: &Value,
        field: &'static str,
    ) -> Result<Vec<i64>, LearnedLratDryRunProofArtifactImportReject> {
        value
            .get(field)
            .ok_or(LearnedLratDryRunProofArtifactImportReject::MissingField(
                field,
            ))?
            .as_array()
            .ok_or(LearnedLratDryRunProofArtifactImportReject::InvalidField(
                field,
            ))?
            .iter()
            .map(|entry| {
                entry
                    .as_i64()
                    .ok_or(LearnedLratDryRunProofArtifactImportReject::InvalidField(
                        field,
                    ))
            })
            .collect()
    }

    fn json_required_u64_array(
        value: &Value,
        field: &'static str,
    ) -> Result<Vec<u64>, LearnedLratDryRunProofArtifactImportReject> {
        value
            .get(field)
            .ok_or(LearnedLratDryRunProofArtifactImportReject::MissingField(
                field,
            ))?
            .as_array()
            .ok_or(LearnedLratDryRunProofArtifactImportReject::InvalidField(
                field,
            ))?
            .iter()
            .map(|entry| {
                entry
                    .as_u64()
                    .ok_or(LearnedLratDryRunProofArtifactImportReject::InvalidField(
                        field,
                    ))
            })
            .collect()
    }

    fn json_string(value: &Value, field: &'static str) -> Option<String> {
        value.get(field)?.as_str().map(str::to_string)
    }

    fn json_string_array(value: &Value, field: &'static str) -> Option<Vec<String>> {
        value
            .get(field)?
            .as_array()?
            .iter()
            .map(|item| item.as_str().map(str::to_string))
            .collect()
    }

    fn clause_from_dimacs_i64(
        dimacs_lits: &[i64],
    ) -> Result<Vec<Literal>, LearnedLratProofOutAppendReject> {
        dimacs_lits
            .iter()
            .map(|&lit| {
                let lit = i32::try_from(lit)
                    .map_err(|_| LearnedLratProofOutAppendReject::InvalidLiteral)?;
                if lit == 0 {
                    return Err(LearnedLratProofOutAppendReject::InvalidLiteral);
                }
                Ok(Literal::from_dimacs(lit))
            })
            .collect()
    }

    fn sha256_hex(bytes: &[u8]) -> String {
        let digest = Sha256::digest(bytes);
        let mut hex = String::with_capacity(64);
        for byte in digest {
            let _ = write!(&mut hex, "{byte:02x}");
        }
        hex
    }

    fn checked_fmla_learned_lrat_materialization_replay(
        export: LearnedLratMaterializationExport,
    ) -> LearnedLratMaterializationReplay {
        let retain_materializer_rows = export.materialization_status
            == LearnedLratMaterializationStatus::RetainedDependenciesComplete
            || Self::learned_lrat_status_allows_fail_closed_materializer_fragment(
                export.materialization_status,
            );
        let rows = if retain_materializer_rows {
            let materializer_row_limit = if export.materialization_status
                == LearnedLratMaterializationStatus::RetainedDependenciesComplete
            {
                export.materializer_rows.len()
            } else {
                export
                    .materializer_rows
                    .len()
                    .min(LEARNED_LRAT_DRY_RUN_MAX_FAIL_CLOSED_MATERIALIZER_ROWS)
            };
            let mut rows = Vec::with_capacity(export.materializer_rows.len() + 1);
            for materializer_row in export.materializer_rows.iter().take(materializer_row_limit) {
                rows.push(LearnedLratReplayRow {
                    kind: LearnedLratReplayRowKind::MaterializerAdd,
                    checker_visible_id: materializer_row.checker_visible_id,
                    clause_lits_dimacs: materializer_row.clause_lits_dimacs.clone(),
                    checker_visible_lrat_hints: materializer_row.checker_visible_lrat_hints.clone(),
                });
            }
            if export.materialization_status
                == LearnedLratMaterializationStatus::RetainedDependenciesComplete
            {
                rows.push(LearnedLratReplayRow {
                    kind: LearnedLratReplayRowKind::LearnedAdd,
                    checker_visible_id: export.checker_visible_id,
                    clause_lits_dimacs: export.clause_lits_dimacs.clone(),
                    checker_visible_lrat_hints: export.checker_visible_lrat_hints.clone(),
                });
            }
            rows
        } else {
            Vec::new()
        };

        LearnedLratMaterializationReplay {
            checker_visible_id: export.checker_visible_id,
            materialization_status: export.materialization_status,
            rows,
            proof_out_emitted: export.proof_out_emitted,
            proof_writer_io_error: export.proof_writer_io_error,
        }
    }

    fn materialize_fmla_learned_lrat_authority_record(
        &self,
        record: &LearnedLratAuthorityRecord,
    ) -> LearnedLratMaterializationExport {
        let mut materialization_status =
            LearnedLratMaterializationStatus::RetainedDependenciesComplete;
        if record.proof_writer_io_error {
            materialization_status = LearnedLratMaterializationStatus::FailClosedProofWriterIoError;
        } else if record.proof_out_emitted {
            materialization_status =
                LearnedLratMaterializationStatus::FailClosedProofOutAlreadyEmitted;
        }

        let (checker_visible_lrat_hints, learned_hints_complete) =
            self.checker_visible_learned_lrat_hints(record);
        if !learned_hints_complete
            && materialization_status
                == LearnedLratMaterializationStatus::RetainedDependenciesComplete
        {
            materialization_status =
                LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency;
        }

        let mut materializer_dependency_ids = Vec::with_capacity(
            checker_visible_lrat_hints.len() + record.materializer_dependency_ids.len(),
        );
        let mut seen_materializer_dependency_ids = det_hash_set_with_capacity(
            checker_visible_lrat_hints.len() + record.materializer_dependency_ids.len(),
        );
        for &hint in &checker_visible_lrat_hints {
            if seen_materializer_dependency_ids.insert(hint) {
                materializer_dependency_ids.push(hint);
            }
        }
        for &hint in &record.materializer_dependency_ids {
            if seen_materializer_dependency_ids.insert(hint) {
                materializer_dependency_ids.push(hint);
            }
        }

        let mut materializer_rows = Vec::new();
        for &hint in &materializer_dependency_ids {
            let Some(source_record) = self
                .scoped_decompose_proof_emit_records
                .iter()
                .find(|source_record| source_record.checker_visible_id == hint)
            else {
                continue;
            };

            let checker_visible_hints = self.checker_visible_materializer_lrat_hints(source_record);
            if !self.materializer_record_is_complete(source_record, &checker_visible_hints)
                && materialization_status
                    == LearnedLratMaterializationStatus::RetainedDependenciesComplete
            {
                materialization_status =
                    LearnedLratMaterializationStatus::FailClosedIncompleteMaterializerDependency;
            }

            materializer_rows.push(LearnedLratMaterializerDependencyExport {
                context: source_record.context.clone(),
                checker_visible_id: source_record.checker_visible_id,
                clause_lits_dimacs: source_record.clause_lits_dimacs.clone(),
                checker_visible_lrat_hints: checker_visible_hints,
                solver_runtime_emitted: source_record.solver_runtime_emitted,
                proof_writer_io_error: source_record.proof_writer_io_error,
            });
        }

        if materializer_rows.is_empty()
            && materialization_status
                == LearnedLratMaterializationStatus::RetainedDependenciesComplete
        {
            materialization_status =
                LearnedLratMaterializationStatus::FailClosedMissingMaterializerDependency;
        }

        LearnedLratMaterializationExport {
            checker_visible_id: record.checker_visible_id,
            clause_lits_dimacs: record.clause_lits_dimacs.clone(),
            raw_resolution_chain: record.raw_resolution_chain.clone(),
            checker_visible_lrat_hints,
            materializer_rows,
            proof_out_emitted: record.proof_out_emitted,
            proof_writer_io_error: record.proof_writer_io_error,
            authority_status: record.authority_status,
            materialization_status,
        }
    }

    fn checker_visible_learned_lrat_hints(
        &self,
        record: &LearnedLratAuthorityRecord,
    ) -> (Vec<u64>, bool) {
        let mut checker_visible_lrat_hints = Vec::with_capacity(record.lrat_hints.len());
        let mut seen = det_hash_set_with_capacity(record.lrat_hints.len());
        let mut complete = true;

        for &hint in &record.lrat_hints {
            if hint == 0 || hint == record.checker_visible_id {
                complete = false;
                continue;
            }
            if !self.lrat_id_usable_as_hint(hint) {
                complete = false;
                continue;
            }
            if seen.insert(hint) {
                checker_visible_lrat_hints.push(hint);
            }
        }

        (checker_visible_lrat_hints, complete)
    }

    fn checker_visible_materializer_lrat_hints(
        &self,
        record: &DecomposeProofEmitRecord,
    ) -> Vec<u64> {
        let mut checker_visible_lrat_hints = Vec::with_capacity(record.lrat_hints.len());
        let mut seen = det_hash_set_with_capacity(record.lrat_hints.len());

        for &hint in &record.lrat_hints {
            if hint != 0 && self.lrat_id_usable_as_hint(hint) && seen.insert(hint) {
                checker_visible_lrat_hints.push(hint);
            }
        }

        checker_visible_lrat_hints
    }

    fn materializer_record_is_complete(
        &self,
        record: &DecomposeProofEmitRecord,
        checker_visible_lrat_hints: &[u64],
    ) -> bool {
        record.proof_out_record_kind == DecomposeProofOutRecordKind::Add
            && record.proof_manager_mode == "lrat"
            && record.solver_runtime_emitted
            && !record.proof_writer_io_error
            && !record.lrat_hints.is_empty()
            && record.lrat_hints.len() == checker_visible_lrat_hints.len()
    }

    #[inline]
    fn proof_manager_mode_label(&self) -> &'static str {
        if self.lrat_mode {
            "lrat"
        } else {
            "drat"
        }
    }

    fn clause_lits_dimacs(clause: &[Literal]) -> Vec<i64> {
        clause
            .iter()
            .map(|lit| i64::from(lit.to_dimacs()))
            .collect()
    }

    fn file_visible_lrat_hints_for_observer(&self, hints: &[u64]) -> Vec<u64> {
        if !self.lrat_mode || hints.is_empty() || self.lrat_file_hints_are_clean(hints) {
            return hints.to_vec();
        }

        let mut file_hints = Vec::with_capacity(hints.len());
        let mut seen = det_hash_set_with_capacity(hints.len());
        for &hint in hints {
            if self.lrat_id_usable_as_hint(hint) && seen.insert(hint) {
                file_hints.push(hint);
            }
        }
        file_hints
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn emit_add_with_decompose_context(
        &mut self,
        clause: &[Literal],
        hints: &[u64],
        kind: ProofAddKind,
        context: &DecomposeProofEmitContext,
    ) -> io::Result<u64> {
        let added_before = self.output.added_count();
        let clause_id = self.emit_add(clause, hints, kind)?;
        if clause_id != 0 && self.output.added_count() > added_before {
            let lrat_hints = self.file_visible_lrat_hints_for_observer(hints);
            self.scoped_decompose_proof_emit_records
                .push(DecomposeProofEmitRecord {
                    context: context.clone(),
                    proof_field: "derived_clause_proof_steps",
                    proof_out_record_kind: DecomposeProofOutRecordKind::Add,
                    checker_visible_id: clause_id,
                    delete_source_id: None,
                    clause_lits_dimacs: Self::clause_lits_dimacs(clause),
                    lrat_hints,
                    proof_manager_mode: self.proof_manager_mode_label(),
                    solver_runtime_emitted: true,
                    proof_writer_io_error: self.output.has_io_error(),
                    external_checker_verified: false,
                });
        }
        Ok(clause_id)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn emit_delete_with_decompose_context(
        &mut self,
        clause: &[Literal],
        clause_id: u64,
        context: &DecomposeProofEmitContext,
    ) -> io::Result<()> {
        let deleted_before = self.output.deleted_count();
        self.emit_delete(clause, clause_id)?;
        if clause_id != 0 && self.output.deleted_count() > deleted_before {
            self.scoped_decompose_proof_emit_records
                .push(DecomposeProofEmitRecord {
                    context: context.clone(),
                    proof_field: "deletion_proof_steps",
                    proof_out_record_kind: DecomposeProofOutRecordKind::Delete,
                    checker_visible_id: clause_id,
                    delete_source_id: Some(clause_id),
                    clause_lits_dimacs: Self::clause_lits_dimacs(clause),
                    lrat_hints: Vec::new(),
                    proof_manager_mode: self.proof_manager_mode_label(),
                    solver_runtime_emitted: true,
                    proof_writer_io_error: self.output.has_io_error(),
                    external_checker_verified: false,
                });
        }
        Ok(())
    }

    #[inline]
    pub(crate) fn register_clause_id(&mut self, clause_id: u64) {
        if !self.lrat_mode || clause_id == 0 {
            return;
        }
        self.known_lrat_ids.insert(clause_id);
        if clause_id >= self.next_lrat_id {
            self.next_lrat_id = clause_id + 1;
        }
        // Keep the writer's counter past all original clause IDs so derived
        // clauses emitted via output.add() don't collide (#7108).
        self.output.advance_past(self.next_lrat_id);
        #[cfg(debug_assertions)]
        if let Some(ref mut lrat) = self.lrat_checker {
            if let Some(clause) = self.pending_originals.pop() {
                lrat.add_original(clause_id, &clause);
            }
        }
    }

    #[inline]
    pub(crate) fn register_original_clause(&mut self, _clause: &[Literal]) {
        #[cfg(debug_assertions)]
        self.checker.add_original(_clause);
        #[cfg(debug_assertions)]
        if self.lrat_checker.is_some() {
            self.pending_originals.push(_clause.to_vec());
        }
    }

    /// Emit a PR (propagation-redundant) clause addition as a DPR `a`-line
    /// (`clause… witness… 0`) — the symmetry-breaking lex-leader binary with its
    /// σ-image witness (#8011).
    ///
    /// SOUNDNESS: the internal RUP/RAT `ForwardChecker` CANNOT verify a PR clause,
    /// so this records the clause as a TrustedTransform with the debug checker (so
    /// later derived clauses that resolve against it are not spuriously rejected)
    /// and defers the actual PR verification to the EXTERNAL verified DPR/LPR
    /// checker (dpr-trim → cake_lpr). PR is a DRAT-family extension; the LRAT/LPR
    /// emission route is not wired, so this errors out in LRAT mode rather than
    /// write an unverifiable step (matching `ProofOutput::add_pr`).
    pub(crate) fn emit_add_pr(
        &mut self,
        clause: &[Literal],
        witness: &[Literal],
    ) -> io::Result<()> {
        debug_assert!(
            !self.lrat_mode,
            "BUG: PR/LPR emission attempted on the LRAT route (#8011 wires DPR only)"
        );
        #[cfg(debug_assertions)]
        self.checker.add_trusted_transform(clause);
        self.output.add_pr(clause, witness)
    }

    /// Emit a symmetry-breaking clause as a DSR `a`-line with its full
    /// substitution witness σ (#8011 SR route). Like [`Self::emit_add_pr`] this
    /// registers the clause as a TrustedTransform (the internal RUP/RAT checker
    /// cannot verify SR) and defers verification to the EXTERNAL `dsr-trim →
    /// drat/lsr → cake_lpr` chain. SR is a DRAT-family extension; the LSR/LRAT
    /// route is not wired, so this errors out in LRAT mode.
    pub(crate) fn emit_add_sr(
        &mut self,
        clause: &[Literal],
        witness: &[Literal],
    ) -> io::Result<()> {
        debug_assert!(
            !self.lrat_mode,
            "BUG: SR/LSR emission attempted on the LRAT route (#8011 wires DSR only)"
        );
        #[cfg(debug_assertions)]
        self.checker.add_trusted_transform(clause);
        self.output.add_sr(clause, witness)
    }

    /// DRAT additions written so far (soundness-triage instrumentation).
    pub(crate) fn proof_adds_written(&self) -> u64 {
        self.output.adds_written()
    }

    pub(crate) fn emit_add(
        &mut self,
        clause: &[Literal],
        hints: &[u64],
        mut kind: ProofAddKind,
    ) -> io::Result<u64> {
        debug_assert!(
            !clause.is_empty() || matches!(kind, ProofAddKind::Derived),
            "BUG: empty proof clause must be derived, got {kind:?}"
        );

        // Serialized LRAT has no "trusted transform" tag: every addition is
        // untrusted to a standalone checker. Keep the trusted classification
        // internally for malformed/missing-hint derived additions, but never
        // serialize it below without an actual hint chain.
        // Defense-in-depth: filter out sentinel ID 0 from hints before
        // validation and proof writing (#7957). Multiple hint-construction
        // paths can produce 0-valued entries when a clause has no assigned
        // LRAT ID (e.g., clause_id() returns 0 for unregistered clauses).
        // Some callers already filter (lrat_reverse_hints, BVE retain),
        // but not all do. Filtering here at the proof-manager boundary
        // prevents panics in release builds while preserving the
        // debug_assert in LratWriter::add for development visibility.
        debug_assert!(
            hints.iter().all(|&h| h != 0),
            "BUG: LRAT hints contain ID 0 (caller should filter) — \
             filtering defensively at proof-manager boundary"
        );
        let filtered_hints_buf: Vec<u64>;
        let hints = if self.lrat_mode && hints.contains(&0) {
            filtered_hints_buf = hints.iter().copied().filter(|&h| h != 0).collect();
            &filtered_hints_buf
        } else {
            hints
        };

        let missing_derived_hints =
            self.lrat_mode && matches!(kind, ProofAddKind::Derived) && hints.is_empty();
        if missing_derived_hints && clause.is_empty() {
            if let Some(last_add) = self.last_add {
                if last_add.is_empty && self.trusted_lrat_ids.contains(&last_add.id) {
                    // Repeated reports of the same unproved terminal clause
                    // must not consume a fresh hidden ID each time. Keep the
                    // proof failed closed while preserving solver ID stability.
                    self.lrat_structural_failure = true;
                    self.lrat_authority_fail_closed = true;
                    return Ok(last_add.id);
                }
            }
        }
        if missing_derived_hints {
            kind = ProofAddKind::TrustedTransform;
        }

        if self.lrat_mode && matches!(kind, ProofAddKind::Derived) {
            for &hint in hints {
                if !self.lrat_id_usable_as_hint(hint) {
                    self.lrat_structural_failure = true;
                    return Ok(0);
                }
            }
        }

        let mut suppress_lrat_write = false;
        #[cfg(debug_assertions)]
        match kind {
            ProofAddKind::Axiom => self.checker.add_original(clause),
            ProofAddKind::TrustedTransform => {
                // A missing-hint empty derivation is deliberately hidden and
                // fail-closed below. It is not a valid trusted-transform input
                // for the debug forward checker.
                if !clause.is_empty() {
                    self.checker.add_trusted_transform(clause);
                }
            }
            ProofAddKind::Derived => {
                if !hints.is_empty() && self.lrat_mode {
                    self.checker.add_original(clause);
                } else {
                    self.checker.add_derived(clause);
                }
            }
        }
        if self.lrat_mode
            && matches!(kind, ProofAddKind::Axiom)
            && hints.is_empty()
            && !clause.is_empty()
        {
            self.lrat_blocked_by_theory_lemmas = true;
            suppress_lrat_write = true;
        }
        if self.lrat_mode && hints.is_empty() && matches!(kind, ProofAddKind::Axiom) {
            // Suppress Axiom clauses with empty hints — these are theory
            // lemmas that the LRAT checker cannot verify (no resolution chain).
            suppress_lrat_write = true;
        }
        // Suppress every empty-hint TrustedTransform from LRAT output. LRAT
        // cannot encode the trust classification, and "usually RUP" is not a
        // proof: a standalone checker must verify every serialized addition.
        // Reserve a hidden ID so solver bookkeeping remains coherent and
        // downstream file-visible chains filter it out. Every such transform
        // latches the authority failure: even a hidden unit can change the
        // solver's semantic state without any standalone LRAT justification.
        if self.lrat_mode && matches!(kind, ProofAddKind::TrustedTransform) && hints.is_empty() {
            self.lrat_structural_failure = true;
            self.lrat_authority_fail_closed = true;
            let reserved_id = self.output.reserve_id();
            if reserved_id != 0 {
                self.known_lrat_ids.insert(reserved_id);
                self.trusted_lrat_ids.insert(reserved_id);
                self.next_lrat_id = reserved_id + 1;
                #[cfg(debug_assertions)]
                if let Some(ref mut lrat) = self.lrat_checker {
                    lrat.add_original(reserved_id, clause);
                }
            }
            self.last_add = Some(LastAdd::new(reserved_id, clause));
            return Ok(reserved_id);
        }
        if self.lrat_blocked_by_theory_lemmas() && !clause.is_empty() {
            suppress_lrat_write = true;
        }
        if suppress_lrat_write {
            if self.lrat_mode && !clause.is_empty() {
                self.output.reserve_id();
            }
            return Ok(0);
        }

        self.validate_lrat_hints(clause, hints, kind);

        // Deduplicate hint IDs for output (#5248), and filter out trusted
        // (suppressed) IDs (#6270) plus deleted IDs (#8488). Most emitted
        // chains are already file-safe; keep that path allocation-free.
        let clause_id =
            if self.lrat_mode && !hints.is_empty() && !self.lrat_file_hints_are_clean(hints) {
                let mut file_hints_buf = std::mem::take(&mut self.file_hints_buf);
                let mut file_hints_seen = std::mem::take(&mut self.file_hints_seen);
                file_hints_buf.clear();
                file_hints_seen.clear();
                self.collect_lrat_file_hints_for_output(
                    hints,
                    &mut file_hints_buf,
                    &mut file_hints_seen,
                );

                let add_result = self.output.add(clause, file_hints_buf.as_slice());
                file_hints_buf.clear();
                file_hints_seen.clear();
                self.file_hints_buf = file_hints_buf;
                self.file_hints_seen = file_hints_seen;
                add_result?
            } else {
                self.output.add(clause, hints)?
            };
        if self.lrat_mode && clause_id != 0 {
            self.known_lrat_ids.insert(clause_id);
            self.next_lrat_id = clause_id + 1;

            // Feed LRAT chain verifier with the emitted clause and checker_hints
            // (which keep trusted IDs — the online checker has those clauses).
            #[cfg(debug_assertions)]
            if let Some(ref mut lrat) = self.lrat_checker {
                match kind {
                    ProofAddKind::Derived => {
                        // All derived clauses are added as originals in the
                        // online checker (#7108, #6270). The online checker
                        // cannot reliably verify hint chains because:
                        // - Learned clauses are opaque originals in the checker
                        // - TrustedTransform clauses lack RUP derivation chains
                        // - Empty clause hints may reference clauses not in the
                        //   checker's DB (e.g., deleted during inprocessing)
                        //
                        // Full proof validation is done by the external LRAT
                        // checker (lrat-check) which sees the complete proof
                        // file. The online checker provides structural
                        // defense-in-depth (clause DB consistency) only.
                        lrat.add_original(clause_id, clause);
                    }
                    ProofAddKind::Axiom => lrat.add_original(clause_id, clause),
                    ProofAddKind::TrustedTransform => lrat.add_original(clause_id, clause),
                }
            }
        }
        self.last_add = Some(LastAdd::new(clause_id, clause));
        Ok(clause_id)
    }

    pub(crate) fn emit_add_signed_lrat_hints(
        &mut self,
        clause: &[Literal],
        hints: &[i64],
        kind: ProofAddKind,
    ) -> io::Result<u64> {
        debug_assert!(
            !clause.is_empty() || matches!(kind, ProofAddKind::Derived),
            "BUG: empty proof clause must be derived, got {kind:?}"
        );

        if hints.is_empty() || !self.lrat_mode {
            return self.emit_add(clause, &[], kind);
        }

        if let Err(reason) =
            self.preflight_forward_lrat_add_signed_with_planned_ids(clause, hints, kind, &[])
        {
            self.lrat_structural_failure = true;
            if matches!(
                reason,
                PlannedForwardAddReject::UnverifiedTrustedTransform
                    | PlannedForwardAddReject::DerivedMissingHints
            ) {
                self.lrat_authority_fail_closed = true;
            }
            return Ok(0);
        }

        #[cfg(debug_assertions)]
        match kind {
            ProofAddKind::Axiom => self.checker.add_original(clause),
            ProofAddKind::TrustedTransform => self.checker.add_trusted_transform(clause),
            ProofAddKind::Derived => {
                if !hints.is_empty() {
                    self.checker.add_original(clause);
                } else {
                    self.checker.add_derived(clause);
                }
            }
        }

        self.validate_signed_lrat_hints(hints);
        let clause_id = self.output.add_signed_lrat_hints(clause, hints)?;
        if clause_id != 0 {
            self.known_lrat_ids.insert(clause_id);
            self.next_lrat_id = clause_id + 1;

            #[cfg(debug_assertions)]
            if let Some(ref mut lrat) = self.lrat_checker {
                // The online checker is structural only here; external LRAT is
                // the authority for signed RAT witness validation.
                lrat.add_original(clause_id, clause);
            }
        }
        self.last_add = Some(LastAdd::new(clause_id, clause));
        Ok(clause_id)
    }

    #[inline]
    fn collect_lrat_file_hints_for_output(
        &self,
        hints: &[u64],
        file_hints_buf: &mut Vec<u64>,
        seen: &mut DetHashSet<u64>,
    ) {
        debug_assert!(file_hints_buf.is_empty());
        debug_assert!(seen.is_empty());
        file_hints_buf.reserve(hints.len());
        for &hint in hints {
            if self.lrat_id_usable_as_hint(hint) && seen.insert(hint) {
                file_hints_buf.push(hint);
            }
        }
    }

    #[inline]
    fn lrat_file_hints_are_clean(&self, hints: &[u64]) -> bool {
        const SMALL_HINT_CHAIN: usize = 8;
        if hints.len() > SMALL_HINT_CHAIN {
            return false;
        }
        for (pos, &hint) in hints.iter().enumerate() {
            if !self.lrat_id_usable_as_hint(hint) {
                return false;
            }
            if hints[..pos].contains(&hint) {
                return false;
            }
        }
        true
    }

    pub(crate) fn emit_delete(&mut self, clause: &[Literal], clause_id: u64) -> io::Result<()> {
        if self.lrat_blocked_by_theory_lemmas() {
            return Ok(());
        }
        if self.lrat_mode && clause_id == 0 {
            #[cfg(debug_assertions)]
            self.checker.delete_clause(clause);
            return Ok(());
        }

        if self.lrat_mode && clause_id != 0 && !self.known_lrat_ids.contains(clause_id) {
            // #8488: ID was already deleted from known_lrat_ids.
            // This happens when a clause's LRAT ID is consumed by a proof
            // deletion (e.g., during replacement or inprocessing) but the
            // arena slot retains the stale clause_ids[] mapping. A subsequent
            // deletion path reads the stale ID and attempts a second delete.
            //
            // This is benign: the clause was legitimately deleted from the
            // proof once. Skip the duplicate to avoid corrupting the proof
            // stream with a double-deletion of the same ID.
            #[cfg(debug_assertions)]
            debug_assert!(
                self.deleted_lrat_ids.contains(&clause_id),
                "BUG: deleting truly unknown LRAT clause ID {clause_id} \
                     (never registered, not previously deleted). \
                     next_lrat_id={}, known_count={}",
                self.next_lrat_id,
                self.known_lrat_ids.len(),
            );
            return Ok(());
        }
        #[cfg(debug_assertions)]
        if !clause.is_empty() {
            self.checker.delete_clause(clause);
        }
        // Backward-reserved clauses have no file-visible addition yet. Their
        // deletion is optional, and serializing it would either precede the
        // later backfill or refer to a clause that reconstruction never emits.
        // Keep the reservation so a reachable historical clause can still be
        // backfilled; successful emission makes it file-visible again.
        if self.lrat_mode && self.backward_reserved_ids.contains(clause_id) {
            self.remove_known_lrat_id(clause_id);
            #[cfg(debug_assertions)]
            self.deleted_lrat_ids.insert(clause_id);
            return Ok(());
        }
        // Trusted IDs were never written to the LRAT file (#6270).
        // Suppress the deletion line (external checker doesn't know about them)
        // but still update the online checker and internal tracking.
        if self.lrat_mode && self.trusted_lrat_ids.contains(&clause_id) {
            #[cfg(debug_assertions)]
            if let Some(ref mut lrat) = self.lrat_checker {
                lrat.delete(clause_id);
            }
            self.remove_known_lrat_id(clause_id);
            self.trusted_lrat_ids.remove(&clause_id);
            #[cfg(debug_assertions)]
            self.deleted_lrat_ids.insert(clause_id);
            return Ok(());
        }
        #[cfg(debug_assertions)]
        if let Some(ref mut lrat) = self.lrat_checker {
            if self.lrat_mode && clause_id != 0 {
                lrat.delete(clause_id);
            }
        }
        self.output.delete(clause, clause_id)?;
        if self.lrat_mode && clause_id != 0 {
            self.remove_known_lrat_id(clause_id);
            #[cfg(debug_assertions)]
            self.deleted_lrat_ids.insert(clause_id);
        }
        Ok(())
    }

    #[inline]
    fn remove_known_lrat_id(&mut self, clause_id: u64) {
        if self.known_lrat_ids.remove(clause_id) {
            self.known_lrat_ids_deleted_since_shrink =
                self.known_lrat_ids_deleted_since_shrink.saturating_add(1);
        }
    }

    /// Reserve an LRAT ID for backward reconstruction without writing to the
    /// proof file (#8105).
    ///
    /// During solving with backward LRAT reconstruction as the primary path,
    /// learned clauses need an ID for solver-internal tracking (clause_ids,
    /// deletion, etc.) but should NOT be written to the LRAT proof file yet.
    /// The backward reconstruction will write them post-UNSAT with proper hints.
    ///
    /// The reserved ID is registered in `known_lrat_ids` so that:
    /// - Deletion steps can reference it (emit_delete checks known_lrat_ids)
    /// - The ID counter stays monotonic
    pub(crate) fn reserve_lrat_id_for_backward(&mut self) -> u64 {
        if !self.lrat_mode {
            return 0;
        }
        let id = self.output.reserve_id();
        if id != 0 {
            self.known_lrat_ids.insert(id);
            self.backward_reserved_ids.insert(id);
            if id >= self.next_lrat_id {
                self.next_lrat_id = id + 1;
            }
        }
        id
    }

    pub(crate) fn record_fmla_learned_lrat_authority_fail_closed(
        &mut self,
        checker_visible_id: u64,
        clause: &[Literal],
        raw_resolution_chain: &[u64],
        lrat_hints: &[u64],
    ) {
        if !self.lrat_mode || checker_visible_id == 0 {
            return;
        }
        let (materializer_dependency_ids, source_clause_dependency_ids) =
            self.learned_lrat_materializer_dependencies(lrat_hints);
        self.learned_lrat_authority_records
            .push(LearnedLratAuthorityRecord {
                checker_visible_id,
                clause_lits_dimacs: Self::clause_lits_dimacs(clause),
                raw_resolution_chain: raw_resolution_chain.to_vec(),
                lrat_hints: lrat_hints.to_vec(),
                materializer_dependency_ids,
                source_clause_dependency_ids,
                proof_manager_mode: self.proof_manager_mode_label(),
                proof_out_emitted: false,
                proof_writer_io_error: self.output.has_io_error(),
                authority_status: LearnedLratAuthorityStatus::FailClosedMaterializer,
            });
    }

    fn learned_lrat_materializer_dependencies(
        &self,
        file_lrat_hints: &[u64],
    ) -> (Vec<u64>, Vec<u64>) {
        let mut materializer_dependency_ids = Vec::new();
        let mut materializer_seen = det_hash_set_with_capacity(file_lrat_hints.len());
        let mut source_clause_dependency_ids = Vec::new();
        let mut source_seen = det_hash_set_new();

        for &hint in file_lrat_hints {
            if hint == 0 || !materializer_seen.insert(hint) {
                continue;
            }
            let Some(record) = self
                .scoped_decompose_proof_emit_records
                .iter()
                .find(|record| record.checker_visible_id == hint)
            else {
                continue;
            };
            materializer_dependency_ids.push(hint);
            for &source_id in &record.lrat_hints {
                if source_id != 0 && source_seen.insert(source_id) {
                    source_clause_dependency_ids.push(source_id);
                }
            }
        }

        (materializer_dependency_ids, source_clause_dependency_ids)
    }

    /// Write a backward-reconstructed LRAT step to the proof file (#8105).
    ///
    /// Called during UNSAT finalization for each learned clause that is
    /// reachable from the empty clause. The step includes the clause's
    /// literals and LRAT hints (antecedent clause IDs).
    ///
    /// Unlike `emit_add`, this does NOT allocate a new ID -- the ID was
    /// already reserved during solving via `reserve_lrat_id_for_backward`.
    /// Instead, it writes the addition line using the pre-assigned ID.
    pub(crate) fn emit_backward_step(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[i64],
    ) -> io::Result<()> {
        if !self.lrat_mode || clause_id == 0 {
            return Ok(());
        }
        if self.lrat_blocked_by_theory_lemmas() {
            return Ok(());
        }
        // Skip clauses whose proof lines were already written during solving
        // (#8448). BVE resolvents and other inprocessing-derived clauses are
        // emitted via `emit_add` (forward path) and must NOT be re-emitted
        // by backward reconstruction. Only IDs reserved via
        // `reserve_lrat_id_for_backward` need backward emission.
        if !self.backward_reserved_ids.contains(clause_id) {
            return Ok(());
        }
        // A malformed backward step cannot be repaired by dropping individual
        // hints: doing so changes RAT witness groups and can turn an incomplete
        // certificate into a different proof. Suppress the whole step and
        // retain its reservation so finalization detects incompleteness.
        if let Err(reason) = self.preflight_forward_lrat_add_signed_with_planned_ids(
            clause,
            hints,
            ProofAddKind::Derived,
            &[],
        ) {
            self.lrat_structural_failure = true;
            if matches!(
                reason,
                PlannedForwardAddReject::DerivedMissingHints
                    | PlannedForwardAddReject::UnverifiedTrustedTransform
            ) {
                self.lrat_authority_fail_closed = true;
            }
            return Ok(());
        }

        self.validate_signed_lrat_hints(hints);
        if let Err(error) = self
            .output
            .add_with_id_signed_lrat_hints(clause_id, clause, hints)
        {
            self.lrat_structural_failure = true;
            return Err(error);
        }
        self.known_lrat_ids.insert(clause_id);
        self.backward_reserved_ids.remove(clause_id);
        Ok(())
    }

    /// Check whether a clause ID is currently known (not yet deleted) in the
    /// LRAT tracking set (#8448). Used by backward subsumption to filter out
    /// deferred deletions for clauses that were already deleted.
    #[inline]
    pub(crate) fn is_known_lrat_id(&self, clause_id: u64) -> bool {
        self.known_lrat_ids.contains(clause_id)
    }

    pub(crate) fn planned_forward_add_ids(
        &self,
        count: usize,
    ) -> Result<Vec<u64>, PlannedForwardAddReject> {
        if !self.lrat_mode {
            return Err(PlannedForwardAddReject::NotLrat);
        }
        if self.lrat_blocked_by_theory_lemmas() {
            return Err(PlannedForwardAddReject::LratBlocked);
        }
        if self.output.has_io_error() {
            return Err(PlannedForwardAddReject::IoFailed);
        }
        if self.output.has_pending_lrat_deletions() {
            return Err(PlannedForwardAddReject::PendingDeletions);
        }
        let Some(start) = self.output.next_lrat_id() else {
            return Err(PlannedForwardAddReject::NotLrat);
        };
        if start != self.next_lrat_id {
            return Err(PlannedForwardAddReject::OutputIdMismatch);
        }
        let end = start
            .checked_add(count as u64)
            .ok_or(PlannedForwardAddReject::IdOverflow)?;
        Ok((start..end).collect())
    }

    pub(crate) fn preflight_forward_lrat_add_with_planned_ids(
        &self,
        clause: &[Literal],
        hints: &[u64],
        kind: ProofAddKind,
        planned_visible_ids: &[u64],
    ) -> Result<(), PlannedForwardAddReject> {
        if !self.lrat_mode {
            return Err(PlannedForwardAddReject::NotLrat);
        }
        if self.lrat_blocked_by_theory_lemmas() {
            return Err(PlannedForwardAddReject::LratBlocked);
        }
        if self.output.has_io_error() {
            return Err(PlannedForwardAddReject::IoFailed);
        }
        if clause.is_empty() && !matches!(kind, ProofAddKind::Derived) {
            return Err(PlannedForwardAddReject::InvalidClause);
        }
        if matches!(kind, ProofAddKind::Axiom) && hints.is_empty() {
            return Err(PlannedForwardAddReject::SuppressedAxiom);
        }
        if matches!(kind, ProofAddKind::TrustedTransform) && hints.is_empty() {
            return Err(PlannedForwardAddReject::UnverifiedTrustedTransform);
        }
        if matches!(kind, ProofAddKind::Derived) && hints.is_empty() {
            return Err(PlannedForwardAddReject::DerivedMissingHints);
        }

        let mut seen = det_hash_set_with_capacity(hints.len());
        for &hint in hints {
            if hint == 0 {
                return Err(PlannedForwardAddReject::ZeroHint);
            }
            if !seen.insert(hint) {
                return Err(PlannedForwardAddReject::DuplicateHint);
            }
            let known_now = self.known_lrat_ids.contains(hint);
            let planned_visible = planned_visible_ids.contains(&hint);
            if !known_now && !planned_visible {
                return Err(PlannedForwardAddReject::UnknownHint);
            }
            if known_now && self.trusted_lrat_ids.contains(&hint) {
                return Err(PlannedForwardAddReject::TrustedHint);
            }
            if known_now && self.backward_reserved_ids.contains(hint) {
                return Err(PlannedForwardAddReject::BackwardReservedHint);
            }
        }

        Ok(())
    }

    pub(crate) fn preflight_forward_lrat_add_signed_with_planned_ids(
        &self,
        clause: &[Literal],
        hints: &[i64],
        kind: ProofAddKind,
        planned_visible_ids: &[u64],
    ) -> Result<(), PlannedForwardAddReject> {
        if !self.lrat_mode {
            return Err(PlannedForwardAddReject::NotLrat);
        }
        if self.lrat_blocked_by_theory_lemmas() {
            return Err(PlannedForwardAddReject::LratBlocked);
        }
        if self.output.has_io_error() {
            return Err(PlannedForwardAddReject::IoFailed);
        }
        if clause.is_empty() && !matches!(kind, ProofAddKind::Derived) {
            return Err(PlannedForwardAddReject::InvalidClause);
        }
        if matches!(kind, ProofAddKind::Axiom) && hints.is_empty() {
            return Err(PlannedForwardAddReject::SuppressedAxiom);
        }
        if matches!(kind, ProofAddKind::TrustedTransform) && hints.is_empty() {
            return Err(PlannedForwardAddReject::UnverifiedTrustedTransform);
        }
        if matches!(kind, ProofAddKind::Derived) && hints.is_empty() {
            return Err(PlannedForwardAddReject::DerivedMissingHints);
        }

        // Positive RUP hints are unique within their prefix or RAT witness
        // group. A helper clause may legitimately be reused by a later witness,
        // so a single global absolute-ID set would reject valid RAT chains.
        let mut positive_seen = det_hash_set_with_capacity(hints.len());
        let mut witness_seen = det_hash_set_with_capacity(hints.len());
        for &hint in hints {
            if hint == 0 {
                return Err(PlannedForwardAddReject::ZeroHint);
            }
            if hint == i64::MIN {
                return Err(PlannedForwardAddReject::IdOverflow);
            }
            let hint_id = hint.unsigned_abs();
            if hint < 0 {
                if !witness_seen.insert(hint_id) {
                    return Err(PlannedForwardAddReject::DuplicateHint);
                }
                positive_seen.clear();
            } else if !positive_seen.insert(hint_id) {
                return Err(PlannedForwardAddReject::DuplicateHint);
            }
            let known_now = self.known_lrat_ids.contains(hint_id);
            let planned_visible = planned_visible_ids.contains(&hint_id);
            if !known_now && !planned_visible {
                return Err(PlannedForwardAddReject::UnknownHint);
            }
            if known_now && self.trusted_lrat_ids.contains(&hint_id) {
                return Err(PlannedForwardAddReject::TrustedHint);
            }
            if known_now && self.backward_reserved_ids.contains(hint_id) {
                return Err(PlannedForwardAddReject::BackwardReservedHint);
            }
        }

        Ok(())
    }

    #[inline]
    pub(crate) fn flush(&mut self) -> io::Result<()> {
        let result = self.output.flush();
        if result.is_ok() {
            if let Some(next_id) = self.output.next_lrat_id() {
                if self.next_lrat_id < next_id {
                    self.next_lrat_id = next_id;
                }
            }
        }
        result
    }

    #[inline]
    pub(crate) fn added_count(&self) -> u64 {
        self.output.added_count()
    }

    #[cfg(test)]
    #[inline]
    pub(crate) fn deleted_count(&self) -> u64 {
        self.output.deleted_count()
    }

    #[inline]
    pub(crate) fn has_io_error(&self) -> bool {
        self.output.has_io_error() || self.lrat_structural_failure
    }

    #[inline]
    pub(crate) fn has_inprocessing_boundary_error(&self) -> bool {
        self.output.has_io_error()
            || (self.lrat_structural_failure && !self.lrat_authority_fail_closed)
    }

    pub(crate) fn mark_lrat_authority_fail_closed(&mut self) {
        self.lrat_authority_fail_closed = true;
    }

    #[inline]
    pub(crate) fn has_lrat_authority_fail_closed(&self) -> bool {
        self.lrat_authority_fail_closed
    }

    #[inline]
    pub(crate) fn lrat_failures(&self) -> u64 {
        #[cfg(debug_assertions)]
        if let Some(ref lrat) = self.lrat_checker {
            return lrat.failures();
        }
        0
    }

    /// Register a clause as an LRAT axiom in the checker (debug-only).
    ///
    /// Allocates an ID from `next_lrat_id` (the unified counter that tracks
    /// the maximum across original clause IDs and proof writer IDs) to avoid
    /// collisions with IDs assigned by `register_clause_id`. Then advances the
    /// writer's counter past this ID so subsequent `emit_add` calls produce
    /// non-conflicting IDs.
    ///
    /// Returns the allocated ID so callers can advance solver-side counters
    /// (next_original_clause_id, next_clause_id) to prevent collisions with
    /// subsequent original clause additions.
    ///
    /// Used by `push()` to register ¬selector as an LRAT axiom (#7108).
    #[cfg(debug_assertions)]
    pub(crate) fn register_lrat_axiom(&mut self, clause: &[Literal]) -> u64 {
        if !self.lrat_mode {
            return 0;
        }
        let id = self.next_lrat_id;
        self.next_lrat_id += 1;
        self.known_lrat_ids.insert(id);
        // Keep the writer's counter synchronized so subsequent proof steps
        // (via output.add()) don't reuse this ID.
        self.output.advance_past(self.next_lrat_id);
        if let Some(ref mut lrat) = self.lrat_checker {
            lrat.add_original(id, clause);
        }
        id
    }

    #[cfg(debug_assertions)]
    pub(crate) fn checker_live_clause_count(&self) -> usize {
        self.checker.live_clause_count()
    }

    #[inline]
    pub(crate) fn output(&self) -> &ProofOutput {
        &self.output
    }

    #[inline]
    pub(crate) fn output_mut(&mut self) -> &mut ProofOutput {
        &mut self.output
    }

    #[inline]
    pub(crate) fn into_output(self) -> ProofOutput {
        self.output
    }

    /// Clear the last-add record so that `verify_unsat_chain` only validates
    /// the current finalization's empty clause, not a stale entry from a
    /// previous solve cycle or from `pop()`'s selector-clause emission (#7175).
    pub(crate) fn clear_last_add(&mut self) {
        self.last_add = None;
    }

    /// Structural LRAT chain integrity check: verify all hints reference
    /// known, live clause IDs. Always-on in all builds (#5005).
    fn validate_lrat_hints(&self, clause: &[Literal], hints: &[u64], kind: ProofAddKind) {
        if !self.lrat_mode || self.lrat_blocked_by_theory_lemmas() {
            return;
        }
        if matches!(kind, ProofAddKind::Derived) {
            // Every Derived addition requires a real verification chain.
            // `emit_add` fail-closes and hides a missing-hint step before this
            // point; keep the assertion as development defense-in-depth.
            debug_assert!(
                !hints.is_empty(),
                "BUG: LRAT derived clause requires hints (clause len={})",
                clause.len()
            );
        }
        for &hint in hints {
            // Hint ID 0 is filtered at the emit_add boundary (#7957).
            // Keep as debug_assert for development visibility.
            debug_assert!(hint != 0, "BUG: LRAT hint contains clause ID 0");
            if hint == 0 {
                continue;
            }
            assert!(
                hint < self.next_lrat_id,
                "BUG: LRAT hint {hint} references future ID (next={})",
                self.next_lrat_id
            );
            if !self.known_lrat_ids.contains(hint) {
                // #8488: Hint references a clause that was deleted during
                // inprocessing. For TrustedTransform and non-derived clauses,
                // this is tolerable because external LRAT checkers don't
                // verify those hint chains. For Derived clauses, this would
                // produce an invalid proof if the deleted clause is essential
                // for the RUP derivation.
                //
                // Skip the stale hint rather than panicking. The external
                // LRAT checker will validate the remaining hints.
                #[cfg(debug_assertions)]
                {
                    let was_deleted = self.deleted_lrat_ids.contains(&hint);
                    debug_assert!(
                        was_deleted,
                        "BUG: LRAT hint {hint} references unknown clause \
                         (never registered, not previously deleted). \
                         kind={kind:?}, next_lrat_id={}, known_count={}",
                        self.next_lrat_id,
                        self.known_lrat_ids.len(),
                    );
                }
            }
        }
    }

    fn validate_signed_lrat_hints(&self, hints: &[i64]) {
        if !self.lrat_mode || self.lrat_blocked_by_theory_lemmas() {
            return;
        }
        for &hint in hints {
            debug_assert!(hint != 0, "BUG: signed LRAT hint contains clause ID 0");
            debug_assert!(
                hint != i64::MIN,
                "BUG: signed LRAT hint i64::MIN cannot be encoded"
            );
            if hint == 0 || hint == i64::MIN {
                continue;
            }
            let hint_id = hint.unsigned_abs();
            assert!(
                hint_id < self.next_lrat_id,
                "BUG: signed LRAT hint {hint} references future ID (next={})",
                self.next_lrat_id
            );
            if !self.known_lrat_ids.contains(hint_id) {
                #[cfg(debug_assertions)]
                {
                    let was_deleted = self.deleted_lrat_ids.contains(&hint_id);
                    debug_assert!(
                        was_deleted,
                        "BUG: signed LRAT hint {hint} references unknown clause \
                         (never registered, not previously deleted). \
                         next_lrat_id={}, known_count={}",
                        self.next_lrat_id,
                        self.known_lrat_ids.len(),
                    );
                }
            }
        }
    }

    /// Clear backward_reserved_ids after proof finalization (#8603).
    ///
    /// After backward proof emission completes (all `emit_backward_step` calls
    /// done), the set is dead data — no more backward steps will be emitted.
    /// Clearing it releases memory that would otherwise grow monotonically
    /// over long proofs.
    pub(crate) fn clear_backward_reserved_ids(&mut self) {
        self.backward_reserved_ids.clear_and_shrink();
    }

    /// Periodic cleanup of debug-only tracking sets (#8603).
    ///
    /// `deleted_lrat_ids` grows monotonically (every clause deletion adds to it).
    /// For long proofs this can consume hundreds of MB of genuinely dead diagnostic
    /// data. This method clears the set when it exceeds `threshold` entries.
    /// The set is diagnostic-only (used in debug_assert panic messages) — clearing
    /// it is safe and only reduces debug panic message quality for very old IDs.
    #[cfg(debug_assertions)]
    pub(crate) fn cleanup_debug_tracking(&mut self, threshold: usize) {
        if self.deleted_lrat_ids.len() > threshold {
            self.deleted_lrat_ids.clear();
            // `BTreeSet` (the `#[cfg(kani)]` backend) has no `shrink_to`; `clear`
            // already releases its nodes there.
            #[cfg(not(kani))]
            self.deleted_lrat_ids.shrink_to(0);
        }
    }

    /// Shrink `known_lrat_ids` capacity after batch deletions (#8603).
    ///
    /// This is the immediate shrink primitive. Prefer
    /// `shrink_known_ids_after_reduction` from normal reduction paths so the
    /// bitmap is not rebuilt after every ordinary reduce.
    pub(crate) fn shrink_known_ids(&mut self) {
        self.known_lrat_ids.shrink_to_fit();
        self.known_lrat_ids_deleted_since_shrink = 0;
    }

    /// Policy-gated live-ID cleanup for post-reduction calls.
    ///
    /// `LiveIdSet::shrink_to_fit` scans/rebuilds bitmap storage, so ordinary
    /// reduce cycles should not pay it unconditionally. Run it only when the
    /// caller is already at a memory/GC pressure point, and only if deletions
    /// actually removed LRAT IDs since the previous shrink.
    pub(crate) fn shrink_known_ids_after_reduction(&mut self, pressure: bool) {
        if !self.lrat_mode || !pressure || self.known_lrat_ids_deleted_since_shrink == 0 {
            return;
        }
        self.shrink_known_ids();
    }

    /// Post-UNSAT structural chain integrity check (#5005).
    ///
    /// Verifies the LRAT proof structure is consistent after finalization.
    /// This is an O(1) defense-in-depth check that runs in all builds.
    ///
    /// The per-emit `validate_lrat_hints` (always-on) checks each hint at
    /// emit time against `known_lrat_ids`, ensuring all hints reference
    /// known, live clause IDs. Combined with the monotonic ID invariant
    /// (`hint < next_lrat_id`), this guarantees every derivation chain
    /// terminates at original clauses (axioms). This method catches
    /// systemic issues at the proof boundary:
    ///
    /// 1. Empty ID tracking set (broken registration)
    /// 2. ID counter never advanced (no clauses emitted)
    /// 3. Last emitted clause was not the empty clause (incomplete proof)
    pub(crate) fn try_verify_unsat_chain(&self) -> Result<(), &'static str> {
        if !self.lrat_mode || self.lrat_blocked_by_theory_lemmas() {
            return Ok(());
        }
        // The known_lrat_ids set must contain at least the original clauses
        // that were not deleted during solving. An empty set means tracking
        // was broken or all clauses were deleted (which is invalid — the
        // empty clause derivation requires at least some axioms).
        if self.known_lrat_ids.is_empty() {
            return Err("LRAT ID tracking empty after UNSAT");
        }
        // next_lrat_id must have advanced past the initial value.
        if self.next_lrat_id <= 1 {
            return Err("LRAT next_id never advanced");
        }
        // The last emitted addition must be the empty clause. An UNSAT proof
        // that doesn't end with an empty clause derivation is structurally
        // invalid — the proof manager may have been corrupted or the
        // finalization sequence was incomplete.
        match self.last_add {
            Some(last_add) if last_add.is_empty => Ok(()),
            Some(_) => Err("LRAT proof did not end with empty clause"),
            None => Ok(()),
        }
    }

    #[cfg(test)]
    pub(crate) fn verify_unsat_chain(&self) {
        if let Err(reason) = self.try_verify_unsat_chain() {
            panic!("BUG: {reason}");
        }
    }
}
