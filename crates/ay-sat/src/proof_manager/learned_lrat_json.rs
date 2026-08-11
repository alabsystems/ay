// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Serialization helpers for learned-clause LRAT replay artifacts.

use super::{
    LearnedLratDryRunProofArtifactImportReject, LearnedLratMaterializationStatus,
    LearnedLratProofOutAppendReject, LearnedLratReplayRow, LearnedLratReplayRowKind, ProofManager,
};
use crate::Literal;
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::fmt::Write as _;

impl ProofManager {
    pub(super) fn serialize_lrat_add_line(row: &LearnedLratReplayRow) -> String {
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

    pub(super) fn learned_lrat_replay_row_kind_to_str(
        kind: LearnedLratReplayRowKind,
    ) -> &'static str {
        match kind {
            LearnedLratReplayRowKind::MaterializerAdd => "materializer_add",
            LearnedLratReplayRowKind::LearnedAdd => "learned_add",
        }
    }

    pub(super) fn learned_lrat_replay_row_kind_from_str(
        value: &str,
    ) -> Option<LearnedLratReplayRowKind> {
        match value {
            "materializer_add" => Some(LearnedLratReplayRowKind::MaterializerAdd),
            "learned_add" => Some(LearnedLratReplayRowKind::LearnedAdd),
            _ => None,
        }
    }

    pub(super) fn learned_lrat_materialization_status_to_str(
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

    pub(super) fn learned_lrat_materialization_status_from_str(
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

    pub(super) fn json_required_str<'a>(
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

    pub(super) fn json_required_u64(
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

    pub(super) fn json_required_bool(
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

    pub(super) fn json_required_i64_array(
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

    pub(super) fn json_required_u64_array(
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

    pub(super) fn json_string(value: &Value, field: &'static str) -> Option<String> {
        value.get(field)?.as_str().map(str::to_string)
    }

    pub(super) fn json_string_array(value: &Value, field: &'static str) -> Option<Vec<String>> {
        value
            .get(field)?
            .as_array()?
            .iter()
            .map(|item| item.as_str().map(str::to_string))
            .collect()
    }

    pub(super) fn clause_from_dimacs_i64(
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

    pub(super) fn sha256_hex(bytes: &[u8]) -> String {
        let digest = Sha256::digest(bytes);
        let mut hex = String::with_capacity(64);
        for byte in digest {
            let _ = write!(&mut hex, "{byte:02x}");
        }
        hex
    }
}
