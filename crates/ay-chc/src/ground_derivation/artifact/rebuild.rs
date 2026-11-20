// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reuse identities authenticated from the same immutably borrowed source.
//!
//! This private token is not proof authority. Readers must still canonicalize
//! the reconstructed values and independently validate the native derivation.
//! It only avoids rehashing/revalidating the source inside the wire round trip.

use super::*;
#[cfg(test)]
use crate::proof_metadata::normalized_chc_input_sha256_with_progress;
use crate::proof_metadata::{
    normalized_chc_input_identity_with_progress, ordered_chc_clause_sequence_sha256_with_progress,
    wire_sort::WireSort, IdentityHashInterrupted,
};

pub(super) struct AuthenticatedSource<'a> {
    problem: &'a ChcProblem,
    normalized_input_schema: &'static str,
    normalized_input_sha256: String,
    source_clause_sequence_sha256: String,
}

fn interrupted(_: IdentityHashInterrupted) -> ChcGroundDerivationArtifactError {
    interruption_error(GroundValidationInterrupted)
}

fn sort_error(err: ay_core::original_query::QueryError) -> ChcGroundDerivationArtifactError {
    match err {
        ay_core::original_query::QueryError::Interrupted(_) => {
            interruption_error(GroundValidationInterrupted)
        }
        ay_core::original_query::QueryError::Invalid(detail) => error(
            ChcGroundDerivationArtifactErrorReason::InvalidSourceProblem,
            detail,
        ),
        ay_core::original_query::QueryError::Exhausted => error(
            ChcGroundDerivationArtifactErrorReason::SourceWorkLimitExceeded,
            "whole-problem canonical sort exceeds work bound",
        ),
    }
}

pub(super) fn normalized_source(
    problem: &ChcProblem,
    budget: &mut Option<usize>,
    control: &mut GroundValidationControl<'_>,
) -> Result<(&'static str, String), ChcGroundDerivationArtifactError> {
    let mut poll = || control.poll().is_ok();
    match budget {
        Some(remaining) => WireSort {
            remaining,
            progress: &mut poll,
        }
        .normalized(problem)
        .map_err(sort_error),
        None => {
            normalized_chc_input_identity_with_progress(problem, &mut poll).map_err(interrupted)
        }
    }
}

pub(super) fn ordered_source(
    problem: &ChcProblem,
    budget: &mut Option<usize>,
    control: &mut GroundValidationControl<'_>,
) -> Result<String, ChcGroundDerivationArtifactError> {
    let mut poll = || control.poll().is_ok();
    match budget {
        Some(remaining) => WireSort {
            remaining,
            progress: &mut poll,
        }
        .ordered(problem)
        .map_err(sort_error),
        None => ordered_chc_clause_sequence_sha256_with_progress(problem, &mut poll)
            .map_err(interrupted),
    }
}

impl<'a> AuthenticatedSource<'a> {
    pub(super) fn check(
        problem: &'a ChcProblem,
        normalized_input_schema: &str,
        normalized_input_sha256: &str,
        source_clause_sequence_sha256: &str,
        artifact_label: &str,
        mut budget: Option<usize>,
        control: &mut GroundValidationControl<'_>,
    ) -> Result<Self, ChcGroundDerivationArtifactError> {
        let (expected_schema, expected_problem_hash) =
            normalized_source(problem, &mut budget, control)?;
        // Keep normalized-input mismatch ahead of both computation and checking
        // of the positional hash, including when the caller budget is expiring.
        if normalized_input_sha256 != expected_problem_hash {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::ProblemHashMismatch,
                format!(
                    "{artifact_label} normalized-input hash does not match the supplied problem"
                ),
            ));
        }
        // The hashed text names its schema on its first line, so a label that
        // disagrees with an authenticated hash was rewritten after hashing.
        if normalized_input_schema != expected_schema {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::SchemaMismatch,
                format!(
                    "{artifact_label} normalized-input schema `{normalized_input_schema}` is not \
                     the supplied problem's `{expected_schema}`"
                ),
            ));
        }
        let expected_clause_hash = ordered_source(problem, &mut budget, control)?;
        if source_clause_sequence_sha256 != expected_clause_hash {
            return Err(error(
                ChcGroundDerivationArtifactErrorReason::ClauseSequenceHashMismatch,
                format!("{artifact_label} source-clause sequence hash does not match the supplied problem"),
            ));
        }
        control.poll().map_err(interruption_error)?;
        Ok(Self {
            problem,
            normalized_input_schema: expected_schema,
            normalized_input_sha256: expected_problem_hash,
            source_clause_sequence_sha256: expected_clause_hash,
        })
    }

    pub(super) fn rebuild_v1(
        &self,
        derivation: &GroundDerivation,
        control: &mut GroundValidationControl<'_>,
    ) -> Result<GroundDerivationEnvelope, ChcGroundDerivationArtifactError> {
        let (steps, counts) =
            wire_steps_from_derivation_with_control(self.problem, derivation, control)?;
        control.poll().map_err(interruption_error)?;
        GroundDerivationEnvelope::from_parts(
            steps,
            counts,
            derivation.query_step,
            self.normalized_input_schema,
            self.normalized_input_sha256.clone(),
            self.source_clause_sequence_sha256.clone(),
        )
    }

    pub(super) fn rebuild_v2(
        &self,
        derivation: &GroundDerivation,
        control: &mut GroundValidationControl<'_>,
    ) -> Result<GroundDerivationEnvelopeV2, ChcGroundDerivationArtifactError> {
        let (steps, counts) =
            wire_steps_v2_from_derivation_with_control(self.problem, derivation, control)?;
        control.poll().map_err(interruption_error)?;
        GroundDerivationEnvelopeV2::from_parts(
            steps,
            counts,
            derivation.query_step,
            self.normalized_input_schema,
            self.normalized_input_sha256.clone(),
            self.source_clause_sequence_sha256.clone(),
        )
    }
}

impl GroundDerivationEnvelope {
    pub(super) fn from_parts(
        steps: Vec<WireStep>,
        counts: ContentCounts,
        query_step: usize,
        normalized_input_schema: &'static str,
        normalized_input_sha256: String,
        source_clause_sequence_sha256: String,
    ) -> Result<Self, ChcGroundDerivationArtifactError> {
        Ok(Self {
            schema: CHC_GROUND_DERIVATION_ARTIFACT_SCHEMA.to_string(),
            schema_version: 1,
            role: CHC_GROUND_DERIVATION_ARTIFACT_ROLE.to_string(),
            normalized_input_schema: normalized_input_schema.to_string(),
            normalized_input_sha256,
            source_clause_sequence_sha256,
            step_count: checked_u64(steps.len(), "step count")?,
            query_step: checked_u32(query_step, "query step")?,
            premise_edge_count: checked_u64(counts.premise_edges, "premise edge count")?,
            binding_count: checked_u64(counts.bindings, "binding count")?,
            value_node_count: checked_u64(counts.value_nodes, "value node count")?,
            steps,
        })
    }
}

impl GroundDerivationEnvelopeV2 {
    pub(super) fn from_parts(
        steps: Vec<WireStepV2>,
        counts: ContentCounts,
        query_step: usize,
        normalized_input_schema: &'static str,
        normalized_input_sha256: String,
        source_clause_sequence_sha256: String,
    ) -> Result<Self, ChcGroundDerivationArtifactError> {
        Ok(Self {
            schema: CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA.to_string(),
            schema_version: 2,
            role: CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE.to_string(),
            normalized_input_schema: normalized_input_schema.to_string(),
            normalized_input_sha256,
            source_clause_sequence_sha256,
            step_count: checked_u64(steps.len(), "step count")?,
            query_step: checked_u32(query_step, "query step")?,
            premise_edge_count: checked_u64(counts.premise_edges, "premise edge count")?,
            binding_count: checked_u64(counts.bindings, "binding count")?,
            uf_observation_count: checked_u64(counts.uf_observations, "UF observation count")?,
            value_node_count: checked_u64(counts.value_nodes, "value node count")?,
            steps,
        })
    }
}

#[cfg(test)]
mod tests;
