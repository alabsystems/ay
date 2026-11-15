// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exhaustive resource-bound identity for the per-thread refutation memo.

use ay_sat::{ResolutionProofLimits, ResolutionValidationLimits};

/// Every resource bound of a [`ResolutionProofLimits`] except its two
/// wall-clock deadlines.
///
/// Construction is exhaustive on purpose: see the module docs.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct LimitsKey {
    max_num_vars: usize,
    max_input_clauses: usize,
    max_input_literals: usize,
    max_input_clause_literals: usize,
    max_input_bytes: usize,
    max_conflicts: Option<u64>,
    max_decisions: Option<u64>,
    solver_clause_db_reduction_threshold_bytes: usize,
    max_proof_output_bytes: usize,
    max_derived_steps: usize,
    max_derived_literals: usize,
    max_hints: usize,
    max_pending_deletions: usize,
    max_codec_bytes: usize,
    max_backward_reconstruction_bytes: usize,
    validation_max_original_clauses: usize,
    validation_max_original_literals: usize,
    validation_max_derived_steps: usize,
    validation_max_derived_literals: usize,
    validation_max_hints: usize,
    validation_max_work: u64,
    validation_max_bytes: usize,
}

impl LimitsKey {
    pub(super) fn of(limits: &ResolutionProofLimits) -> Self {
        // Destructured with NO rest pattern. A new limit field must be routed
        // into the key here, or this stops compiling.
        let ResolutionProofLimits {
            deadline: _,
            max_num_vars,
            max_input_clauses,
            max_input_literals,
            max_input_clause_literals,
            max_input_bytes,
            max_conflicts,
            max_decisions,
            solver_clause_db_reduction_threshold_bytes,
            max_proof_output_bytes,
            max_derived_steps,
            max_derived_literals,
            max_hints,
            max_pending_deletions,
            max_codec_bytes,
            max_backward_reconstruction_bytes,
            validation,
        } = limits;
        let ResolutionValidationLimits {
            deadline: _,
            max_original_clauses: validation_max_original_clauses,
            max_original_literals: validation_max_original_literals,
            max_derived_steps: validation_max_derived_steps,
            max_derived_literals: validation_max_derived_literals,
            max_hints: validation_max_hints,
            max_work: validation_max_work,
            max_bytes: validation_max_bytes,
        } = validation;
        Self {
            max_num_vars: *max_num_vars,
            max_input_clauses: *max_input_clauses,
            max_input_literals: *max_input_literals,
            max_input_clause_literals: *max_input_clause_literals,
            max_input_bytes: *max_input_bytes,
            max_conflicts: *max_conflicts,
            max_decisions: *max_decisions,
            solver_clause_db_reduction_threshold_bytes: *solver_clause_db_reduction_threshold_bytes,
            max_proof_output_bytes: *max_proof_output_bytes,
            max_derived_steps: *max_derived_steps,
            max_derived_literals: *max_derived_literals,
            max_hints: *max_hints,
            max_pending_deletions: *max_pending_deletions,
            max_codec_bytes: *max_codec_bytes,
            max_backward_reconstruction_bytes: *max_backward_reconstruction_bytes,
            validation_max_original_clauses: *validation_max_original_clauses,
            validation_max_original_literals: *validation_max_original_literals,
            validation_max_derived_steps: *validation_max_derived_steps,
            validation_max_derived_literals: *validation_max_derived_literals,
            validation_max_hints: *validation_max_hints,
            validation_max_work: *validation_max_work,
            validation_max_bytes: *validation_max_bytes,
        }
    }
}
