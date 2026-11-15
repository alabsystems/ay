// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bv_blast_export::BvBlastValidateLimits;
use crate::bv_blast_solver::BvExprProofLimits;
use ay_sat::{ResolutionProofLimits, ResolutionValidationLimits};

// Explicit finite test grants. No private production constructor or defaults.
pub(super) fn proof_limits(deadline: Instant) -> (BvExprProofLimits, BvBlastValidateLimits) {
    let validation = ResolutionValidationLimits {
        deadline: Some(deadline),
        max_original_clauses: 16_000,
        max_original_literals: 64_000,
        max_derived_steps: 100,
        max_derived_literals: 10_000,
        max_hints: 10_000,
        max_work: 1_000_000,
        max_bytes: 8 * 1024 * 1024,
    };
    let resolution = ResolutionProofLimits {
        deadline: Some(deadline),
        max_num_vars: 4096,
        max_input_clauses: 16_000,
        max_input_literals: 64_000,
        max_input_clause_literals: 64,
        max_input_bytes: 8 * 1024 * 1024,
        max_conflicts: Some(0),
        max_decisions: Some(0),
        solver_clause_db_reduction_threshold_bytes: 8 * 1024 * 1024,
        max_proof_output_bytes: 8 * 1024 * 1024,
        max_derived_steps: 100,
        max_derived_literals: 10_000,
        max_hints: 10_000,
        max_pending_deletions: 100,
        max_codec_bytes: 8 * 1024 * 1024,
        max_backward_reconstruction_bytes: 8 * 1024 * 1024,
        validation,
    };
    let proof = BvExprProofLimits {
        sweep: false,
        max_expr_nodes: 4096,
        max_expr_occurrences: 100_000,
        max_expr_depth: 512,
        max_leaf_name_bytes: 1024 * 1024,
        max_internal_width: 128,
        max_estimated_gate_work: 100_000,
        max_construction_bytes: 8 * 1024 * 1024,
        max_resolution_steps: 100,
        max_expanded_literals: 10_000,
        max_expansion_work: 1_000_000,
        max_expansion_bytes: 8 * 1024 * 1024,
        resolution,
    };
    let gates = BvBlastValidateLimits {
        deadline: Some(deadline),
        max_vars: 4096,
        max_bit_lemmas: 4096,
        max_clauses: 16_000,
        max_clause_literals: 64,
        max_original_literals: 64_000,
        max_resolution_steps: 100,
        max_derived_literals: 10_000,
        max_work: 1_000_000,
    };
    (proof, gates)
}
