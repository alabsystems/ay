// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_sat::{ResolutionProofLimits, ResolutionValidationLimits};

fn optional<T: Ord + Copy>(a: Option<T>, b: Option<T>) -> Option<T> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}

/// Child knobs can only narrow the root grants, including optional ceilings.
/// Search/construction remain separate caps, not measured ledger work.
///
/// Every limit is built as an exhaustive struct literal, so a field added to
/// any of these limit types fails to compile here until it is narrowed too:
/// a child can never inherit an un-intersected cap from its own request.
pub(super) fn child(
    root: &BvExprProofLimits,
    root_gates: &BvBlastValidateLimits,
    child: &BvExprProofLimits,
    child_gates: &BvBlastValidateLimits,
    end: Instant,
) -> (BvExprProofLimits, BvBlastValidateLimits) {
    let mut proof = BvExprProofLimits {
        max_expr_nodes: child.max_expr_nodes.min(root.max_expr_nodes),
        max_expr_occurrences: child.max_expr_occurrences.min(root.max_expr_occurrences),
        max_expr_depth: child.max_expr_depth.min(root.max_expr_depth),
        max_leaf_name_bytes: child.max_leaf_name_bytes.min(root.max_leaf_name_bytes),
        max_internal_width: child.max_internal_width.min(root.max_internal_width),
        max_estimated_gate_work: child
            .max_estimated_gate_work
            .min(root.max_estimated_gate_work),
        max_construction_bytes: child
            .max_construction_bytes
            .min(root.max_construction_bytes),
        max_resolution_steps: child.max_resolution_steps.min(root.max_resolution_steps),
        max_expanded_literals: child.max_expanded_literals.min(root.max_expanded_literals),
        max_expansion_work: child.max_expansion_work.min(root.max_expansion_work),
        max_expansion_bytes: child.max_expansion_bytes.min(root.max_expansion_bytes),
        resolution: resolution(&child.resolution, &root.resolution),
        // A swept retry is an extra attempt; a child may drop it, never add it.
        sweep: child.sweep && root.sweep,
    };
    let mut gates = BvBlastValidateLimits {
        deadline: optional(child_gates.deadline, root_gates.deadline),
        max_vars: child_gates.max_vars.min(root_gates.max_vars),
        max_bit_lemmas: child_gates.max_bit_lemmas.min(root_gates.max_bit_lemmas),
        max_clauses: child_gates.max_clauses.min(root_gates.max_clauses),
        max_clause_literals: child_gates
            .max_clause_literals
            .min(root_gates.max_clause_literals),
        max_original_literals: child_gates
            .max_original_literals
            .min(root_gates.max_original_literals),
        max_resolution_steps: child_gates
            .max_resolution_steps
            .min(root_gates.max_resolution_steps),
        max_derived_literals: child_gates
            .max_derived_literals
            .min(root_gates.max_derived_literals),
        max_work: child_gates.max_work.min(root_gates.max_work),
    };
    let end = [
        proof.resolution.deadline,
        proof.resolution.validation.deadline,
        gates.deadline,
    ]
    .into_iter()
    .flatten()
    .fold(end, Instant::min);
    install(&mut proof, &mut gates, end);
    (proof, gates)
}

fn resolution(
    child: &ResolutionProofLimits,
    root: &ResolutionProofLimits,
) -> ResolutionProofLimits {
    ResolutionProofLimits {
        deadline: optional(child.deadline, root.deadline),
        max_num_vars: child.max_num_vars.min(root.max_num_vars),
        max_input_clauses: child.max_input_clauses.min(root.max_input_clauses),
        max_input_literals: child.max_input_literals.min(root.max_input_literals),
        max_input_clause_literals: child
            .max_input_clause_literals
            .min(root.max_input_clause_literals),
        max_input_bytes: child.max_input_bytes.min(root.max_input_bytes),
        max_conflicts: optional(child.max_conflicts, root.max_conflicts),
        max_decisions: optional(child.max_decisions, root.max_decisions),
        solver_clause_db_reduction_threshold_bytes: child
            .solver_clause_db_reduction_threshold_bytes
            .min(root.solver_clause_db_reduction_threshold_bytes),
        max_proof_output_bytes: child
            .max_proof_output_bytes
            .min(root.max_proof_output_bytes),
        max_derived_steps: child.max_derived_steps.min(root.max_derived_steps),
        max_derived_literals: child.max_derived_literals.min(root.max_derived_literals),
        max_hints: child.max_hints.min(root.max_hints),
        max_pending_deletions: child.max_pending_deletions.min(root.max_pending_deletions),
        max_codec_bytes: child.max_codec_bytes.min(root.max_codec_bytes),
        max_backward_reconstruction_bytes: child
            .max_backward_reconstruction_bytes
            .min(root.max_backward_reconstruction_bytes),
        validation: validation(&child.validation, &root.validation),
    }
}

fn validation(
    child: &ResolutionValidationLimits,
    root: &ResolutionValidationLimits,
) -> ResolutionValidationLimits {
    ResolutionValidationLimits {
        deadline: optional(child.deadline, root.deadline),
        max_original_clauses: child.max_original_clauses.min(root.max_original_clauses),
        max_original_literals: child.max_original_literals.min(root.max_original_literals),
        max_derived_steps: child.max_derived_steps.min(root.max_derived_steps),
        max_derived_literals: child.max_derived_literals.min(root.max_derived_literals),
        max_hints: child.max_hints.min(root.max_hints),
        max_work: child.max_work.min(root.max_work),
        max_bytes: child.max_bytes.min(root.max_bytes),
    }
}

pub(super) fn install(
    proof: &mut BvExprProofLimits,
    gates: &mut BvBlastValidateLimits,
    end: Instant,
) {
    proof.resolution.deadline = Some(end);
    proof.resolution.validation.deadline = Some(end);
    gates.deadline = Some(end);
}
