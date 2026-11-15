// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Sort, Symbol};
use ay_sat::{ResolutionProofLimits, ResolutionValidationLimits};
use std::{cell::Cell, time::Duration};

mod controls;
mod metered_bridge;
mod outside;
mod replay;
mod specialized;

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

// Explicit test-owned grants, not a production default or renewed allowance.
fn limits(deadline: Instant) -> (BvExprProofLimits, BvBlastValidateLimits) {
    let validation = ResolutionValidationLimits {
        deadline: Some(deadline),
        max_original_clauses: 16_000,
        max_original_literals: 64_000,
        max_derived_steps: 4096,
        max_derived_literals: 64_000,
        max_hints: 64_000,
        max_work: 50_000_000,
        max_bytes: 128 * 1024 * 1024,
    };
    let resolution = ResolutionProofLimits {
        deadline: Some(deadline),
        max_num_vars: 4096,
        max_input_clauses: 16_000,
        max_input_literals: 64_000,
        max_input_clause_literals: 64,
        max_input_bytes: 16 * 1024 * 1024,
        max_conflicts: Some(250_000),
        max_decisions: Some(2_000_000),
        solver_clause_db_reduction_threshold_bytes: 16 * 1024 * 1024,
        max_proof_output_bytes: 16 * 1024 * 1024,
        max_derived_steps: 4096,
        max_derived_literals: 64_000,
        max_hints: 64_000,
        max_pending_deletions: 4096,
        max_codec_bytes: 128 * 1024 * 1024,
        max_backward_reconstruction_bytes: 16 * 1024 * 1024,
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
        max_construction_bytes: 128 * 1024 * 1024,
        max_resolution_steps: 4096,
        max_expanded_literals: 2_000_000,
        max_expansion_work: 50_000_000,
        max_expansion_bytes: 128 * 1024 * 1024,
        resolution,
    };
    let gates = BvBlastValidateLimits {
        deadline: Some(deadline),
        max_vars: 4096,
        max_bit_lemmas: 4096,
        max_clauses: 16_000,
        max_clause_literals: 64,
        max_original_literals: 64_000,
        max_resolution_steps: 4096,
        max_derived_literals: 64_000,
        max_work: 50_000_000,
    };
    (proof, gates)
}

fn app(terms: &mut TermStore, op: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(op), args, sort)
}

/// `(= (= (bvadd a b) constant) (= a (bvneg b)))`: valid at zero, a
/// refutation of several rows. A sum of two words, so no offset-equality
/// reading (`offset_equality.rs`) collapses its two sides into one lowering;
/// `(= (bvsub a b) 0)` against `(= a b)` now lowers both to the same `Eq`.
fn equality(terms: &mut TermStore, a: TermId, b: TermId, constant: TermId) -> TermId {
    let sum = app(terms, "bvadd", &[a, b], Sort::bitvec(8));
    let zero_test = app(terms, "=", &[sum, constant], Sort::Bool);
    let negated = app(terms, "bvneg", &[b], Sort::bitvec(8));
    let opposite = app(terms, "=", &[a, negated], Sort::Bool);
    app(terms, "=", &[zero_test, opposite], Sort::Bool)
}

fn arithmetic(constant: u32) -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("retained_a", Sort::bitvec(8));
    let b = terms.mk_var("retained_b", Sort::bitvec(8));
    let constant = terms.mk_bitvec(constant.into(), 8);
    let clause = equality(&mut terms, a, b, constant);
    (terms, clause)
}

fn identity() -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("retained_identity", Sort::bitvec(9));
    let zero = terms.mk_bitvec(0.into(), 9);
    let sum = app(&mut terms, "bvadd", &[a, zero], Sort::bitvec(9));
    let clause = app(&mut terms, "=", &[a, sum], Sort::Bool);
    (terms, clause)
}

fn capture(terms: &TermStore, clause: TermId) -> RetainedBvRefutation {
    let end = deadline();
    let (proof, gates) = limits(end);
    capture_clause(terms, &[clause], end, &proof, &gates, &mut || true).unwrap()
}

fn replay(
    terms: &TermStore,
    clause: TermId,
    payload: Option<&RetainedBvRefutation>,
) -> Result<(), BridgeError> {
    let end = deadline();
    let (mut proof, gates) = limits(end);
    proof.resolution.max_conflicts = Some(0);
    proof.resolution.max_decisions = Some(0);
    proof.resolution.max_backward_reconstruction_bytes = 0;
    proof.resolution.max_pending_deletions = 0;
    replay_clause(terms, &[clause], payload, end, &proof, &gates, &mut || true)
}

fn separate_derived_ids(payload: &mut RetainedBvRefutation) {
    let first = payload.rows[0].id;
    for row in &mut payload.rows {
        row.id = row.id.checked_add(1_000_000).unwrap();
        for hint in &mut row.hints {
            if *hint >= first {
                *hint = hint.checked_add(1_000_000).unwrap();
            }
        }
    }
    payload.empty_clause_id = payload.empty_clause_id.checked_add(1_000_000).unwrap();
}
