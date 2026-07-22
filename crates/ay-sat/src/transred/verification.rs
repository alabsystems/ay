// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani verification harnesses for transitive reduction.

use super::*;
use crate::clause_arena::HEADER_WORDS;
use crate::test_util::lit;

// Generation value used in kani proofs to simulate "current round"
const GEN: u32 = 1;

fn assert_witness_validity(
    witness_ctx: &WitnessContext<'_>,
    pending_delete: &[u32],
    expected: &[(usize, bool)],
) {
    for (clause_idx, should_be_valid) in expected {
        let is_valid =
            TransRed::is_valid_witness_clause(*clause_idx, witness_ctx, pending_delete, GEN);
        assert_eq!(
            is_valid, *should_be_valid,
            "unexpected witness validity for clause {}",
            clause_idx
        );
    }
}

/// Regression-proof for #3312:
/// if one duplicate is marked pending-delete, the sibling duplicate stays
/// as the only valid witness. This models the post-condition required to
/// avoid deleting both duplicates in one transred round.
///
/// Rewritten from `TransRed::run()` to `WitnessContext` post-condition
/// because the full `run()` is intractable for Kani (timeout at 300s).
#[kani::proof]
fn proof_transred_run_keeps_one_duplicate_binary_clause() {
    let mut clauses = ClauseArena::new();
    let l0 = lit(0, false);
    let l1 = lit(1, true);
    let c0 = clauses.add(&[l0, l1], false);
    let c1 = clauses.add(&[l0, l1], false);

    let vals = [0i8; 4];
    let delete_c0: bool = kani::any();
    let removed_idx = if delete_c0 { c0 } else { c1 };
    let kept_idx = if delete_c0 { c1 } else { c0 };
    // Clause refs are arena word offsets, not dense 0..N clause numbers.
    let mut pending_delete = [0u32; 2 * (HEADER_WORDS + 2)];
    pending_delete[removed_idx] = GEN;

    let witness_ctx = WitnessContext {
        clauses: &clauses,
        vals: &vals,
        original_clause_limit: clauses.len(),
    };
    assert!(
        !TransRed::is_valid_witness_clause(removed_idx, &witness_ctx, &pending_delete, GEN),
        "removed duplicate must not be a valid witness"
    );
    assert!(
        TransRed::is_valid_witness_clause(kept_idx, &witness_ctx, &pending_delete, GEN),
        "kept duplicate must remain a valid witness"
    );

    let mut both_deleted = [0u32; 2 * (HEADER_WORDS + 2)];
    both_deleted[c0] = GEN;
    both_deleted[c1] = GEN;
    assert!(!TransRed::is_valid_witness_clause(
        c0,
        &witness_ctx,
        &both_deleted,
        GEN
    ));
    assert!(!TransRed::is_valid_witness_clause(
        c1,
        &witness_ctx,
        &both_deleted,
        GEN
    ));
}

/// Prove that `is_valid_witness_clause` rejects all invalid witness categories:
/// - pending-delete clauses
/// - out-of-bounds indices
/// - clauses beyond original_clause_limit (learned after preprocessing)
/// - deleted/empty clauses
/// - learned clauses
#[kani::proof]
fn proof_transred_duplicate_binary_pending_delete_preserves_one_witness() {
    let mut clauses = ClauseArena::new();
    let l0 = lit(0, false);
    let l1 = lit(1, true);
    let c0 = clauses.add(&[l0, l1], false);
    let c1 = clauses.add(&[l0, l1], false);

    let vals = [0i8; 4];

    let base_ctx = WitnessContext {
        clauses: &clauses,
        vals: &vals,
        original_clause_limit: clauses.len(),
    };
    let no_pending_delete = [0u32; 2 * (HEADER_WORDS + 2)];
    assert_witness_validity(&base_ctx, &no_pending_delete, &[(c0, true), (c1, true)]);
    let mut c0_pending_delete = [0u32; 2 * (HEADER_WORDS + 2)];
    c0_pending_delete[c0] = GEN;
    assert_witness_validity(&base_ctx, &c0_pending_delete, &[(c0, false), (c1, true)]);
    let mut c1_pending_delete = [0u32; 2 * (HEADER_WORDS + 2)];
    c1_pending_delete[c1] = GEN;
    assert_witness_validity(&base_ctx, &c1_pending_delete, &[(c0, true), (c1, false)]);
}

#[kani::proof]
fn proof_transred_pending_delete_clause_is_not_valid_witness() {
    let mut clauses = ClauseArena::new();
    let l0 = lit(0, false);
    let l1 = lit(1, true);
    // C0: valid irredundant binary clause, marked pending-delete
    let c0 = clauses.add(&[l0, l1], false);
    // C1: valid irredundant binary clause, NOT pending-delete
    let c1 = clauses.add(&[l0, l1], false);

    let vals = [0i8; 4];
    let mut pending_delete = [0u32; 2 * (HEADER_WORDS + 2)];
    pending_delete[c0] = GEN;
    let witness_ctx = WitnessContext {
        clauses: &clauses,
        vals: &vals,
        original_clause_limit: clauses.len(),
    };

    // Pending-delete clause must be rejected
    assert!(
        !TransRed::is_valid_witness_clause(c0, &witness_ctx, &pending_delete, GEN),
        "pending-delete clause must not be a valid witness"
    );

    // Non-pending-delete clause must be accepted
    assert!(
        TransRed::is_valid_witness_clause(c1, &witness_ctx, &pending_delete, GEN),
        "non-pending irredundant binary must be a valid witness"
    );

    // Out-of-bounds index must be rejected
    assert!(
        !TransRed::is_valid_witness_clause(99, &witness_ctx, &pending_delete, GEN),
        "out-of-bounds index must not be a valid witness"
    );

    // Index beyond original_clause_limit must be rejected
    let restricted_ctx = WitnessContext {
        clauses: &clauses,
        vals: &vals,
        original_clause_limit: c1, // only C0 is "original"
    };
    assert!(
        !TransRed::is_valid_witness_clause(c1, &restricted_ctx, &pending_delete, GEN),
        "clause beyond original_clause_limit must not be a valid witness"
    );
}
