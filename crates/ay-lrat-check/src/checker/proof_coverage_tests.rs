// Copyright 2026 Andrew Yates
// Proof coverage gap tests: untested error paths and edge cases.
//
// Identified by P1:588 proof_coverage reflection iteration.
// Each test targets a specific untested code path in the LRAT checker.

use super::*;
use crate::lrat_parser::{self, LratStep};

// ─── verify_proof: no empty clause derived ──────────────────────────

/// A proof that completes without deriving the empty clause must be rejected.
/// Covers verify_proof lines 213-219 (derived_empty_clause check).
#[test]
fn test_verify_proof_no_empty_clause_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b

    // Valid derivation of (b), but proof ends without empty clause.
    let steps = vec![LratStep::Add {
        id: 3,
        clause: vec![Literal::from_dimacs(2)],
        hints: vec![1, 2],
    }];
    let result = checker.verify_proof(&steps);
    assert!(
        !result,
        "proof that does not derive empty clause must be rejected"
    );
}

/// A proof containing only deletions (no additions) must be rejected.
#[test]
fn test_verify_proof_deletion_only_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]);

    let steps = vec![LratStep::Delete { ids: vec![1] }];
    let result = checker.verify_proof(&steps);
    assert!(
        !result,
        "deletion-only proof must be rejected: no empty clause"
    );
}

/// An empty proof (no steps at all) must be rejected.
#[test]
fn test_verify_proof_empty_steps_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]);
    let result = checker.verify_proof(&[]);
    assert!(!result, "empty proof must be rejected");
}

// ─── RAT: extra RUP hints consumed by inner loop ────────────────────

/// The inner RUP-hint loop in verify_rat_witnesses (rat.rs:56) consumes ALL
/// positive values before the outer loop can see them. This means extra
/// positive hints after a valid witness group are silently consumed as
/// RUP hints for that witness (the conflict is found before they're checked).
///
/// The guard at rat.rs:46 (`if hint >= 0 { return false }`) is effectively
/// dead code — no sequence of valid LRAT hints can reach it because the
/// inner `while rat_hints[i] > 0` loop always runs first. This test
/// documents the behavior: extra positive hints after a valid witness
/// group are harmlessly consumed.
#[test]
fn test_rat_extra_positive_hints_consumed_by_inner_loop() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(2, &[lit(2)]); // (b)

    // Hints: [-1, 2, 3]. The inner loop consumes [2, 3] as RUP hints for
    // witness clause 1. Hint 2 causes conflict, hint 3 is never evaluated
    // but is structurally part of the RUP section. The proof passes.
    let ok = checker.add_derived(3, &[lit(1)], &[-1, 2, 3]);
    assert!(
        ok,
        "extra positive hints after valid witness should be harmlessly consumed"
    );
}

/// RAT completeness check: if a clause containing ~pivot is not covered
/// by any witness group, the proof is rejected (rat.rs:77-96).
#[test]
fn test_rat_incomplete_witnesses_rejected() {
    let mut checker = LratChecker::new(4);
    checker.add_original(1, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(2, &[lit(-1), lit(3)]); // ~a v c (another clause with ~a)
    checker.add_original(3, &[lit(2)]); // (b)
    checker.add_original(4, &[lit(3)]); // (c)

    // Derive (a) via RAT: pivot=a. Must provide witnesses for BOTH clause 1
    // and clause 2 (both contain ~a). Only provide witness for clause 1.
    let ok = checker.add_derived(5, &[lit(1)], &[-1, 3]);
    assert!(
        !ok,
        "RAT proof with incomplete witnesses (missing clause 2) must be rejected"
    );
}

// ─── propagate_rup_hints: duplicate hint rejection ──────────────────

/// Duplicate hint IDs in the RUP section must be rejected (CaDiCaL parity).
#[test]
fn test_rup_duplicate_hint_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b

    // Derive (b) with duplicate hint [1, 1, 2] — first 1 propagates, second 1
    // is a duplicate and is rejected.
    let ok = checker.add_derived(3, &[lit(2)], &[1, 1, 2]);
    assert!(!ok, "duplicate RUP hint ID should be rejected");
}

/// Tautological hint clause must be rejected (CaDiCaL parity).
#[test]
fn test_rup_tautological_hint_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(-1)]); // a v ~a (tautological)
    checker.add_original(2, &[lit(-2)]); // ~b

    // Try to derive something using the tautological clause as a hint.
    let ok = checker.add_derived(3, &[lit(2)], &[1]);
    assert!(!ok, "tautological hint clause should be rejected");
}

// ─── Binary LRAT edge cases ─────────────────────────────────────────

/// Empty binary LRAT input produces zero proof steps.
#[test]
fn test_binary_lrat_empty_input() {
    let steps = lrat_parser::parse_binary_lrat(&[]).expect("empty binary input should parse");
    assert!(steps.is_empty(), "empty input should produce empty steps");
}

/// Text LRAT with only whitespace lines produces zero steps.
#[test]
fn test_text_lrat_whitespace_only() {
    let steps = lrat_parser::parse_text_lrat("   \n  \n\n").expect("whitespace-only should parse");
    assert!(
        steps.is_empty(),
        "whitespace-only input should produce empty steps"
    );
}

/// Text LRAT with only comment lines produces zero steps.
#[test]
fn test_text_lrat_comments_only() {
    let steps = lrat_parser::parse_text_lrat("c this is a comment\nc another\n")
        .expect("comment-only should parse");
    assert!(
        steps.is_empty(),
        "comment-only input should produce empty steps"
    );
}

// ─── delete_verified: marks resize for large extension variables ─────

/// delete_verified with literals having indices beyond the initial marks
/// array size must resize correctly.
#[test]
fn test_delete_verified_large_extension_variable() {
    let mut checker = LratChecker::new(2); // Initial marks for 2 vars
                                           // Add a clause with extension variable 100 (well beyond initial capacity).
    checker.add_original(1, &[lit(1)]); // (a)
    checker.add_original(2, &[lit(-1)]); // (~a)
                                         // Derive empty clause to make the checker consistent.
    assert!(checker.add_derived(3, &[], &[1, 2]));

    // Add a clause with an extension variable.
    assert!(checker.add_derived(
        4,
        &[Literal::from_dimacs(100), Literal::from_dimacs(-100)],
        &[1, 2]
    ));

    // delete_verified with the extension variable literal.
    // The marks array must resize to accommodate index for variable 100.
    let ok = checker.delete_verified(4, &[Literal::from_dimacs(100), Literal::from_dimacs(-100)]);
    assert!(ok, "delete_verified must handle extension variable indices");
}

// ─── verify_chain: missing hint clause ──────────────────────────────

/// When a positive hint references a non-existent clause ID, verify_chain
/// returns false. Tests the `None => return false` path in propagate_rup_hints.
#[test]
fn test_rup_missing_hint_clause_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b

    // Hint 999 does not exist.
    let ok = checker.add_derived(2, &[lit(2)], &[999]);
    assert!(!ok, "non-existent hint clause must cause failure");
}

// ─── check_resolution: negative hint causes failure ─────────────────

/// check_resolution returns false if a negative hint appears in the RUP
/// section (line 67-69 of resolution.rs).
#[test]
fn test_resolution_negative_hint_in_rup_section() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b

    // Valid hints for (b) would be [1, 2]. Use [-1, 2] — negative hint
    // in the RUP section makes RUP fail, then falls through to RAT/blocked.
    let ok = checker.add_derived(3, &[lit(2)], &[-1, 2]);
    // This should fail because the RAT/blocked fallback won't help.
    assert!(
        !ok,
        "negative hint at start should cause verify_chain failure"
    );
}

// ─── Extension variables in derived clauses ─────────────────────────

/// Derived clauses may use extension variables (beyond num_vars).
/// The assignment and marks arrays must grow dynamically.
#[test]
fn test_extension_variable_grows_arrays() {
    let mut checker = LratChecker::new(2); // 2 variables declared
    checker.add_original(1, &[lit(1)]); // (a)
    checker.add_original(2, &[lit(-1)]); // (~a) — contradicts

    // Derive a clause using extension variable 50 (beyond num_vars=2).
    // The contradiction means empty clause is RUP.
    let ok = checker.add_derived(3, &[Literal::from_dimacs(50)], &[1, 2]);
    assert!(
        ok,
        "extension variable clause should be derivable from contradiction"
    );

    // Derive empty clause.
    let ok = checker.add_derived(4, &[], &[1, 2]);
    assert!(ok, "empty clause should be derivable");
    assert!(checker.derived_empty_clause());
}

// ─── Out-of-range literal in original clause ────────────────────────

/// An original clause with a literal exceeding num_vars must be rejected.
#[test]
fn test_out_of_range_literal_rejected_in_original() {
    let mut checker = LratChecker::new(2); // 2 variables declared
                                           // Variable 10 exceeds num_vars=2.
    let ok = checker.add_original(1, &[Literal::from_dimacs(10)]);
    assert!(
        !ok,
        "literal exceeding num_vars should be rejected in original clause"
    );
}
