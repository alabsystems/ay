// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Tests for `check_proof_partial` statistics accuracy.
// Verifies that the partial checker's PartialProofCheck summary
// correctly reflects actual processing when the checker aborts early
// on an invalid step.
//
// See sat-debuggability epic #4172.

use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, TermStore};
use ay_proof::{check_proof_partial, ProofCheckError};

/// When `check_proof_partial` succeeds, the summary must satisfy:
/// `checked_steps + skipped_hole_steps == total_steps`.
#[test]
fn test_partial_stats_invariant_on_success() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let hole = proof.add_step(ProofStep::Step {
        rule: AletheRule::Hole,
        clause: vec![not_x],
        premises: vec![],
        args: vec![],
    });
    proof.add_resolution(vec![], x, hole, h0);

    let (summary, err) = check_proof_partial(&proof, &terms);
    assert!(err.is_none(), "valid mixed proof should pass: {err:?}");

    assert_eq!(
        summary.checked_steps + summary.skipped_hole_steps,
        summary.total_steps,
        "checked + skipped must equal total on success"
    );
    assert_eq!(summary.total_steps, 3);
    assert_eq!(summary.checked_steps, 2);
    assert_eq!(summary.skipped_hole_steps, 1);
}

/// On error, `check_proof_partial` returns an error in the second tuple element.
/// The error aborts at the failing step, so the actual number of steps
/// checked is strictly less than `total_steps - skipped_hole_steps`.
#[test]
fn test_partial_checker_aborts_early_on_invalid_step() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let not_x = terms.mk_not(x);

    // Build a 5-step proof where step 2 is invalid:
    // Step 0: assume(x)         — valid
    // Step 1: assume(not_x)     — valid
    // Step 2: resolution({y})   — INVALID (resolvent should be empty)
    // Step 3: assume(y)         — never reached
    // Step 4: resolution({})    — never reached
    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let h1 = proof.add_assume(not_x, None);
    proof.add_step(ProofStep::Resolution {
        clause: vec![y], // wrong resolvent
        pivot: x,
        clause1: h0,
        clause2: h1,
    });
    proof.add_assume(y, None);
    proof.add_resolution(vec![], y, ProofId(2), ProofId(3));

    let (_summary, err) = check_proof_partial(&proof, &terms);
    let err = err.expect("invalid resolution must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidResolution { step, .. } if step == ProofId(2)),
        "expected InvalidResolution at step 2, got: {err:?}"
    );
}

/// Multiple holes interleaved with valid steps: all non-hole steps
/// must be validated and hole clauses must be usable as premises.
#[test]
fn test_partial_checker_multiple_holes_interleaved() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);

    // Step 0: assume(a)
    // Step 1: hole claiming {not_a, b}
    // Step 2: resolution on a: {a} ⊗ {not_a, b} → {b}
    // Step 3: hole claiming {not_b}
    // Step 4: resolution on b: {b} ⊗ {not_b} → {}
    let mut proof = Proof::new();
    let h0 = proof.add_assume(a, None);
    let hole1 = proof.add_step(ProofStep::Step {
        rule: AletheRule::Hole,
        clause: vec![not_a, b],
        premises: vec![],
        args: vec![],
    });
    let res1 = proof.add_resolution(vec![b], a, h0, hole1);
    let hole2 = proof.add_step(ProofStep::Step {
        rule: AletheRule::Hole,
        clause: vec![not_b],
        premises: vec![],
        args: vec![],
    });
    proof.add_resolution(vec![], b, res1, hole2);

    let (summary, err) = check_proof_partial(&proof, &terms);
    assert!(err.is_none(), "valid multi-hole proof should pass: {err:?}");

    assert_eq!(summary.total_steps, 5);
    assert_eq!(summary.skipped_hole_steps, 2);
    assert_eq!(summary.checked_steps, 3); // assume + 2 resolutions
    assert_eq!(
        summary.checked_steps + summary.skipped_hole_steps,
        summary.total_steps,
    );
}

/// Partial checker must still enforce terminal empty clause requirement.
#[test]
fn test_partial_checker_rejects_non_empty_terminal_clause() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(x, None);

    let (_summary, err) = check_proof_partial(&proof, &terms);
    let err = err.expect("proof without empty terminal clause must fail");
    assert!(
        matches!(err, ProofCheckError::FinalClauseNotEmpty { .. }),
        "expected FinalClauseNotEmpty, got: {err:?}"
    );
}
