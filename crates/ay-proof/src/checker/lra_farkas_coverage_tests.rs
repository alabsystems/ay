// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode coverage tests for LRA Farkas theory lemma validation (#6670).
//!
//! These tests validate that the checker correctly processes LraFarkas theory
//! lemmas in strict mode. Tests construct TheoryLemma proof steps with Farkas
//! annotations and verify the checker accepts valid lemmas and rejects invalid ones.
//!
//! Validation is wired: `validate_lra_farkas` converts blocking-clause polarity
//! to conflict-literal polarity, then delegates to
//! `ay_core::proof_validation::verify_farkas_conflict_lits_full`.

use num_bigint::BigInt;

use crate::checker::*;
use ay_core::{FarkasAnnotation, ProofId, ProofStep, Sort, TermId, TermStore, TheoryLemmaKind};

/// Helper: validate a TheoryLemma step in strict mode.
fn validate_theory_lemma_strict(
    terms: &TermStore,
    clause: Vec<TermId>,
    farkas: Option<FarkasAnnotation>,
    kind: TheoryLemmaKind,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::TheoryLemma {
        theory: "LRA".to_string(),
        clause,
        farkas,
        kind,
        lia: None,
    };
    let mut derived = Vec::new();
    validate_step(terms, &mut derived, ProofId(0), &step, true, None)
}

// ===== Valid Farkas lemmas =====

/// A valid Farkas conflict: x <= 5 AND x >= 10 is contradictory.
///
/// Blocking clause: (not (x <= 5)) OR (not (x >= 10))
/// Farkas: coefficients [1, 1] eliminate x: 1*(x - 5) + 1*(10 - x) = 5 > 0.
#[test]
fn test_strict_lra_farkas_valid_bounds_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    // Conflict literals: x <= 5 (true) and x >= 10 (true)
    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);

    // Blocking clause negates the conflict: (not (x <= 5)), (not (x >= 10))
    let not_x_le_5 = terms.mk_not_raw(x_le_5);
    let not_x_ge_10 = terms.mk_not_raw(x_ge_10);

    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    validate_theory_lemma_strict(
        &terms,
        vec![not_x_le_5, not_x_ge_10],
        Some(farkas),
        TheoryLemmaKind::LraFarkas,
    )
    .expect("valid bounds conflict with correct Farkas should pass");
}

/// A valid Farkas conflict involving equality: x = 0 AND x >= 1.
///
/// Blocking clause: (not (x = 0)) OR (not (x >= 1))
/// Farkas: [1, 1] — x = 0 decomposes to x <= 0 AND x >= 0;
/// combined with x >= 1, we get 0 >= 1 contradiction.
#[test]
fn test_strict_lra_farkas_valid_equality_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));

    let x_eq_0 = terms.mk_eq(x, zero);
    let x_ge_1 = terms.mk_ge(x, one);

    let not_x_eq_0 = terms.mk_not_raw(x_eq_0);
    let not_x_ge_1 = terms.mk_not_raw(x_ge_1);

    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    validate_theory_lemma_strict(
        &terms,
        vec![not_x_eq_0, not_x_ge_1],
        Some(farkas),
        TheoryLemmaKind::LraFarkas,
    )
    .expect("valid equality conflict with correct Farkas should pass");
}

// ===== Invalid Farkas lemmas (correctly rejected) =====

/// Invalid Farkas certificate: wrong coefficients that don't eliminate variables.
///
/// x <= 5 AND x >= 10 with coefficients [1, 0] — the x variable from x >= 10
/// is not eliminated.
#[test]
fn test_strict_lra_farkas_wrong_coefficients_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);

    let not_x_le_5 = terms.mk_not_raw(x_le_5);
    let not_x_ge_10 = terms.mk_not_raw(x_ge_10);

    // Wrong coefficients: [1, 0] — does not eliminate x
    let farkas = FarkasAnnotation::from_ints(&[1, 0]);
    let result = validate_theory_lemma_strict(
        &terms,
        vec![not_x_le_5, not_x_ge_10],
        Some(farkas),
        TheoryLemmaKind::LraFarkas,
    );

    result.expect_err("wrong coefficients should fail Farkas validation");
}

/// LraFarkas with no Farkas annotation at all — rejected in strict mode.
#[test]
fn test_strict_lra_farkas_missing_annotation_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);

    let not_x_le_5 = terms.mk_not_raw(x_le_5);
    let not_x_ge_10 = terms.mk_not_raw(x_ge_10);

    let result = validate_theory_lemma_strict(
        &terms,
        vec![not_x_le_5, not_x_ge_10],
        None, // no annotation
        TheoryLemmaKind::LraFarkas,
    );

    result.expect_err("missing Farkas annotation should fail in strict mode");
}

/// Non-contradictory literals with bogus Farkas annotation — rejected.
///
/// x <= 10 AND x >= 5 — these are consistent (any x in [5, 10] satisfies both).
/// No valid Farkas certificate exists.
#[test]
fn test_strict_lra_farkas_non_contradictory_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_10 = terms.mk_le(x, ten);
    let x_ge_5 = terms.mk_ge(x, five);

    let not_x_le_10 = terms.mk_not_raw(x_le_10);
    let not_x_ge_5 = terms.mk_not_raw(x_ge_5);

    // Attempting coefficients [1, 1]: sum is 1*(x - 10) + 1*(5 - x) = -5 <= 0
    // This does NOT produce a contradiction (constant is negative, not positive).
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let result = validate_theory_lemma_strict(
        &terms,
        vec![not_x_le_10, not_x_ge_5],
        Some(farkas),
        TheoryLemmaKind::LraFarkas,
    );

    result.expect_err("non-contradictory literals should fail Farkas validation");
}
