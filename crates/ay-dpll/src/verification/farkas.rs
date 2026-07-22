// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! Farkas certificate verification for LRA/LIA theory conflicts.
//!
//! Shared arithmetic certificate validation lives in `ay-core` so the runtime
//! DPLL(T) verifier and the proof checker use the same semantics.

use ay_core::proof_validation::{
    verify_farkas_annotation_shape, verify_farkas_conflict_lits_full, FarkasValidationError,
};
use ay_core::{FarkasAnnotation, TermStore, TheoryConflict, TheoryLit};

use super::structural::verify_theory_conflict;
use super::VerificationError;

/// Verify a theory conflict that includes Farkas coefficients.
///
/// In addition to structural checks, this verifies:
/// 1. Farkas coefficients are present
/// 2. All coefficients are non-negative (required for Farkas lemma)
/// 3. Number of coefficients matches number of literals
///
/// Returns [`VerificationError::MissingFarkasAnnotation`] when
/// `conflict.farkas` is `None`. This happens when the LRA simplex solver
/// produces `UnsatWithFarkas` but fails to extract valid coefficients
/// (e.g., due to BigRational overflow or deduplication). The conflict
/// clause is still sound (derived from simplex infeasibility), but the
/// proof certificate is missing. Callers should use
/// [`VerificationError::is_missing_annotation`] to distinguish this from
/// genuinely invalid certificates.
pub(crate) fn verify_theory_conflict_with_farkas(
    conflict: &TheoryConflict,
) -> Result<(), VerificationError> {
    verify_theory_conflict(&conflict.literals)?;

    match conflict.farkas {
        Some(ref farkas) => verify_farkas_certificate(farkas, conflict.literals.len()),
        None => Err(VerificationError::MissingFarkasAnnotation),
    }
}

/// Verify a theory conflict with Farkas coefficients, including semantic checks.
///
/// This extends [`verify_theory_conflict_with_farkas`] by checking that the Farkas
/// coefficients actually yield a contradiction when applied to the conflict
/// constraints. Returns [`VerificationError::MissingFarkasAnnotation`] when
/// the annotation is absent (propagated from the structural check).
///
/// Runs in ALL builds since the adversarial-review followup on #rank-4
/// increment 2: the UnsatWithFarkas dispatch arms use this as their release
/// backstop, mirroring the plain-Unsat arms' `verify_conflict_semantic`.
pub(crate) fn verify_theory_conflict_with_farkas_full(
    conflict: &TheoryConflict,
    terms: &TermStore,
) -> Result<(), VerificationError> {
    verify_theory_conflict_with_farkas(conflict)?;

    // If we reach here, farkas is guaranteed to be Some (structural check above
    // returns MissingFarkasAnnotation for None).
    let farkas = conflict
        .farkas
        .as_ref()
        .expect("structural check passed implies farkas is Some");

    verify_farkas_certificate_full(terms, &conflict.literals, farkas)
}

/// Verify a Farkas certificate is structurally valid.
pub(crate) fn verify_farkas_certificate(
    farkas: &FarkasAnnotation,
    num_literals: usize,
) -> Result<(), VerificationError> {
    verify_farkas_annotation_shape(farkas, num_literals).map_err(map_farkas_error)
}

/// Verify that a Farkas certificate semantically proves the conflict is UNSAT.
pub(crate) fn verify_farkas_certificate_full(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
) -> Result<(), VerificationError> {
    verify_farkas_conflict_lits_full(terms, conflict, farkas).map_err(map_farkas_error)
}

fn map_farkas_error(err: FarkasValidationError) -> VerificationError {
    VerificationError::InvalidFarkas {
        reason: err.to_string(),
    }
}
