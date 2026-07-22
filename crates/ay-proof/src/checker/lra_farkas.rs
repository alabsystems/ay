// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode semantic validation for `TheoryLemmaKind::LraFarkas` proof steps.
//!
//! Converts proof-clause (blocking clause) polarity into theory-conflict polarity,
//! then delegates to the shared `ay_core::proof_validation::verify_farkas_conflict_lits_full`.

use ay_core::{FarkasAnnotation, ProofId, TermData, TermId, TermStore, TheoryLit};

use super::ProofCheckError;

/// Validate an `LraFarkas` theory lemma in strict mode.
///
/// The proof `clause` is a blocking clause: each literal is the *negation* of the
/// corresponding conflict literal. For example, conflict `{x ≤ 5, x ≥ 10}` produces
/// blocking clause `{¬(x ≤ 5), ¬(x ≥ 10)}`.
///
/// This function:
/// 1. Requires a `FarkasAnnotation` (missing → error).
/// 2. Converts each blocking-clause literal to a `TheoryLit` conflict literal.
/// 3. Delegates to `verify_farkas_conflict_lits_full` for semantic validation.
pub(crate) fn validate_lra_farkas(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
) -> Result<(), ProofCheckError> {
    let farkas = farkas.ok_or_else(|| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "LraFarkas in strict mode requires a Farkas annotation".to_string(),
    })?;

    let conflict: Vec<TheoryLit> = clause
        .iter()
        .map(|&lit| blocking_lit_to_conflict_lit(terms, lit))
        .collect();

    ay_core::proof_validation::verify_farkas_conflict_lits_full(terms, &conflict, farkas).map_err(
        |e| ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: e.to_string(),
        },
    )
}

/// Convert a blocking-clause literal to the corresponding conflict `TheoryLit`.
///
/// - `¬(atom)` in the blocking clause → conflict literal `atom = true`
/// - `atom` in the blocking clause → conflict literal `atom = false`
fn blocking_lit_to_conflict_lit(terms: &TermStore, lit: TermId) -> TheoryLit {
    match terms.get(lit) {
        TermData::Not(inner) => TheoryLit {
            term: *inner,
            value: true,
        },
        _ => TheoryLit {
            term: lit,
            value: false,
        },
    }
}
