// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Premise-based clausification rule validation for strict proof checking.
//!
//! The `or` rule decomposes `(assume (or l1 l2 ... ln))` into `(cl l1 l2 ... ln)`.
//! This is the Alethe encoding for multi-literal input clause decomposition,
//! emitted by `SatProofManager` at `sat_proof_manager.rs:286`.

use ay_core::{ProofId, TermId, TermStore};

use super::boolean::{clause_matches_unordered, decode_app, err, make_err};
use super::ProofCheckError;

/// Validate the `or` Alethe rule (premise-based clause decomposition).
///
/// Pattern:
///   premise: `(assume (or l1 l2 ... ln))`
///   conclusion: `(cl l1 l2 ... ln)`
///
/// Checks:
///   1. Exactly one premise with exactly one term
///   2. That term is `(or ...)` application
///   3. Conclusion clause contains exactly the `or` children (unordered)
pub(crate) fn validate_or_clausification(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 {
        return err(step, "or", "rule requires exactly one premise");
    }
    if premise_clauses[0].len() != 1 {
        return err(
            step,
            "or",
            "premise must be a unit clause containing (or ...)",
        );
    }
    let or_term = premise_clauses[0][0];
    let args = decode_app(terms, or_term, "or")
        .ok_or_else(|| make_err(step, "or", "premise term must be an or application"))?;
    if !clause_matches_unordered(clause, args) {
        return err(
            step,
            "or",
            "conclusion clause must contain exactly the or children",
        );
    }
    Ok(())
}
