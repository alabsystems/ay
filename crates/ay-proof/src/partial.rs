// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Partial proof validation that skips Hole steps.
//!
//! Provides [`check_proof_partial`] for validating proofs that may contain
//! incomplete (Hole) steps. Always returns accurate [`PartialProofCheck`]
//! statistics, even when validation encounters an error (#4592).

use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId, TermStore};

use crate::checker::{ensure_terminal_empty_clause, validate_step, ProofCheckError};

/// Partial proof check result for proofs that may contain Hole steps.
///
/// Unlike [`crate::ProofQuality`] (which is returned from functions that reject
/// Hole steps), this struct is always populated — even when validation
/// encounters an error. This prevents the caller from needing a fallback
/// estimator that would inflate `checked_steps` on the error path (#4592).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PartialProofCheck {
    /// Number of non-Hole steps that were actually validated by the checker.
    /// On error, this reflects only the prefix that was checked before the
    /// failing step — not `total_steps - skipped_hole_steps`.
    pub checked_steps: u32,
    /// Number of Hole steps skipped during partial validation.
    pub skipped_hole_steps: u32,
    /// Total number of steps in the proof.
    pub total_steps: u32,
}

impl std::fmt::Display for PartialProofCheck {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "checked={} skipped_holes={} total={}",
            self.checked_steps, self.skipped_hole_steps, self.total_steps,
        )
    }
}

/// Validate proof structure, skipping Hole steps instead of rejecting them.
///
/// Returns a [`PartialProofCheck`] with accurate step counts regardless of
/// whether validation succeeds or fails. On error, `checked_steps` reflects
/// only the steps actually validated before the error — it does NOT fall back
/// to `total_steps - skipped_hole_steps`.
///
/// Hole steps are treated as axioms for premise linkage (their clause is
/// accepted without semantic verification). All other steps are validated
/// normally.
pub fn check_proof_partial(
    proof: &Proof,
    terms: &TermStore,
) -> (PartialProofCheck, Option<ProofCheckError>) {
    let mut result = PartialProofCheck {
        total_steps: proof.steps.len() as u32,
        ..Default::default()
    };

    if proof.steps.is_empty() {
        return (result, Some(ProofCheckError::EmptyProof));
    }

    let mut derived_clauses: Vec<Option<Vec<TermId>>> = Vec::with_capacity(proof.steps.len());

    for (idx, step) in proof.steps.iter().enumerate() {
        let is_hole = matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Hole,
                ..
            }
        );

        if is_hole {
            result.skipped_hole_steps += 1;
            // Accept hole clause for linkage without semantic validation.
            if let ProofStep::Step { clause, .. } = step {
                derived_clauses.push(Some(clause.clone()));
            } else {
                derived_clauses.push(None);
            }
            continue;
        }

        let step_result = validate_step(
            terms,
            &mut derived_clauses,
            ProofId(idx as u32),
            step,
            false,
            None,
        );

        match step_result {
            Ok(()) => result.checked_steps += 1,
            Err(e) => return (result, Some(e)),
        }
    }

    let terminal_result = ensure_terminal_empty_clause(&derived_clauses);
    if let Err(e) = terminal_result {
        return (result, Some(e));
    }

    (result, None)
}

#[cfg(test)]
#[path = "partial_tests.rs"]
mod tests;
