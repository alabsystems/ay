// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Stateless source-bound candidate generation; never solver publication.

use crate::sos::{
    budget::{SosPolynomialBudget, SosProgress},
    search_with_progress, SosClauseSource,
};
use ay_core::{ProofStep, TermId, TermStore};

/// The caller refused further work, allocation, or cooperative execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum SosCandidateError {
    /// Candidate generation exceeded its resource or cancellation budget.
    #[error("SOS candidate generation exceeded the caller's resource or cancellation budget")]
    ResourceLimit,
}

/// Search for an **untrusted** rational SOS candidate for an exact clause.
///
/// The candidate refutes the conjunction of the negations of the ordered
/// `clause` literals. Inputs must be direct integer/real polynomial comparisons
/// or their explicit negations. Source positions, including constant comparison
/// and duplicate slots, are preserved. The returned [`ProofStep::NraSos`] owns
/// that same clause and its evidence; it is not an UNSAT result or a publication
/// certificate. A consumer must independently validate it with `ay-proof` and
/// bind the complete proof to the intended problem before accepting any result.
///
/// `progress` receives conservative incremental work and allocation/scratch
/// debits, shared across translation, both search degrees, all LP attempts,
/// replay, and conversion. Returning `false` is sticky: no later phase can
/// resume the attempt. A final poll dominates success. Control is cooperative,
/// not a hard real-time guarantee; individual exact operations are size-bounded.
///
/// `Ok(None)` means unsupported input, a fixed local limit, or no witness found
/// in the bounded DSOS search. It does **not** establish satisfiability. A
/// caller refusal returns [`SosCandidateError::ResourceLimit`]. This stateless
/// API neither reads a solver's cached witness nor changes its decision policy.
pub fn find_sos_refutation_candidate(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<Option<ProofStep>, SosCandidateError> {
    let mut control = SosProgress::new(progress);
    if !control.poll() {
        return Err(SosCandidateError::ResourceLimit);
    }
    let source = {
        let mut budget = SosPolynomialBudget::with_progress(&mut control);
        SosClauseSource::from_clause(terms, clause, &mut budget)
    };
    let candidate = source.and_then(|source| {
        let certificate =
            search_with_progress(source.constraints(), source.variables(), &mut control)?;
        source.convert_candidate(&certificate, &mut control)
    });
    if !control.poll() {
        return Err(SosCandidateError::ResourceLimit);
    }
    Ok(candidate)
}

#[cfg(test)]
mod tests;
