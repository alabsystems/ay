// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Immutable source-derived units for structural array preprocessing.
//!
//! Retention is not authority. Every consumer must authenticate the complete
//! fragment against its current original roots before splicing any conclusion.
//! Shared proof storage keeps nested-query provenance snapshots shallow.

use std::sync::Arc;

use ay_core::{Proof, ProofId, Sort, TermId, TermStore};

#[derive(Debug, Clone)]
pub(crate) struct ArrayUnitDerivation {
    proof: Arc<Proof>,
    conclusion: ProofId,
    term: TermId,
}

impl ArrayUnitDerivation {
    /// Admit a unit only after checking its actual source-bound derivation.
    /// The caller must prepay constructing the supplied immutable proof; this
    /// method meters its retained record and the complete authentication.
    pub(crate) fn checked(
        terms: &TermStore,
        original_roots: &[TermId],
        proof: Arc<Proof>,
        conclusion: ProofId,
        term: TermId,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Option<Self> {
        if !progress(1, std::mem::size_of::<Self>()) {
            return None;
        }
        let candidate = Self {
            proof,
            conclusion,
            term,
        };
        candidate.reauthenticate(terms, original_roots, progress)?;
        Some(candidate)
    }

    pub(crate) fn term(&self) -> TermId {
        self.term
    }

    /// Freshly check the exact unit in the consumer's current source context.
    /// Missing roots, changed terms, malformed references or exhausted work
    /// refuse. No prior query's successful authentication is cached here.
    pub(crate) fn reauthenticate(
        &self,
        terms: &TermStore,
        original_roots: &[TermId],
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Option<(&Proof, ProofId)> {
        if !progress(1, 0)
            || self.term.0 as usize >= terms.len()
            || self.conclusion.0 as usize >= self.proof.steps.len()
            || terms.sort(self.term) != &Sort::Bool
        {
            return None;
        }
        let authenticated =
            ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
                &self.proof,
                terms,
                None,
                None,
                original_roots,
                progress,
            )
            .ok()?;
        if authenticated.clause(self.conclusion)? != [self.term] || !progress(0, 0) {
            return None;
        }
        Some((&self.proof, self.conclusion))
    }
}

#[cfg(test)]
mod tests;
