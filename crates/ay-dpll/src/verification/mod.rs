// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! Theory conflict verification for soundness checking
//!
//! This module verifies that theory conflicts are actually UNSAT.
//! Catches bugs where theories return spurious conflicts.
//!
//! # Phase 1: Basic Verification (COMPLETE)
//!
//! Structural sanity checks:
//! - Conflict must not be empty (would mean unconditional UNSAT)
//! - No duplicate literals (indicates bug in conflict generation)
//! - No contradictory literals (same term with both true and false)
//!
//! # Phase 2: Semantic Verification (COMPLETE)
//!
//! Theory-specific semantic verification:
//! - LRA/LIA: Full Farkas lemma verification - verifies λ≥0, λᵀA=0, λᵀb<0
//! - EUF: Re-runs congruence closure to verify conflicts are truly UNSAT
//! - Array: Combined ArrayEuf solver for ROW/extensionality axioms
//! - BV: Structural verification (bit-blasting requires SAT backend for semantic checks)
//! - String: Structural verification (lemma-based reasoning prevents fresh-solver approach)
//!
//! Note: LIA GCD/divisibility failures return `TheoryResult::Unsat` (not
//! `UnsatWithFarkas`) since these are not Farkas-provable over reals.
//!
//! # Release-Mode Verification Policy (#4515, #5420)
//!
//! All semantic verification runs in all builds. The cost is acceptable:
//!
//! | Check | Build | Cost | Rationale |
//! |-------|-------|------|-----------|
//! | Structural conflict (`verify_theory_conflict`) | All | O(k) | Cheap: set membership on conflict lits |
//! | Structural propagation (`verify_theory_propagation`) | All | O(k) | Cheap: reason validity checks |
//! | Farkas structural (`verify_theory_conflict_with_farkas`) | All | O(k) | Cheap: coefficient sign checks |
//! | Farkas semantic (`verify_theory_conflict_with_farkas_full`) | All | O(k) | ~2μs BigRational arithmetic on 2-10 lits |
//! | EUF semantic (`verify_euf_conflict`) | All | O(n) | Fresh EufSolver with full TermStore |
//! | Propagation semantic (`verify_propagation_semantic`) | All | O(n) | Fresh theory solver per check |
//!
//! Where k = conflict size (typically 2-10), n = TermStore size (can be 10,000+).
//!
//! The Farkas certificate is pure arithmetic validation — no solver allocation,
//! no congruence closure. EUF verification allocates `UnionFind::new(terms.len())`
//! per conflict, making it O(n) regardless of conflict size.
//!
//! Long-term: certificate-based EUF verification via Alethe congruence steps
//! would reduce cost to O(proof_length), further reducing EUF checking overhead.
//!
//! # Phase 3: External Proof Format (NOT STARTED)
//!
//! Future: Generate proofs in standard format (Alethe, LFSC) checkable by external tools.
mod dispatch;
mod dt_tautology;
mod euf;
mod farkas;
mod structural;

#[cfg(test)]
mod tests;

use ay_core::TermId;
use thiserror::Error;

/// Errors from theory conflict verification
#[derive(Debug, Error)]
pub(crate) enum VerificationError {
    /// Conflict is empty - theories should not return empty conflicts
    #[error("Conflict is empty (theories should return at least one literal)")]
    EmptyConflict,

    /// Conflict contains duplicate literals
    #[error("Conflict contains duplicate literal: term={term:?} value={value}")]
    DuplicateLiteral {
        /// The duplicated term
        term: TermId,
        /// The value of the duplicated literal
        value: bool,
    },

    /// Conflict contains contradictory literals (same term, opposite values)
    #[error("Conflict contains contradictory literals: term={term:?} appears with both values")]
    ContradictoryLiterals {
        /// The term that appears with contradictory values
        term: TermId,
    },

    /// Conflict literals are satisfiable (not a real conflict) - caught by mini-solver
    #[error("Conflict literals are satisfiable (not a real conflict)")]
    ConflictIsSat,

    /// Farkas coefficients are invalid (negative coefficient)
    #[error("Farkas certificate invalid: {reason}")]
    InvalidFarkas {
        /// Description of the invalidity
        reason: String,
    },

    /// Farkas annotation is missing from a conflict produced via UnsatWithFarkas.
    ///
    /// The conflict clause itself is sound (derived from simplex infeasibility),
    /// but the proof certificate cannot be recorded. Callers should skip proof
    /// recording but continue learning the conflict clause.
    #[error(
        "Farkas annotation missing: conflict is sound but proof certificate cannot be recorded"
    )]
    MissingFarkasAnnotation,

    /// Internal verification error
    #[error("Internal verification error: {0}")]
    Internal(String),

    /// Propagation reason set is empty
    #[error("Propagation reason is empty (theory must provide at least one antecedent)")]
    EmptyReason,

    /// Propagation reason contains duplicate literals
    #[error("Propagation reason contains duplicate literal: term={term:?} value={value}")]
    DuplicateReasonLiteral {
        /// The duplicated term
        term: TermId,
        /// The value of the duplicated literal
        value: bool,
    },

    /// Propagated literal appears in its own reason set (circular justification)
    #[error("Propagated literal term={term:?} value={value} appears in its own reason set")]
    CircularPropagation {
        /// The term that appears in both propagated and reason
        term: TermId,
        /// The value of the propagated literal
        value: bool,
    },

    /// Theory propagation is not implied by its reason set (semantic check failed)
    #[error("Propagation not implied: reason set does not entail term={term:?} value={value}")]
    PropagationNotImplied {
        /// The propagated term
        term: TermId,
        /// The propagated value
        value: bool,
    },
}

impl VerificationError {
    /// Returns `true` if this error indicates a missing (but not invalid) Farkas
    /// annotation. Callers that perform graceful degradation can use this to
    /// distinguish "no certificate to verify" from "certificate is invalid".
    pub(crate) fn is_missing_annotation(&self) -> bool {
        matches!(self, Self::MissingFarkasAnnotation)
    }
}

// Re-export all public items from submodules so that `crate::verification::X` paths
// continue to work unchanged at all import sites.
pub(crate) use dispatch::{
    classify_propagation_domain, log_conflict_debug, log_conflict_debug_with_terms,
    log_propagation_debug, TheoryDomain,
};
// verify_conflict_semantic and verify_propagation_semantic create fresh theory
// solvers per conflict/propagation. Demoted back to debug-only (#6564): root
// cause (stale ImpliedBound.reasons) fixed by lazy reason collection.
pub(crate) use dispatch::conflict_has_array_context;
pub(crate) use dispatch::make_verification_combiner;
pub(crate) use dispatch::verify_conflict_semantic;
pub(crate) use dispatch::verify_conflict_semantic_euf_prechecked;
pub(crate) use dispatch::{verify_conflict_semantic_memoized, ConflictSemanticVerifyMemo};
pub(crate) use dt_tautology::build_datatype_tautology_axioms;
pub(crate) use euf::verify_euf_conflict;
pub(crate) use farkas::verify_theory_conflict_with_farkas;
pub(crate) use structural::{
    dedup_conflict_literals, dedup_conflict_with_farkas, verify_theory_conflict,
    verify_theory_propagation,
};
// #8254: Promoted to all builds.
pub(crate) use dispatch::verify_lra_full_state_satisfiable;
// Promoted to all builds (adversarial-review followup on #rank-4 increment 2):
// the UnsatWithFarkas dispatch arms now run full semantic Farkas verification
// in release as the backstop the plain-Unsat arms get from
// verify_conflict_semantic.
pub(crate) use farkas::verify_theory_conflict_with_farkas_full;
// #8529: Promoted to all builds. Demoting to debug-only (#8782) caused false
// SAT on QF_LRA benchmarks (synched.base.smt2) because unsound propagations
// from implied-bound derivation chains were not caught in release builds.
pub(crate) use dispatch::verify_propagation_semantic;

// Items used only by tests — not referenced by production code outside this module.
#[cfg(test)]
pub(crate) use euf::verify_euf_propagation;
#[cfg(test)]
pub(crate) use farkas::{verify_farkas_certificate, verify_farkas_certificate_full};
