// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! Structural verification of theory conflicts and propagations.
//!
//! Phase 1 checks: empty conflicts, duplicate literals, contradictory literals,
//! circular propagations. These are cheap O(k) checks on conflict/reason size.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};

use ay_core::{TermId, TheoryConflict, TheoryLit, TheoryPropagation};

use super::VerificationError;

/// Remove exact duplicate `(term, value)` literals from a theory conflict,
/// preserving first-occurrence order (#4666).
///
/// A theory conflict is a SET of literals whose conjunction is claimed
/// unsatisfiable; the learned blocking clause is the disjunction of their
/// negations. `X ∨ X ≡ X`, so dropping exact duplicates is a logical
/// identity — it can neither weaken nor strengthen the conflict.
///
/// Several theory producers (combined Nelson-Oppen explanations that
/// concatenate per-theory reason sets, cross-sort bound propagation) can
/// emit the same literal twice. Before this dedupe, such conflicts were
/// structurally rejected by [`verify_theory_conflict`]
/// (`DuplicateLiteral`), which on the fail-closed paths degrades the check
/// to `Unknown` WITHOUT learning a blocking clause — so the theory
/// re-derives the identical conflict thousands of times (index_range's LRA
/// `contradictory_variable_bounds` was observed re-derived 2304x).
///
/// Contradictory pairs (same term, both polarities) are intentionally NOT
/// touched: a tautological conflict indicates a genuine producer bug and
/// keeps being surfaced by the structural check.
///
/// No-op (no reallocation) when the conflict has no exact duplicates.
pub(crate) fn dedup_conflict_literals(conflict: &mut Vec<TheoryLit>) {
    let mut seen: HashSet<(TermId, bool)> = Default::default();
    // Fast path: scan for a duplicate before mutating.
    let has_dup = conflict
        .iter()
        .any(|lit| !seen.insert((lit.term, lit.value)));
    if !has_dup {
        return;
    }
    seen.clear();
    conflict.retain(|lit| seen.insert((lit.term, lit.value)));
}

/// Farkas-aware variant of [`dedup_conflict_literals`] (#4666).
///
/// [`ay_core::FarkasAnnotation`] coefficients are positional (index i pairs
/// with literal i), so literal dedupe must merge coefficients. Merging by
/// SUMMATION is exactly right: a Farkas combination `λ₁·c + λ₂·c` of the
/// same constraint `c` equals `(λ₁+λ₂)·c`, and non-negativity is preserved
/// under addition of non-negative rationals — the certificate stays valid
/// for the deduped literal vector.
///
/// If the annotation's length does not match the literal count, the
/// conflict is left UNTOUCHED: positional alignment is already broken, and
/// the existing `InvalidFarkas` (coefficient-count mismatch) structural
/// error path (followed by certificate downgrade + fail-closed semantic
/// backstop) is the correct handler for that producer bug.
pub(crate) fn dedup_conflict_with_farkas(conflict: &mut TheoryConflict) {
    match &conflict.farkas {
        None => dedup_conflict_literals(&mut conflict.literals),
        Some(farkas) => {
            if farkas.coefficients.len() != conflict.literals.len() {
                // Mis-aligned certificate: leave it to the structural
                // wrong-count error + semantic backstop.
                return;
            }
            let mut first_idx: HashMap<(TermId, bool), usize> = Default::default();
            let mut lits: Vec<TheoryLit> = Vec::with_capacity(conflict.literals.len());
            let mut coeffs = Vec::with_capacity(farkas.coefficients.len());
            for (lit, coeff) in conflict.literals.iter().zip(&farkas.coefficients) {
                let key = (lit.term, lit.value);
                if let Some(&i) = first_idx.get(&key) {
                    coeffs[i] += *coeff;
                } else {
                    first_idx.insert(key, lits.len());
                    lits.push(*lit);
                    coeffs.push(*coeff);
                }
            }
            if lits.len() == conflict.literals.len() {
                // No duplicates — leave the original vectors untouched.
                return;
            }
            conflict.literals = lits;
            conflict.farkas = Some(ay_core::FarkasAnnotation::new(coeffs));
        }
    }
}

/// Verify that a theory conflict is structurally valid.
///
/// This is Phase 1 verification: basic sanity checks on conflict structure.
/// More thorough verification (re-solving, Farkas checks) will be added in later phases.
///
/// # Arguments
/// * `conflict` - The conflict literals from the theory
///
/// # Returns
/// * `Ok(())` if the conflict passes basic validation
/// * `Err(VerificationError)` if structural issues are detected
pub(crate) fn verify_theory_conflict(conflict: &[TheoryLit]) -> Result<(), VerificationError> {
    // Check 1: Conflict must not be empty
    // An empty conflict would mean "unconditionally UNSAT" which is suspicious
    if conflict.is_empty() {
        return Err(VerificationError::EmptyConflict);
    }

    // Check 2: No duplicate or contradictory literals
    // Track (term, value) pairs we've seen
    let mut seen: HashMap<TermId, bool> = Default::default();
    let mut seen_set: HashSet<(TermId, bool)> = Default::default();

    for lit in conflict {
        let key = (lit.term, lit.value);

        // Check for exact duplicate
        if seen_set.contains(&key) {
            return Err(VerificationError::DuplicateLiteral {
                term: lit.term,
                value: lit.value,
            });
        }
        seen_set.insert(key);

        // Check for contradictory (same term, opposite value)
        if let Some(&prev_value) = seen.get(&lit.term) {
            if prev_value != lit.value {
                return Err(VerificationError::ContradictoryLiterals { term: lit.term });
            }
        }
        seen.insert(lit.term, lit.value);
    }

    // Phase 1 passes basic validation
    // Future phases will add:
    // - verify_conflict_unsat() using mini-solver (Phase 2)
    // - verify_farkas() for LRA/LIA conflicts (Phase 2)
    // - verify_congruence() for EUF conflicts (Phase 2)

    Ok(())
}

/// Verify that a theory propagation is structurally valid.
///
/// Checks that the propagation `reason ⊨ literal` is well-formed:
/// 1. Reason set must not be empty (a propagation needs at least one antecedent)
/// 2. No duplicate literals in the reason set
/// 3. The propagated literal must not appear in its own reason set (circularity)
///
/// This is a debug-time check analogous to [`verify_theory_conflict`] for conflicts.
/// A theory solver bug that produces invalid propagations would go undetected on
/// SAT paths (model validation might catch wrong models), but could produce
/// **wrong UNSAT** on UNSAT paths with no defense.
///
/// # Arguments
/// * `propagation` - The theory propagation to verify
///
/// # Returns
/// * `Ok(())` if the propagation passes structural validation
/// * `Err(VerificationError)` if structural issues are detected
pub(crate) fn verify_theory_propagation(
    propagation: &TheoryPropagation,
) -> Result<(), VerificationError> {
    // Check 1: Reason must not be empty
    if propagation.reason.is_empty() {
        return Err(VerificationError::EmptyReason);
    }

    // Check 2: No duplicate literals in reason set
    let mut seen: HashSet<(TermId, bool)> = Default::default();
    for lit in &propagation.reason {
        let key = (lit.term, lit.value);
        if seen.contains(&key) {
            return Err(VerificationError::DuplicateReasonLiteral {
                term: lit.term,
                value: lit.value,
            });
        }
        seen.insert(key);
    }

    // Check 3: Propagated literal must not appear in its own reason set
    // Both same-polarity (tautological) and opposite-polarity (contradictory) are bugs.
    let prop_term = propagation.literal.term;
    for lit in &propagation.reason {
        if lit.term == prop_term {
            return Err(VerificationError::CircularPropagation {
                term: prop_term,
                value: propagation.literal.value,
            });
        }
    }

    Ok(())
}
