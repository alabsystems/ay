// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode semantic validation for `TheoryLemmaKind::LiaGeneric` proof steps.
//!
//! When an `LiaAnnotation` is present, delegates to the corresponding
//! `ay_core::proof_validation::validate_lia_theory_lemma` validator.
//!
//! When no annotation is present, falls back to Farkas validation (same as LRA)
//! since many LIA conflicts are pure bounds gaps that the Farkas validator
//! can verify without integer-specific reasoning.

use ay_core::term::TermData;
use ay_core::{FarkasAnnotation, LiaAnnotation, ProofId, Sort, Symbol, TermId, TermStore};

use super::ProofCheckError;

/// Validate Alethe's `la_disequality` split:
///
/// ```text
/// (cl (or (= a b) (not (<= a b)) (not (<= b a))))
/// ```
///
/// This is the linear-order antisymmetry tautology used to split an arithmetic
/// disequality.  The rule is self-certifying: its exact term shape is the
/// certificate, so strict mode checks the operands and both opposite bounds
/// rather than trusting the producer's classification.
pub(crate) fn validate_la_disequality(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
) -> Result<(), ProofCheckError> {
    let invalid = |reason: &str| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: format!("invalid la_disequality: {reason}"),
    };
    if premise_count != 0 || !args.is_empty() {
        return Err(invalid("rule must be premiseless and have no arguments"));
    }
    let [or_term] = clause else {
        return Err(invalid(
            "conclusion must be a unit clause containing an or-term",
        ));
    };
    let TermData::App(Symbol::Named(or_name), disjuncts) = terms.get(*or_term) else {
        return Err(invalid("unit conclusion is not an or-term"));
    };
    if or_name != "or" || disjuncts.len() != 3 {
        return Err(invalid("or-term must have exactly three disjuncts"));
    }

    let decode_eq = |term| match terms.get(term) {
        TermData::App(Symbol::Named(name), operands) if name == "=" && operands.len() == 2 => {
            Some((operands[0], operands[1]))
        }
        _ => None,
    };
    let decode_not_le = |term| {
        let TermData::Not(inner) = terms.get(term) else {
            return None;
        };
        match terms.get(*inner) {
            TermData::App(Symbol::Named(name), operands) if name == "<=" && operands.len() == 2 => {
                Some((operands[0], operands[1]))
            }
            _ => None,
        }
    };

    // Alethe fixes all three positions in the packed `or` term. The outer
    // proof conclusion is a unit clause, but the `or` term's children are not
    // an unordered clause: accepting a permutation here would diverge from
    // Carcara's `la_disequality` rule.
    let (lhs, rhs) = decode_eq(disjuncts[0])
        .ok_or_else(|| invalid("first disjunct must be a binary equality"))?;
    let lhs_sort = terms.sort(lhs);
    if lhs_sort != terms.sort(rhs) || !matches!(lhs_sort, Sort::Int | Sort::Real) {
        return Err(invalid(
            "equality operands must have the same arithmetic sort",
        ));
    }
    let b1 = decode_not_le(disjuncts[1])
        .ok_or_else(|| invalid("second disjunct must negate a <= atom"))?;
    let b2 = decode_not_le(disjuncts[2])
        .ok_or_else(|| invalid("third disjunct must negate a <= atom"))?;
    if b1 != (lhs, rhs) || b2 != (rhs, lhs) {
        return Err(invalid(
            "negated bounds must follow the equality operands in forward then reverse order",
        ));
    }
    Ok(())
}

/// Validate an `LiaGeneric` theory lemma in strict mode.
///
/// Strategy:
/// 1. If an `LiaAnnotation` is present, use the LIA-specific validator.
/// 2. If only a `FarkasAnnotation` is present (no LIA annotation), fall back
///    to the shared Farkas validator (same as LRA). This handles the common
///    case where LIA conflicts are simple bounds gaps.
/// 3. If neither annotation is present, reject.
pub(crate) fn validate_lia_generic(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
    lia: Option<&LiaAnnotation>,
) -> Result<(), ProofCheckError> {
    if let Some(lia_ann) = lia {
        // LIA-specific validation
        ay_core::proof_validation::validate_lia_theory_lemma(
            terms, step_id, clause, farkas, lia_ann,
        )
        .map_err(|e| ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: e.to_string(),
        })
    } else if farkas.is_some() {
        // Fall back to Farkas validation (same as LRA)
        super::lra_farkas::validate_lra_farkas(terms, step_id, clause, farkas)
    } else {
        Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "LiaGeneric in strict mode requires either LiaAnnotation or FarkasAnnotation"
                .to_string(),
        })
    }
}
