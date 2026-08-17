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

/// Validate the exact flat conclusion of [`validate_la_disequality`].
pub(crate) fn validate_arith_eq_triangle(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let invalid = |reason: &str| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: format!("invalid arithmetic equality triangle: {reason}"),
    };
    let [not_forward, not_reverse, equality] = clause else {
        return Err(invalid("clause must contain exactly three literals"));
    };
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
    let (lhs, rhs) =
        decode_eq(*equality).ok_or_else(|| invalid("third literal must be a binary equality"))?;
    let sort = terms.sort(lhs);
    if sort != terms.sort(rhs) || !matches!(sort, Sort::Int | Sort::Real) {
        return Err(invalid("equality operands must share Int or Real sort"));
    }
    if decode_not_le(*not_forward) != Some((lhs, rhs))
        || decode_not_le(*not_reverse) != Some((rhs, lhs))
    {
        return Err(invalid(
            "first two literals must negate the forward and reverse <= atoms",
        ));
    }
    Ok(())
}

/// Validate one exact equality-adapter implication, `a=b => a<=b` (or its
/// reverse bound).  The kind cannot authorize an arbitrary arithmetic clause.
pub(crate) fn validate_arith_eq_implies_bound(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let invalid = |reason: &str| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: format!("invalid arithmetic equality implication: {reason}"),
    };
    let [not_equality, bound] = clause else {
        return Err(invalid("clause must contain exactly two literals"));
    };
    let TermData::Not(equality) = terms.get(*not_equality) else {
        return Err(invalid("first literal must negate an equality"));
    };
    let TermData::App(Symbol::Named(eq_name), eq_args) = terms.get(*equality) else {
        return Err(invalid("first literal must negate a binary equality"));
    };
    if eq_name != "=" || eq_args.len() != 2 {
        return Err(invalid("first literal must negate a binary equality"));
    }
    let (lhs, rhs) = (eq_args[0], eq_args[1]);
    let sort = terms.sort(lhs);
    if sort != terms.sort(rhs) || !matches!(sort, Sort::Int | Sort::Real) {
        return Err(invalid("equality operands must share Int or Real sort"));
    }
    let TermData::App(Symbol::Named(bound_name), bound_args) = terms.get(*bound) else {
        return Err(invalid("second literal must be a <= atom"));
    };
    if bound_name != "<=" || bound_args.len() != 2 {
        return Err(invalid("second literal must be a <= atom"));
    }
    if (bound_args[0], bound_args[1]) != (lhs, rhs) && (bound_args[0], bound_args[1]) != (rhs, lhs)
    {
        return Err(invalid(
            "bound operands must be exactly the equality operands",
        ));
    }
    Ok(())
}

pub(crate) fn validate_int_bounds_tautology(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if ay_core::proof_validation::recognize_int_bounds_tautology(terms, clause) {
        Ok(())
    } else {
        Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "integer split clause does not negate to contradictory exact bounds"
                .to_string(),
        })
    }
}

pub(crate) fn validate_arith_disequality_split(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if ay_core::proof_validation::recognize_arith_disequality_split(terms, clause) {
        Ok(())
    } else {
        Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "guarded arithmetic split does not match its equality operands".to_string(),
        })
    }
}

/// Validate an `LiaGeneric` theory lemma under a caller-owned envelope.
///
/// Strategy:
/// 1. If an `LiaAnnotation` is present, use the LIA-specific validator.
/// 2. If only a `FarkasAnnotation` is present (no LIA annotation), fall back
///    to the shared Farkas validator (same as LRA). This handles the common
///    case where LIA conflicts are simple bounds gaps.
/// 3. If neither annotation is present, reject.
pub(crate) fn validate_metered(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
    lia: Option<&LiaAnnotation>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
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
        super::lra_farkas::validate_metered(terms, step_id, clause, farkas, progress)
    } else {
        Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "LiaGeneric in strict mode requires either LiaAnnotation or FarkasAnnotation"
                .to_string(),
        })
    }
}
