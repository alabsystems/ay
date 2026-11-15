// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Premise-based clausification rule validation for strict proof checking.
//!
//! The standard `and` rule projects an indexed immediate conjunct from a
//! unit positive premise. The `or` rule decomposes `(assume (or l1 l2 ... ln))` into `(cl l1 l2 ... ln)`.
//! This is the Alethe encoding for multi-literal input clause decomposition,
//! emitted by `SatProofManager` at `sat_proof_manager.rs:286`.

use ay_core::{ProofId, TermId, TermStore};

use super::boolean::{clause_matches_unordered, decode_app, err, make_err};
use super::ProofCheckError;

/// Check standard Alethe `and`: from one unit positive conjunction and one
/// zero-based integer literal index, conclude exactly that immediate child.
///
/// The existing premise owner supplies only earlier clause-bearing premises.
/// Source/assumption authorization remains a whole-proof obligation. All new
/// reads use the caller's shared progress meter; there is no local allowance,
/// heap, term construction, flattening or walk inside an opaque Bool child.
pub(crate) fn validate_and_clausification(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
    arguments: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    use ay_core::{Constant, Sort, Symbol, TermData};
    use num_traits::{Signed, ToPrimitive};

    // Header reservation: schema lengths, entry/sort/head/argument reads,
    // canonical bounded integer conversion, selection and identity checks.
    // Failed attempts keep this debit; the General semantic charge is intact.
    if !progress(32, 0) {
        return Err(ProofCheckError::ResourceLimit);
    }
    let invalid = || ProofCheckError::InvalidAnd { step };
    let [premise] = premise_clauses else {
        return Err(invalid());
    };
    let &[source] = *premise else {
        return Err(invalid());
    };
    let &[conclusion] = clause else {
        return Err(invalid());
    };
    let &[argument] = arguments else {
        return Err(invalid());
    };
    for term in [source, conclusion, argument] {
        if terms.entry_stamp(term).is_none() {
            return Err(invalid());
        }
    }
    if terms.sort(source) != &Sort::Bool
        || terms.sort(conclusion) != &Sort::Bool
        || terms.sort(argument) != &Sort::Int
    {
        return Err(invalid());
    }
    let TermData::App(Symbol::Named(head), children) = terms.get(source) else {
        return Err(invalid());
    };
    if head != "and" || children.is_empty() {
        return Err(invalid());
    }
    let TermData::Const(Constant::Int(index)) = terms.get(argument) else {
        return Err(invalid());
    };
    if index.is_negative() || index.bits() > u64::from(usize::BITS) {
        return Err(invalid());
    }
    let index = index.to_usize().ok_or_else(invalid)?;
    if children.get(index).copied() != Some(conclusion) {
        return Err(invalid());
    }

    // Recompute immediate builtin typing, including every unused sibling ID.
    // Eight units cover each poll, slot, entry and cached Bool-sort check;
    // the constant tail covers loop setup/completion. Reserve before scanning.
    let work = children
        .len()
        .checked_mul(8)
        .and_then(|n| n.checked_add(8))
        .ok_or(ProofCheckError::ResourceLimit)?;
    if !progress(work, 0) {
        return Err(ProofCheckError::ResourceLimit);
    }
    for &child in children {
        if !progress(0, 0) {
            return Err(ProofCheckError::ResourceLimit);
        }
        if terms.entry_stamp(child).is_none() || terms.sort(child) != &Sort::Bool {
            return Err(invalid());
        }
    }
    Ok(())
}

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

#[cfg(test)]
mod tests;
