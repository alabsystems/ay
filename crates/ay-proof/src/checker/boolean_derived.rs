// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equiv/ITE/XOR tautology rules and eq_reflexive Alethe rule.
//!
//! Negation-decomposition rules (`not_and`, `not_or`, etc.) and `contraction`
//! are in [`boolean_negation`]. Uses shared utilities from the `boolean` module.

use ay_core::{ProofId, TermId, TermStore};

use super::boolean::{
    clause_matches_expected, clause_matches_unordered, decode_app, err, find_app, find_ite,
    find_negated_app, find_negated_ite, make_err, ExpectedLit,
};
use super::ProofCheckError;

// ---- Equiv tautology rules ----

pub(crate) fn validate_equiv_pos1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let (not_eq, args) = find_negated_app(terms, clause, "=")
        .ok_or_else(|| make_err(step, "equiv_pos1", "clause must contain (not (= ...))"))?;
    if args.len() != 2 {
        return err(step, "equiv_pos1", "equality must be binary");
    }
    let expected = [
        ExpectedLit::Lit(not_eq),
        ExpectedLit::Lit(args[0]),
        ExpectedLit::Not(args[1]),
    ];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(step, "equiv_pos1", "clause shape does not match equality");
    }
    Ok(())
}

pub(crate) fn validate_equiv_pos2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let (not_eq, args) = find_negated_app(terms, clause, "=")
        .ok_or_else(|| make_err(step, "equiv_pos2", "clause must contain (not (= ...))"))?;
    if args.len() != 2 {
        return err(step, "equiv_pos2", "equality must be binary");
    }
    let expected = [
        ExpectedLit::Lit(not_eq),
        ExpectedLit::Not(args[0]),
        ExpectedLit::Lit(args[1]),
    ];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(step, "equiv_pos2", "clause shape does not match equality");
    }
    Ok(())
}

pub(crate) fn validate_equiv_neg1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let (eq_term, args) = find_app(terms, clause, "=")
        .ok_or_else(|| make_err(step, "equiv_neg1", "clause must contain an equality"))?;
    if args.len() != 2 {
        return err(step, "equiv_neg1", "equality must be binary");
    }
    let expected = [
        ExpectedLit::Lit(eq_term),
        ExpectedLit::Not(args[0]),
        ExpectedLit::Not(args[1]),
    ];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(step, "equiv_neg1", "clause shape does not match equality");
    }
    Ok(())
}

pub(crate) fn validate_equiv_neg2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let (eq_term, args) = find_app(terms, clause, "=")
        .ok_or_else(|| make_err(step, "equiv_neg2", "clause must contain an equality"))?;
    if args.len() != 2 {
        return err(step, "equiv_neg2", "equality must be binary");
    }
    let expected = [eq_term, args[0], args[1]];
    if !clause_matches_unordered(clause, &expected) {
        return err(step, "equiv_neg2", "clause shape does not match equality");
    }
    Ok(())
}

// ---- ITE tautology rules ----

pub(crate) fn validate_ite_pos1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let (not_ite, (c, _t, e)) = find_negated_ite(terms, clause)
        .ok_or_else(|| make_err(step, "ite_pos1", "clause must contain (not (ite ...))"))?;
    let expected = [not_ite, c, e];
    if !clause_matches_unordered(clause, &expected) {
        return err(step, "ite_pos1", "clause shape does not match ite");
    }
    Ok(())
}

pub(crate) fn validate_ite_pos2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let (not_ite, (c, t, _e)) = find_negated_ite(terms, clause)
        .ok_or_else(|| make_err(step, "ite_pos2", "clause must contain (not (ite ...))"))?;
    let expected = [
        ExpectedLit::Lit(not_ite),
        ExpectedLit::Not(c),
        ExpectedLit::Lit(t),
    ];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(step, "ite_pos2", "clause shape does not match ite");
    }
    Ok(())
}

pub(crate) fn validate_ite_neg1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let (ite, (c, _t, e)) = find_ite(terms, clause)
        .ok_or_else(|| make_err(step, "ite_neg1", "clause must contain an ite term"))?;
    let expected = [
        ExpectedLit::Lit(ite),
        ExpectedLit::Lit(c),
        ExpectedLit::Not(e),
    ];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(step, "ite_neg1", "clause shape does not match ite");
    }
    Ok(())
}

pub(crate) fn validate_ite_neg2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let (ite, (c, t, _e)) = find_ite(terms, clause)
        .ok_or_else(|| make_err(step, "ite_neg2", "clause must contain an ite term"))?;
    let expected = [
        ExpectedLit::Lit(ite),
        ExpectedLit::Not(c),
        ExpectedLit::Not(t),
    ];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(step, "ite_neg2", "clause shape does not match ite");
    }
    Ok(())
}

// ---- XOR tautology rules ----

pub(crate) fn validate_xor_pos1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let (not_xor, args) = find_negated_app(terms, clause, "xor")
        .ok_or_else(|| make_err(step, "xor_pos1", "clause must contain (not (xor ...))"))?;
    if args.len() != 2 {
        return err(step, "xor_pos1", "xor must be binary");
    }
    let expected = [not_xor, args[0], args[1]];
    if !clause_matches_unordered(clause, &expected) {
        return err(step, "xor_pos1", "clause shape does not match xor");
    }
    Ok(())
}

pub(crate) fn validate_xor_pos2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let (not_xor, args) = find_negated_app(terms, clause, "xor")
        .ok_or_else(|| make_err(step, "xor_pos2", "clause must contain (not (xor ...))"))?;
    if args.len() != 2 {
        return err(step, "xor_pos2", "xor must be binary");
    }
    let expected = [
        ExpectedLit::Lit(not_xor),
        ExpectedLit::Not(args[0]),
        ExpectedLit::Not(args[1]),
    ];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(step, "xor_pos2", "clause shape does not match xor");
    }
    Ok(())
}

pub(crate) fn validate_xor_neg1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let (xor_term, args) = find_app(terms, clause, "xor")
        .ok_or_else(|| make_err(step, "xor_neg1", "clause must contain a xor term"))?;
    if args.len() != 2 {
        return err(step, "xor_neg1", "xor must be binary");
    }
    let expected = [
        ExpectedLit::Lit(xor_term),
        ExpectedLit::Lit(args[0]),
        ExpectedLit::Not(args[1]),
    ];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(step, "xor_neg1", "clause shape does not match xor");
    }
    Ok(())
}

pub(crate) fn validate_xor_neg2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let (xor_term, args) = find_app(terms, clause, "xor")
        .ok_or_else(|| make_err(step, "xor_neg2", "clause must contain a xor term"))?;
    if args.len() != 2 {
        return err(step, "xor_neg2", "xor must be binary");
    }
    let expected = [
        ExpectedLit::Lit(xor_term),
        ExpectedLit::Not(args[0]),
        ExpectedLit::Lit(args[1]),
    ];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(step, "xor_neg2", "clause shape does not match xor");
    }
    Ok(())
}

// ---- Derived (premise-based) rules ----

pub(crate) fn validate_eq_reflexive(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.len() != 1 {
        return err(step, "eq_reflexive", "clause must have exactly 1 literal");
    }
    let args = decode_app(terms, clause[0], "=")
        .ok_or_else(|| make_err(step, "eq_reflexive", "literal must be an equality"))?;
    if args.len() != 2 {
        return err(step, "eq_reflexive", "equality must be binary");
    }
    if args[0] != args[1] {
        return err(step, "eq_reflexive", "equality must be reflexive");
    }
    Ok(())
}

/// `eq_symmetric`: `(cl (= (= a b) (= b a)))` — an equivalence between a
/// binary equality and its argument-swapped orientation.
pub(crate) fn validate_eq_symmetric(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.len() != 1 {
        return err(step, "eq_symmetric", "clause must have exactly 1 literal");
    }
    let outer = decode_app(terms, clause[0], "=")
        .ok_or_else(|| make_err(step, "eq_symmetric", "literal must be an equivalence"))?;
    if outer.len() != 2 {
        return err(step, "eq_symmetric", "equivalence must be binary");
    }
    let lhs = decode_app(terms, outer[0], "=")
        .ok_or_else(|| make_err(step, "eq_symmetric", "lhs must be an equality"))?;
    let rhs = decode_app(terms, outer[1], "=")
        .ok_or_else(|| make_err(step, "eq_symmetric", "rhs must be an equality"))?;
    if lhs.len() != 2 || rhs.len() != 2 {
        return err(step, "eq_symmetric", "equalities must be binary");
    }
    if lhs[0] != rhs[1] || lhs[1] != rhs[0] {
        return err(step, "eq_symmetric", "rhs must be the argument-swapped lhs");
    }
    Ok(())
}
