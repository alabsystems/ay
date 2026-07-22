// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Negation-decomposition and contraction Alethe proof rules.
//!
//! Contains `not_and`, `not_or`, `not_implies`, `not_equiv`, `not_ite`,
//! and `contraction` validators. Extracted from `boolean_derived.rs`
//! for code health (#5970).

use ay_core::{ProofId, TermId, TermStore};

use super::boolean::{
    clause_matches_expected, clause_matches_unordered, decode_app, decode_ite, err, make_err,
    strip_not, ExpectedLit,
};
use super::ProofCheckError;

pub(crate) fn validate_not_and(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 {
        return err(step, "not_and", "rule requires exactly one unit premise");
    }
    let and_term = strip_not(terms, premise_clauses[0][0])
        .ok_or_else(|| make_err(step, "not_and", "premise must be (not (and ...))"))?;
    let args = decode_app(terms, and_term, "and")
        .ok_or_else(|| make_err(step, "not_and", "premise must negate an and term"))?;
    let expected: Vec<ExpectedLit> = args.iter().map(|&arg| ExpectedLit::Not(arg)).collect();
    if !clause_matches_expected(terms, clause, &expected) {
        return err(
            step,
            "not_and",
            "clause must contain negations of all conjuncts",
        );
    }
    Ok(())
}

pub(crate) fn validate_not_or(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 || clause.len() != 1 {
        return err(
            step,
            "not_or",
            "rule requires one unit premise and one conclusion literal",
        );
    }
    let or_term = strip_not(terms, premise_clauses[0][0])
        .ok_or_else(|| make_err(step, "not_or", "premise must be (not (or ...))"))?;
    let args = decode_app(terms, or_term, "or")
        .ok_or_else(|| make_err(step, "not_or", "premise must negate an or term"))?;
    let negated = strip_not(terms, clause[0])
        .ok_or_else(|| make_err(step, "not_or", "conclusion must be a negation"))?;
    if !args.contains(&negated) {
        return err(step, "not_or", "conclusion must negate a premise disjunct");
    }
    Ok(())
}

pub(crate) fn validate_not_implies1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 || clause.len() != 1 {
        return err(
            step,
            "not_implies1",
            "rule requires one unit premise and one conclusion literal",
        );
    }
    let imp_term = strip_not(terms, premise_clauses[0][0]).ok_or_else(|| {
        make_err(
            step,
            "not_implies1",
            "premise must be a negated implication",
        )
    })?;
    if let Some(args) = decode_app(terms, imp_term, "=>") {
        if args.len() != 2 || clause[0] != args[0] {
            return err(step, "not_implies1", "conclusion must be F1");
        }
        return Ok(());
    }
    if let Some(args) = decode_app(terms, imp_term, "or") {
        if args.len() != 2 {
            return err(step, "not_implies1", "desugared implication must be binary");
        }
        let f1 = strip_not(terms, args[0]).ok_or_else(|| {
            make_err(
                step,
                "not_implies1",
                "desugared implication must start with (not F1)",
            )
        })?;
        if clause[0] != f1 {
            return err(step, "not_implies1", "conclusion must be F1");
        }
        return Ok(());
    }
    err(step, "not_implies1", "premise must negate an implication")
}

pub(crate) fn validate_not_implies2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 || clause.len() != 1 {
        return err(
            step,
            "not_implies2",
            "rule requires one unit premise and one conclusion literal",
        );
    }
    let imp_term = strip_not(terms, premise_clauses[0][0]).ok_or_else(|| {
        make_err(
            step,
            "not_implies2",
            "premise must be a negated implication",
        )
    })?;
    let expected = if let Some(args) = decode_app(terms, imp_term, "=>") {
        if args.len() != 2 {
            return err(step, "not_implies2", "implication must be binary");
        }
        clause[0]
    } else if let Some(args) = decode_app(terms, imp_term, "or") {
        if args.len() != 2 {
            return err(step, "not_implies2", "desugared implication must be binary");
        }
        clause[0]
    } else {
        return err(step, "not_implies2", "premise must negate an implication");
    };
    if strip_not(terms, expected) != Some(args_from_not_implies2(terms, imp_term, step)?) {
        return err(step, "not_implies2", "conclusion must be (not F2)");
    }
    Ok(())
}

pub(crate) fn validate_not_equiv1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 {
        return err(step, "not_equiv1", "rule requires exactly one unit premise");
    }
    let eq_term = strip_not(terms, premise_clauses[0][0])
        .ok_or_else(|| make_err(step, "not_equiv1", "premise must be (not (= ...))"))?;
    let args = decode_app(terms, eq_term, "=")
        .ok_or_else(|| make_err(step, "not_equiv1", "premise must negate an equality"))?;
    if args.len() != 2 || !clause_matches_unordered(clause, args) {
        return err(
            step,
            "not_equiv1",
            "conclusion must contain both equality sides",
        );
    }
    Ok(())
}

pub(crate) fn validate_not_equiv2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 {
        return err(step, "not_equiv2", "rule requires exactly one unit premise");
    }
    let eq_term = strip_not(terms, premise_clauses[0][0])
        .ok_or_else(|| make_err(step, "not_equiv2", "premise must be (not (= ...))"))?;
    let args = decode_app(terms, eq_term, "=")
        .ok_or_else(|| make_err(step, "not_equiv2", "premise must negate an equality"))?;
    if args.len() != 2 {
        return err(step, "not_equiv2", "equality must be binary");
    }
    let expected = [ExpectedLit::Not(args[0]), ExpectedLit::Not(args[1])];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(
            step,
            "not_equiv2",
            "conclusion must negate both equality sides",
        );
    }
    Ok(())
}

pub(crate) fn validate_not_ite1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 {
        return err(step, "not_ite1", "rule requires exactly one unit premise");
    }
    let ite_term = strip_not(terms, premise_clauses[0][0])
        .ok_or_else(|| make_err(step, "not_ite1", "premise must be (not (ite ...))"))?;
    let (c, _t, e) = decode_ite(terms, ite_term)
        .ok_or_else(|| make_err(step, "not_ite1", "premise must negate an ite term"))?;
    let expected = [ExpectedLit::Lit(c), ExpectedLit::Not(e)];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(step, "not_ite1", "conclusion must contain F1 and (not F3)");
    }
    Ok(())
}

pub(crate) fn validate_not_ite2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 {
        return err(step, "not_ite2", "rule requires exactly one unit premise");
    }
    let ite_term = strip_not(terms, premise_clauses[0][0])
        .ok_or_else(|| make_err(step, "not_ite2", "premise must be (not (ite ...))"))?;
    let (c, t, _e) = decode_ite(terms, ite_term)
        .ok_or_else(|| make_err(step, "not_ite2", "premise must negate an ite term"))?;
    let expected = [ExpectedLit::Not(c), ExpectedLit::Not(t)];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(
            step,
            "not_ite2",
            "conclusion must contain (not F1) and (not F2)",
        );
    }
    Ok(())
}

fn args_from_not_implies2(
    terms: &TermStore,
    imp_term: TermId,
    step: ProofId,
) -> Result<TermId, ProofCheckError> {
    if let Some(args) = decode_app(terms, imp_term, "=>") {
        if args.len() != 2 {
            return Err(make_err(step, "not_implies2", "implication must be binary"));
        }
        return Ok(args[1]);
    }
    if let Some(args) = decode_app(terms, imp_term, "or") {
        if args.len() != 2 {
            return Err(make_err(
                step,
                "not_implies2",
                "desugared implication must be binary",
            ));
        }
        return Ok(args[1]);
    }
    Err(make_err(
        step,
        "not_implies2",
        "premise must negate an implication",
    ))
}

/// `ite1`: premise `(cl (ite F1 F2 F3))` ⊢ `(cl F1 F3)`.
pub(crate) fn validate_ite1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 {
        return err(step, "ite1", "rule requires exactly one unit premise");
    }
    let (c, _t, e) = decode_ite(terms, premise_clauses[0][0])
        .ok_or_else(|| make_err(step, "ite1", "premise must be an ite formula"))?;
    let expected = [ExpectedLit::Lit(c), ExpectedLit::Lit(e)];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(step, "ite1", "conclusion must contain F1 and F3");
    }
    Ok(())
}

/// `ite2`: premise `(cl (ite F1 F2 F3))` ⊢ `(cl (not F1) F2)`.
pub(crate) fn validate_ite2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 {
        return err(step, "ite2", "rule requires exactly one unit premise");
    }
    let (c, t, _e) = decode_ite(terms, premise_clauses[0][0])
        .ok_or_else(|| make_err(step, "ite2", "premise must be an ite formula"))?;
    let expected = [ExpectedLit::Not(c), ExpectedLit::Lit(t)];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(step, "ite2", "conclusion must contain (not F1) and F2");
    }
    Ok(())
}

/// `ite_intro`: ⊢ `(cl (= t (and t (ite c (= s a) (= s b)))))` where
/// `s = (ite c a b)` is a term-level ite occurring in `t`.
///
/// This is the self-naming instance of Alethe's `ite_intro` (the ite term
/// itself serves as the definition name), which is the only form the
/// trust-surgery ite-lift emits.
pub(crate) fn validate_ite_intro(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.len() != 1 {
        return err(step, "ite_intro", "conclusion must be a unit clause");
    }
    let eq_args = decode_app(terms, clause[0], "=")
        .ok_or_else(|| make_err(step, "ite_intro", "conclusion must be an equality"))?;
    if eq_args.len() != 2 {
        return err(step, "ite_intro", "equality must be binary");
    }
    let (lhs, rhs) = (eq_args[0], eq_args[1]);
    let and_args = decode_app(terms, rhs, "and")
        .ok_or_else(|| make_err(step, "ite_intro", "right side must be a conjunction"))?;
    if and_args.len() != 2 || and_args[0] != lhs {
        return err(
            step,
            "ite_intro",
            "conjunction must be (and lhs <ite definition>)",
        );
    }
    let (c, def_then, def_else) = decode_ite(terms, and_args[1])
        .ok_or_else(|| make_err(step, "ite_intro", "second conjunct must be an ite formula"))?;
    let then_args = decode_app(terms, def_then, "=")
        .ok_or_else(|| make_err(step, "ite_intro", "then-branch must be an equality"))?;
    let else_args = decode_app(terms, def_else, "=")
        .ok_or_else(|| make_err(step, "ite_intro", "else-branch must be an equality"))?;
    if then_args.len() != 2 || else_args.len() != 2 || then_args[0] != else_args[0] {
        return err(
            step,
            "ite_intro",
            "branch equalities must share the defined ite term",
        );
    }
    let s = then_args[0];
    let (sc, sa, sb) = decode_ite(terms, s)
        .ok_or_else(|| make_err(step, "ite_intro", "defined term must be an ite term"))?;
    if sc != c || sa != then_args[1] || sb != else_args[1] {
        return err(
            step,
            "ite_intro",
            "branch equalities must equate the ite term with its branches",
        );
    }
    // The defined ite term must actually occur in the left side.
    if !term_contains(terms, lhs, s) {
        return err(
            step,
            "ite_intro",
            "defined ite term does not occur in the left side",
        );
    }
    Ok(())
}

/// Whether `needle` occurs in `haystack` (inclusive), by structural walk.
fn term_contains(terms: &TermStore, haystack: TermId, needle: TermId) -> bool {
    let mut stack = vec![haystack];
    let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    while let Some(t) = stack.pop() {
        if t == needle {
            return true;
        }
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            ay_core::term::TermData::Not(inner) => stack.push(*inner),
            ay_core::term::TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            ay_core::term::TermData::App(_, args) => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
}

pub(crate) fn validate_contraction(
    _terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 {
        return err(step, "contraction", "must have exactly 1 premise");
    }
    let premise = premise_clauses[0];
    for &lit in clause {
        if !premise.contains(&lit) {
            return err(
                step,
                "contraction",
                "result literal not found in premise clause",
            );
        }
    }
    for (idx, &lit) in clause.iter().enumerate() {
        if clause[idx + 1..].contains(&lit) {
            return err(step, "contraction", "result clause has duplicate literals");
        }
    }
    for &lit in premise {
        if !clause.contains(&lit) {
            return err(
                step,
                "contraction",
                "premise literal missing from result clause",
            );
        }
    }
    Ok(())
}

/// Validate `weakening`: the conclusion is the premise clause (as an exact
/// leading prefix, mirroring carcara's check) with extra literals appended.
/// Sound unconditionally: a superset of a derived clause is entailed by it.
pub(crate) fn validate_weakening(
    _terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 {
        return err(step, "weakening", "must have exactly 1 premise");
    }
    let premise = premise_clauses[0];
    if clause.len() < premise.len() {
        return err(
            step,
            "weakening",
            "result clause shorter than premise clause",
        );
    }
    if &clause[..premise.len()] != premise {
        return err(
            step,
            "weakening",
            "premise clause is not a prefix of the result clause",
        );
    }
    Ok(())
}
