// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boolean Alethe rule validation for strict proof checking.
//!
//! This module covers and/or/implies tautology rules.
//! See [`boolean_derived`] for equiv/ite/xor tautology and premise-based rules.

use ay_core::{ProofId, Symbol, TermData, TermId, TermStore};

use super::ProofCheckError;

// ---- Shared utilities (used by both boolean.rs and boolean_derived.rs) ----

pub(crate) fn strip_not(terms: &TermStore, term: TermId) -> Option<TermId> {
    match terms.get(term) {
        TermData::Not(inner) => Some(*inner),
        _ => None,
    }
}

pub(crate) fn decode_app<'a>(
    terms: &'a TermStore,
    term: TermId,
    name: &str,
) -> Option<&'a [TermId]> {
    match terms.get(term) {
        TermData::App(Symbol::Named(n), args) if n == name => Some(args),
        _ => None,
    }
}

pub(crate) fn decode_ite(terms: &TermStore, term: TermId) -> Option<(TermId, TermId, TermId)> {
    match terms.get(term) {
        TermData::Ite(c, t, e) => Some((*c, *t, *e)),
        // After proof rewriting, ITE may appear as App("ite", [c, t, e])
        // instead of the canonical Ite form (#6365).
        TermData::App(Symbol::Named(name), args) if name == "ite" && args.len() == 3 => {
            Some((args[0], args[1], args[2]))
        }
        _ => None,
    }
}

pub(crate) fn find_negated_app<'a>(
    terms: &'a TermStore,
    clause: &[TermId],
    name: &str,
) -> Option<(TermId, &'a [TermId])> {
    clause.iter().copied().find_map(|lit| {
        let inner = strip_not(terms, lit)?;
        let args = decode_app(terms, inner, name)?;
        Some((lit, args))
    })
}

pub(crate) fn find_app<'a>(
    terms: &'a TermStore,
    clause: &[TermId],
    name: &str,
) -> Option<(TermId, &'a [TermId])> {
    clause
        .iter()
        .copied()
        .find_map(|lit| decode_app(terms, lit, name).map(|args| (lit, args)))
}

pub(crate) fn find_negated_ite(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<(TermId, (TermId, TermId, TermId))> {
    clause.iter().copied().find_map(|lit| {
        let inner = strip_not(terms, lit)?;
        let ite = decode_ite(terms, inner)?;
        Some((lit, ite))
    })
}

pub(crate) fn find_ite(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<(TermId, (TermId, TermId, TermId))> {
    clause
        .iter()
        .copied()
        .find_map(|lit| decode_ite(terms, lit).map(|ite| (lit, ite)))
}

fn decode_and_source<'a>(
    terms: &'a TermStore,
    source_term: Option<TermId>,
    clause: &[TermId],
) -> Option<&'a [TermId]> {
    source_term
        .and_then(|term| decode_app(terms, term, "and"))
        .or_else(|| find_app(terms, clause, "and").map(|(_, args)| args))
        .or_else(|| find_negated_app(terms, clause, "and").map(|(_, args)| args))
}

#[derive(Clone, Copy)]
pub(crate) enum ExpectedLit {
    Lit(TermId),
    Not(TermId),
}

pub(crate) fn clause_matches_unordered(clause: &[TermId], expected: &[TermId]) -> bool {
    if clause.len() != expected.len() {
        return false;
    }

    let mut matched = vec![false; expected.len()];
    for &lit in clause {
        let Some((idx, _)) = expected
            .iter()
            .enumerate()
            .find(|(idx, candidate)| !matched[*idx] && **candidate == lit)
        else {
            return false;
        };
        matched[idx] = true;
    }

    true
}

pub(crate) fn matches_negated_components(
    terms: &TermStore,
    items: &[TermId],
    expected: &[TermId],
) -> bool {
    if items.len() != expected.len() {
        return false;
    }

    let mut matched = vec![false; expected.len()];
    for &component in items {
        let Some((idx, _)) = expected.iter().enumerate().find(|(idx, expected_term)| {
            !matched[*idx] && matches_negation_of_term(terms, component, **expected_term)
        }) else {
            return false;
        };
        matched[idx] = true;
    }

    true
}

pub(crate) fn matches_negation_of_term(terms: &TermStore, lit: TermId, term: TermId) -> bool {
    if strip_not(terms, lit) == Some(term) {
        return true;
    }

    match terms.get(term) {
        TermData::Not(inner) => matches_positive_literal_of_term(terms, lit, *inner),
        TermData::App(Symbol::Named(name), args) if name == "and" => {
            let Some(disj_args) = decode_app(terms, lit, "or") else {
                return false;
            };
            disj_args.len() == args.len() && matches_negated_components(terms, disj_args, args)
        }
        TermData::App(Symbol::Named(name), args) if name == "or" => {
            let Some(conj_args) = decode_app(terms, lit, "and") else {
                return false;
            };
            conj_args.len() == args.len() && matches_negated_components(terms, conj_args, args)
        }
        _ => false,
    }
}

pub(crate) fn matches_positive_literal_of_term(
    terms: &TermStore,
    lit: TermId,
    term: TermId,
) -> bool {
    if lit == term {
        return true;
    }

    matches!(
        terms.get(term),
        TermData::App(Symbol::Named(name), _) if name == "and"
    ) && strip_not(terms, lit).is_some_and(|inner| matches_negation_of_term(terms, inner, term))
}

pub(crate) fn clause_matches_expected(
    terms: &TermStore,
    clause: &[TermId],
    expected: &[ExpectedLit],
) -> bool {
    if clause.len() != expected.len() {
        return false;
    }

    let mut matched = vec![false; expected.len()];
    for &lit in clause {
        let Some((idx, _)) = expected.iter().enumerate().find(|(idx, expected_lit)| {
            if matched[*idx] {
                return false;
            }
            match expected_lit {
                ExpectedLit::Lit(term) => lit == *term,
                ExpectedLit::Not(term) => strip_not(terms, lit) == Some(*term),
            }
        }) else {
            return false;
        };
        matched[idx] = true;
    }

    true
}

pub(crate) fn make_err(step: ProofId, rule: &str, reason: &str) -> ProofCheckError {
    ProofCheckError::InvalidBooleanRule {
        step,
        rule: rule.to_string(),
        reason: reason.to_string(),
    }
}

pub(crate) fn err(step: ProofId, rule: &str, reason: &str) -> Result<(), ProofCheckError> {
    Err(make_err(step, rule, reason))
}

// ---- And/Or/Implies tautology rules ----

pub(crate) fn validate_and_pos(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    position: u32,
    source_term: Option<TermId>,
) -> Result<(), ProofCheckError> {
    if clause.len() != 2 {
        return err(step, "and_pos", "clause must have exactly 2 literals");
    }
    let args = decode_and_source(terms, source_term, clause)
        .ok_or_else(|| make_err(step, "and_pos", "could not determine and-source term"))?;
    let index = position as usize;
    if index >= args.len() {
        return err(step, "and_pos", "position index out of range");
    }
    let has_gate = clause.iter().copied().any(|lit| {
        source_term.is_some_and(|term| matches_negation_of_term(terms, lit, term))
            || strip_not(terms, lit)
                .and_then(|inner| decode_app(terms, inner, "and"))
                .is_some_and(|inner_args| inner_args == args)
    });
    let has_conjunct = clause
        .iter()
        .copied()
        .any(|lit| matches_positive_literal_of_term(terms, lit, args[index]));
    if !(has_gate && has_conjunct) {
        return err(
            step,
            "and_pos",
            "clause must contain the and gate literal and the indexed conjunct",
        );
    }
    Ok(())
}

pub(crate) fn validate_and_neg(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    source_term: Option<TermId>,
) -> Result<(), ProofCheckError> {
    let args = decode_and_source(terms, source_term, clause)
        .ok_or_else(|| make_err(step, "and_neg", "could not determine and-source term"))?;
    if clause.len() != args.len() + 1 {
        return err(
            step,
            "and_neg",
            "clause must have exactly n+1 literals (the conjunction plus n negated conjuncts)",
        );
    }
    // Exact multiset match, NOT a count. and_neg is the tautology
    // (and a1..an) ∨ ¬a1 ∨ .. ∨ ¬an, so the clause must contain the positive
    // conjunction exactly once and the negation of EACH conjunct exactly once.
    // Counting how many literals negate *some* arg is unsound: a duplicated ¬ai
    // (e.g. [(and a b), ¬a, ¬a]) makes the count reach n while a different
    // conjunct's negation (¬b) is missing, admitting a non-tautological clause
    // (falsified at a=true, b=false) — a meta-false-PROVE. Partition off one gate
    // literal, then require the remaining n literals to bijectively match the
    // negations of all n conjuncts (matches_negated_components enforces both the
    // length and the per-arg one-to-one cover).
    let mut gate_matched = false;
    let mut negated: Vec<TermId> = Vec::with_capacity(args.len());
    for &lit in clause {
        let is_gate = source_term
            .is_some_and(|term| matches_positive_literal_of_term(terms, lit, term))
            || decode_app(terms, lit, "and").is_some_and(|inner_args| inner_args == args);
        if is_gate && !gate_matched {
            gate_matched = true;
        } else {
            negated.push(lit);
        }
    }
    if !gate_matched || !matches_negated_components(terms, &negated, args) {
        return err(
            step,
            "and_neg",
            "clause must contain the conjunction and the negation of each conjunct exactly once",
        );
    }
    Ok(())
}

pub(crate) fn validate_or_pos(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let (not_or, args) = find_negated_app(terms, clause, "or")
        .ok_or_else(|| make_err(step, "or_pos", "clause must contain (not (or ...))"))?;
    let mut expected = Vec::with_capacity(args.len() + 1);
    expected.push(not_or);
    expected.extend(args.iter().copied());
    if !clause_matches_unordered(clause, &expected) {
        return err(
            step,
            "or_pos",
            "clause must contain (not (or ...)) and all disjuncts",
        );
    }
    Ok(())
}

pub(crate) fn validate_or_neg(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.len() != 2 {
        return err(step, "or_neg", "clause must have exactly 2 literals");
    }
    let (or_term, args) = find_app(terms, clause, "or")
        .ok_or_else(|| make_err(step, "or_neg", "clause must contain an or term"))?;
    let Some(complement) = clause.iter().copied().find(|&lit| lit != or_term) else {
        return err(step, "or_neg", "clause must contain a disjunct complement");
    };
    // Proof IR uses Boolean-normalized literals: when the selected disjunct is
    // itself `(not a)`, its complement can be stored as `a` rather than the
    // raw `(not (not a))` required by Alethe.  This remains exact, not a
    // propositional shortcut: `matches_negation_of_term` accepts only the
    // syntactic complement (including this one double-negation cancellation).
    // The Alethe printer expands the compact form into `or_neg`, `not_not`, and
    // resolution before external checking.
    if !args
        .iter()
        .any(|&disjunct| matches_negation_of_term(terms, complement, disjunct))
        || !clause_matches_unordered(clause, &[or_term, complement])
    {
        return err(
            step,
            "or_neg",
            "clause must contain the disjunction and an exact disjunct complement",
        );
    }
    Ok(())
}

pub(crate) fn validate_implies_pos(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.len() != 3 {
        return err(step, "implies_pos", "clause must have exactly 3 literals");
    }
    let Some((neg_imp, args, native)) = clause.iter().copied().find_map(|lit| {
        let inner = strip_not(terms, lit)?;
        if let Some(args) = decode_app(terms, inner, "=>") {
            Some((lit, args, true))
        } else {
            decode_app(terms, inner, "or").map(|args| (lit, args, false))
        }
    }) else {
        return err(
            step,
            "implies_pos",
            "clause must contain a negated implication or desugared disjunction",
        );
    };
    let expected = if native {
        if args.len() != 2 {
            return err(step, "implies_pos", "implies must be binary");
        }
        vec![
            ExpectedLit::Lit(neg_imp),
            ExpectedLit::Not(args[0]),
            ExpectedLit::Lit(args[1]),
        ]
    } else {
        if args.len() != 2 {
            return err(step, "implies_pos", "desugared implication must be binary");
        }
        vec![
            ExpectedLit::Lit(neg_imp),
            ExpectedLit::Lit(args[0]),
            ExpectedLit::Lit(args[1]),
        ]
    };
    if !clause_matches_expected(terms, clause, &expected) {
        return err(
            step,
            "implies_pos",
            "clause shape does not match implication",
        );
    }
    Ok(())
}

pub(crate) fn validate_implies_neg1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.len() != 2 {
        return err(step, "implies_neg1", "clause must have exactly 2 literals");
    }
    let Some((imp_lit, args, native)) = clause.iter().copied().find_map(|lit| {
        if let Some(args) = decode_app(terms, lit, "=>") {
            Some((lit, args, true))
        } else {
            decode_app(terms, lit, "or").map(|args| (lit, args, false))
        }
    }) else {
        return err(
            step,
            "implies_neg1",
            "clause must contain an implication or desugared disjunction",
        );
    };
    let rhs = if native {
        if args.len() != 2 {
            return err(step, "implies_neg1", "implies must be binary");
        }
        args[0]
    } else {
        if args.len() != 2 {
            return err(step, "implies_neg1", "desugared implication must be binary");
        }
        strip_not(terms, args[0]).ok_or_else(|| {
            make_err(
                step,
                "implies_neg1",
                "desugared implication must start with (not F1)",
            )
        })?
    };
    if !clause_matches_unordered(clause, &[imp_lit, rhs]) {
        return err(
            step,
            "implies_neg1",
            "clause shape does not match implication",
        );
    }
    Ok(())
}

pub(crate) fn validate_implies_neg2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.len() != 2 {
        return err(step, "implies_neg2", "clause must have exactly 2 literals");
    }
    let Some((imp_lit, args, _native)) = clause.iter().copied().find_map(|lit| {
        if let Some(args) = decode_app(terms, lit, "=>") {
            Some((lit, args, true))
        } else {
            decode_app(terms, lit, "or").map(|args| (lit, args, false))
        }
    }) else {
        return err(
            step,
            "implies_neg2",
            "clause must contain an implication or desugared disjunction",
        );
    };
    if args.len() != 2 {
        return err(step, "implies_neg2", "implication must be binary");
    }
    let expected = [ExpectedLit::Lit(imp_lit), ExpectedLit::Not(args[1])];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(
            step,
            "implies_neg2",
            "clause shape does not match implication",
        );
    }
    Ok(())
}
