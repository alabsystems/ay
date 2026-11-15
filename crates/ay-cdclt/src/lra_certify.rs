// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Farkas certificates for LRA clauses that carry none (design P1).
//!
//! A simplex conflict comes with its Farkas coefficients. A bound
//! propagation's reason does not: LRA derives it from row intervals and hands
//! back only the antecedent literals. When proofs are on, the plug-in turns
//! such a clause into an `la_generic` instance by refuting the clause's
//! negation with a private simplex over exactly its atoms. The private solver
//! sees nothing but that clause, so its certificate is about that clause
//! alone, and the checkers verify it independently.

use ay_core::{
    FarkasAnnotation, Sort, TermData, TermId, TermStore, TheoryLemmaKind, TheoryLit, TheoryResult,
    TheorySolver,
};
use ay_lra::LraSolver;
use num_rational::Rational64;
use num_traits::{CheckedAdd, Zero};

use crate::plugin::{HintPremise, ProofHint};

/// A checkable hint for `clause`, a disjunction the caller holds to be valid
/// in linear real arithmetic, or `None`.
///
/// A clause whose negation is a conjunction of bounds gets Farkas
/// coefficients (`la_generic`). A clause with one positive equality
/// `(= s t)` has a disequality in its negation, which no Farkas certificate
/// covers; it is derived instead from `rest ∨ s ≤ t` and `rest ∨ t ≤ s` (each
/// with its own certificate) and the triangle `¬(s ≤ t) ∨ ¬(t ≤ s) ∨ s = t`
/// (`la_disequality`), by resolution.
pub(crate) fn certify_clause(terms: &mut TermStore, clause: &[TheoryLit]) -> Option<ProofHint> {
    if let Some(farkas) = farkas_for_clause(terms, clause) {
        return Some(ProofHint::farkas(farkas));
    }
    let equalities: Vec<(usize, TermId, TermId, TermId)> = clause
        .iter()
        .enumerate()
        .filter_map(|(pos, lit)| {
            let (atom, value) = strip_not(terms, lit.term, lit.value);
            let TermData::App(sym, args) = terms.get(atom) else {
                return None;
            };
            match (sym.name(), args.as_slice(), value) {
                ("=", &[s, t], true) if matches!(terms.sort(s), Sort::Real | Sort::Int) => {
                    Some((pos, atom, s, t))
                }
                _ => None,
            }
        })
        .collect();
    let [(pos, equality, s, t)] = equalities[..] else {
        return None;
    };
    let forward = terms.mk_le(s, t);
    let reverse = terms.mk_le(t, s);
    let is_bound = |term: TermId, lhs: TermId, rhs: TermId| {
        matches!(terms.get(term), TermData::App(sym, args)
            if sym.name() == "<=" && args.as_slice() == [lhs, rhs])
    };
    if !is_bound(forward, s, t) || !is_bound(reverse, t, s) {
        return None;
    }
    let rest: Vec<TheoryLit> = clause
        .iter()
        .enumerate()
        .filter(|&(p, _)| p != pos)
        .map(|(_, lit)| *lit)
        .collect();
    let mut premises = Vec::with_capacity(3);
    for bound in [forward, reverse] {
        let mut side = rest.clone();
        side.push(TheoryLit::new(bound, true));
        let farkas = farkas_for_clause(terms, &side)?;
        premises.push(HintPremise {
            clause: side,
            hint: ProofHint::farkas(farkas),
        });
    }
    premises.push(HintPremise {
        clause: vec![
            TheoryLit::new(forward, false),
            TheoryLit::new(reverse, false),
            TheoryLit::new(equality, true),
        ],
        hint: ProofHint::kind(TheoryLemmaKind::ArithEqTriangle),
    });
    Some(ProofHint::derived(premises))
}

/// Farkas coefficients for `clause`, a disjunction the caller holds to be
/// valid in linear real arithmetic, aligned with it position by position (0
/// for a literal the certificate does not use).
///
/// `None` when the private simplex does not refute the negation with a
/// certificate: a positive equality literal (its negation is a disequality,
/// not a bound), a coefficient beyond `i64`, or a clause that is not an LRA
/// tautology at all. The caller then keeps an uncertified hint.
pub(crate) fn farkas_for_clause(
    terms: &TermStore,
    clause: &[TheoryLit],
) -> Option<FarkasAnnotation> {
    let lits: Vec<(TermId, bool)> = clause
        .iter()
        .map(|l| strip_not(terms, l.term, l.value))
        .collect();
    let mut lra = LraSolver::new(terms);
    for &(atom, _) in &lits {
        lra.register_atom(atom);
    }
    for &(atom, value) in &lits {
        lra.assert_literal(atom, !value);
    }
    let result = TheorySolver::check(&mut lra);
    lra.unset_terms();
    let TheoryResult::UnsatWithFarkas(conflict) = result else {
        return None;
    };
    let farkas = conflict.farkas?;
    if farkas.coefficients.len() != conflict.literals.len() {
        return None;
    }
    let mut coefficients = vec![Rational64::zero(); clause.len()];
    for (lit, coefficient) in conflict.literals.iter().zip(&farkas.coefficients) {
        // A conflict literal is TRUE under the negation: the complement of
        // one clause literal.
        let (atom, value) = strip_not(terms, lit.term, lit.value);
        let pos = lits.iter().position(|&(a, v)| a == atom && v != value)?;
        let slot = coefficients.get_mut(pos)?;
        *slot = slot.checked_add(coefficient)?;
    }
    if coefficients.iter().all(Zero::is_zero) {
        return None;
    }
    Some(FarkasAnnotation::new(coefficients))
}

fn strip_not(terms: &TermStore, mut term: TermId, mut value: bool) -> (TermId, bool) {
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
        value = !value;
    }
    (term, value)
}
