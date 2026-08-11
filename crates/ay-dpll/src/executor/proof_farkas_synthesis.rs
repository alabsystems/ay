// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Small Farkas-certificate synthesis fallbacks used during proof repair.

use ay_core::term::TermData;
use ay_core::{Symbol, TermId, TermStore, TheoryLemmaKind};

use super::proof_farkas::try_lra_farkas_reconstruction;
use super::proof_farkas_validation::blocking_clause_to_conflict;
use super::proof_resolution::congruence::substitute_in_term;

/// Synthesize Farkas coefficients for integer equality contradiction clauses.
///
/// Handles clauses of the form `(not (= t c1)) (not (= t c2))` where `t`
/// is an integer-sorted term and `c1 != c2` are distinct integer constants.
pub(in crate::executor) fn synthesize_equality_farkas(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<ay_core::FarkasAnnotation> {
    use ay_core::{FarkasAnnotation, Sort};

    if clause.len() != 2 {
        return None;
    }

    let decode_negated_eq = |term: TermId| -> Option<(TermId, TermId)> {
        let inner = match terms.get(term) {
            TermData::Not(inner) => *inner,
            _ => return None,
        };
        match terms.get(inner) {
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                Some((args[0], args[1]))
            }
            _ => None,
        }
    };

    let (lhs1, rhs1) = decode_negated_eq(clause[0])?;
    let (lhs2, rhs2) = decode_negated_eq(clause[1])?;
    if !matches!(terms.sort(lhs1), Sort::Int) {
        return None;
    }

    let extract_int_const = |term: TermId| -> Option<i64> {
        match terms.get(term) {
            TermData::Const(ay_core::Constant::Int(n)) => n.try_into().ok(),
            _ => None,
        }
    };
    let constants_differ = |first: TermId, second: TermId| -> Option<bool> {
        Some(extract_int_const(first)? != extract_int_const(second)?)
    };

    if (lhs1 == lhs2 && constants_differ(rhs1, rhs2)?)
        || (rhs1 == rhs2 && constants_differ(lhs1, lhs2)?)
    {
        return Some(FarkasAnnotation::from_ints(&[1, 1]));
    }
    None
}

/// Synthesize a certificate for one equality plus arithmetic constraints.
///
/// The equality is substituted in both directions. A fresh LRA solve provides
/// the remaining row multipliers, then the equality multiplier is recovered
/// exactly from the unsubstituted residual and replayed against the original
/// clause before publication.
pub(in crate::executor) fn synthesize_mixed_equality_arithmetic_farkas(
    terms: &mut TermStore,
    clause: &[TermId],
) -> Option<ay_core::FarkasAnnotation> {
    use ay_core::FarkasAnnotation;

    let eq_positions: Vec<usize> = clause
        .iter()
        .enumerate()
        .filter_map(|(index, &literal)| {
            let TermData::Not(inner) = terms.get(literal) else {
                return None;
            };
            matches!(terms.get(*inner), TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2)
                .then_some(index)
        })
        .collect();
    if eq_positions.len() != 1 || clause.len() < 3 {
        return None;
    }
    let equality_index = eq_positions[0];
    let TermData::Not(equality) = terms.get(clause[equality_index]) else {
        return None;
    };
    let (lhs, rhs) = match terms.get(*equality) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            (args[0], args[1])
        }
        _ => return None,
    };

    for (from, to) in [(lhs, rhs), (rhs, lhs)] {
        let mut substituted = Vec::with_capacity(clause.len() - 1);
        let mut changed = false;
        for (index, &literal) in clause.iter().enumerate() {
            if index == equality_index {
                continue;
            }
            let rewritten = substitute_in_term(terms, literal, from, to);
            changed |= rewritten != literal;
            substituted.push(rewritten);
        }
        if !changed {
            continue;
        }

        let mut substituted_farkas = None;
        let mut substituted_kind = TheoryLemmaKind::LiaGeneric;
        if !try_lra_farkas_reconstruction(
            terms,
            &substituted,
            &mut substituted_farkas,
            &mut substituted_kind,
        ) {
            continue;
        }
        let substituted_coefficients = substituted_farkas?.coefficients;
        if substituted_coefficients.len() != substituted.len() {
            continue;
        }

        let mut coefficients = Vec::with_capacity(clause.len());
        let mut next_substituted = 0;
        for index in 0..clause.len() {
            if index == equality_index {
                coefficients.push(num_rational::Rational64::from(0));
            } else {
                coefficients.push(substituted_coefficients[next_substituted]);
                next_substituted += 1;
            }
        }
        let partial = FarkasAnnotation::new(coefficients);
        let conflict = blocking_clause_to_conflict(terms, clause);
        if let Some(recovered) = ay_core::proof_validation::recover_single_equality_farkas(
            terms,
            &conflict,
            &partial,
            equality_index,
        ) {
            return Some(recovered);
        }
    }
    None
}
