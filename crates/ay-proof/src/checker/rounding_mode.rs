// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict validation for the fixed-domain axioms of SMT-LIB's built-in
//! `RoundingMode` sort.
//!
//! AY represents `RoundingMode` as an uninterpreted core sort, then injects the
//! two facts supplied by the SMT-LIB FloatingPoint theory: its five named
//! values are pairwise distinct, and every value is one of those five. These
//! are theory axioms, not problem assumptions. This validator recognizes only
//! exact instances over the canonical short names, plus the complete
//! six-or-more-value pigeonhole consequence, and therefore lets proof
//! reconstruction certify them without granting authority to arbitrary
//! solver-generated formulas.

use ay_core::{ProofId, Sort, Symbol, TermData, TermId, TermStore};

use super::ProofCheckError;

const MODE_NAMES: [&str; 5] = ["RNE", "RNA", "RTP", "RTN", "RTZ"];
const ALL_MODE_MASK: u8 = (1 << MODE_NAMES.len()) - 1;
const ALL_PAIR_MASK: u32 = (1 << 10) - 1;

/// Recognize a fixed-domain `RoundingMode` axiom accepted by the strict
/// checker. Proof reconstruction uses this exact entry point, keeping its
/// promotion decision aligned with strict re-validation.
#[must_use]
pub fn recognize_rounding_mode_domain(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_rounding_mode_domain(terms, ProofId(0), clause).is_ok()
}

/// Validate one exact `RoundingMode` domain theorem.
pub(crate) fn validate_rounding_mode_domain(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let invalid = |reason: &str| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: format!("invalid RoundingMode domain axiom: {reason}"),
    };

    if clause.is_empty()
        || clause
            .iter()
            .any(|&literal| terms.sort(literal) != &Sort::Bool)
    {
        return Err(invalid("clause must contain only Boolean literals"));
    }

    if recognize_coverage(terms, clause)
        || recognize_pairwise_unit(terms, clause)
        || recognize_distinct_conjunction(terms, clause)
        || recognize_distinct_demorgan(terms, clause)
        || clause
            .iter()
            .any(|&literal| recognize_domain_pigeonhole(terms, literal))
    {
        return Ok(());
    }

    Err(invalid(
        "expected exact five-mode coverage, exact pairwise distinctness, or a complete \
         six-or-more-value domain pigeonhole",
    ))
}

fn is_rounding_mode_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Uninterpreted(name) if name == "RoundingMode")
}

fn mode_index(terms: &TermStore, term: TermId) -> Option<usize> {
    if !is_rounding_mode_sort(terms.sort(term)) {
        return None;
    }
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if !args.is_empty() {
        return None;
    }
    MODE_NAMES.iter().position(|candidate| name == candidate)
}

fn equality_sides(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

fn negated_equality_sides(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let TermData::Not(equality) = terms.get(term) else {
        return None;
    };
    equality_sides(terms, *equality)
}

fn disjunction_literals<'a>(terms: &'a TermStore, clause: &'a [TermId]) -> &'a [TermId] {
    if let [only] = clause {
        if let TermData::App(Symbol::Named(name), args) = terms.get(*only) {
            if name == "or" {
                return args;
            }
        }
    }
    clause
}

fn recognize_coverage(terms: &TermStore, clause: &[TermId]) -> bool {
    let literals = disjunction_literals(terms, clause);
    if literals.len() != MODE_NAMES.len() {
        return false;
    }

    let mut subject = None;
    let mut modes = 0u8;
    for &literal in literals {
        let Some((lhs, rhs)) = equality_sides(terms, literal) else {
            return false;
        };
        let (candidate, mode) = match (mode_index(terms, lhs), mode_index(terms, rhs)) {
            (None, Some(mode)) => (lhs, mode),
            (Some(mode), None) => (rhs, mode),
            _ => return false,
        };
        if !is_rounding_mode_sort(terms.sort(candidate)) {
            return false;
        }
        match subject {
            Some(existing) if existing != candidate => return false,
            None => subject = Some(candidate),
            _ => {}
        }
        let bit = 1u8 << mode;
        if modes & bit != 0 {
            return false;
        }
        modes |= bit;
    }
    subject.is_some() && modes == ALL_MODE_MASK
}

fn pair_bit(lhs: usize, rhs: usize) -> Option<u32> {
    if lhs == rhs {
        return None;
    }
    let (lhs, rhs) = if lhs < rhs { (lhs, rhs) } else { (rhs, lhs) };
    let mut index = 0u32;
    for first in 0..MODE_NAMES.len() {
        for second in (first + 1)..MODE_NAMES.len() {
            if first == lhs && second == rhs {
                return Some(1u32 << index);
            }
            index += 1;
        }
    }
    None
}

fn disequality_pair_bit(terms: &TermStore, term: TermId) -> Option<u32> {
    let (lhs, rhs) = negated_equality_sides(terms, term)?;
    pair_bit(mode_index(terms, lhs)?, mode_index(terms, rhs)?)
}

fn equality_pair_bit(terms: &TermStore, term: TermId) -> Option<u32> {
    let (lhs, rhs) = equality_sides(terms, term)?;
    pair_bit(mode_index(terms, lhs)?, mode_index(terms, rhs)?)
}

fn exact_pair_mask(
    terms: &TermStore,
    terms_to_check: &[TermId],
    pair: fn(&TermStore, TermId) -> Option<u32>,
) -> bool {
    if terms_to_check.len() != 10 {
        return false;
    }
    let mut mask = 0u32;
    for &term in terms_to_check {
        let Some(bit) = pair(terms, term) else {
            return false;
        };
        if mask & bit != 0 {
            return false;
        }
        mask |= bit;
    }
    mask == ALL_PAIR_MASK
}

fn recognize_pairwise_unit(terms: &TermStore, clause: &[TermId]) -> bool {
    matches!(clause, [only] if disequality_pair_bit(terms, *only).is_some())
}

fn recognize_distinct_conjunction(terms: &TermStore, clause: &[TermId]) -> bool {
    let [only] = clause else {
        return false;
    };
    let TermData::App(Symbol::Named(name), conjuncts) = terms.get(*only) else {
        return false;
    };
    name == "and" && exact_pair_mask(terms, conjuncts, disequality_pair_bit)
}

fn recognize_distinct_demorgan(terms: &TermStore, clause: &[TermId]) -> bool {
    let [only] = clause else {
        return false;
    };
    let TermData::Not(disjunction) = terms.get(*only) else {
        return false;
    };
    let TermData::App(Symbol::Named(name), equalities) = terms.get(*disjunction) else {
        return false;
    };
    name == "or" && exact_pair_mask(terms, equalities, equality_pair_bit)
}

/// Recognize `not(distinct t_0 ... t_n)` for more than five values of the
/// five-element `RoundingMode` sort. `TermStore::mk_distinct` expands the
/// distinct term to the conjunction of every pairwise disequality, so validate
/// that complete graph exactly rather than trusting the producer's spelling.
fn recognize_domain_pigeonhole(terms: &TermStore, literal: TermId) -> bool {
    let TermData::Not(distinct) = terms.get(literal) else {
        return false;
    };
    let TermData::App(Symbol::Named(name), conjuncts) = terms.get(*distinct) else {
        return false;
    };
    if name != "and" {
        return false;
    }

    let mut values = Vec::new();
    let mut pairs = Vec::with_capacity(conjuncts.len());
    for &conjunct in conjuncts {
        let Some((lhs, rhs)) = negated_equality_sides(terms, conjunct) else {
            return false;
        };
        if lhs == rhs
            || !is_rounding_mode_sort(terms.sort(lhs))
            || !is_rounding_mode_sort(terms.sort(rhs))
        {
            return false;
        }
        if !values.contains(&lhs) {
            values.push(lhs);
        }
        if !values.contains(&rhs) {
            values.push(rhs);
        }
        let pair = if lhs.0 < rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        if pairs.contains(&pair) {
            return false;
        }
        pairs.push(pair);
    }

    if values.len() <= MODE_NAMES.len() || conjuncts.len() != values.len() * (values.len() - 1) / 2
    {
        return false;
    }
    values.iter().enumerate().all(|(index, &lhs)| {
        values[index + 1..].iter().all(|&rhs| {
            let pair = if lhs.0 < rhs.0 {
                (lhs, rhs)
            } else {
                (rhs, lhs)
            };
            pairs.contains(&pair)
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (TermStore, Vec<TermId>) {
        let mut terms = TermStore::new();
        let sort = Sort::Uninterpreted("RoundingMode".to_string());
        let modes = MODE_NAMES
            .iter()
            .map(|name| terms.mk_app(Symbol::named(*name), Vec::new(), sort.clone()))
            .collect();
        (terms, modes)
    }

    #[test]
    fn accepts_exact_coverage_and_distinctness_forms() {
        let (mut terms, modes) = fixture();
        let subject = terms.mk_var("rm", Sort::Uninterpreted("RoundingMode".to_string()));
        let equalities = modes
            .iter()
            .map(|&mode| terms.mk_eq(subject, mode))
            .collect();
        let coverage = terms.mk_or(equalities);
        assert!(recognize_rounding_mode_domain(&terms, &[coverage]));

        let distinct = terms.mk_distinct(modes.clone());
        assert!(recognize_rounding_mode_domain(&terms, &[distinct]));

        let TermData::App(_, pairwise) = terms.get(distinct).clone() else {
            panic!("five-mode distinctness must expand to a conjunction");
        };
        assert!(recognize_rounding_mode_domain(&terms, &[pairwise[0]]));

        let equal_pairs = pairwise
            .iter()
            .map(|&disequality| match terms.get(disequality) {
                TermData::Not(equality) => *equality,
                _ => panic!("pairwise term must be a disequality"),
            })
            .collect();
        let pair_disjunction = terms.mk_or(equal_pairs);
        let demorgan = terms.mk_not_raw(pair_disjunction);
        assert!(recognize_rounding_mode_domain(&terms, &[demorgan]));
    }

    #[test]
    fn rejects_incomplete_or_forged_domains() {
        let (mut terms, modes) = fixture();
        let subject = terms.mk_var("rm", Sort::Uninterpreted("RoundingMode".to_string()));
        let incomplete_equalities = modes[..4]
            .iter()
            .map(|&mode| terms.mk_eq(subject, mode))
            .collect();
        let incomplete = terms.mk_or(incomplete_equalities);
        assert!(!recognize_rounding_mode_domain(&terms, &[incomplete]));

        let other_sort = Sort::Uninterpreted("OpenSort".to_string());
        let fake = terms.mk_app(Symbol::named("RNE"), Vec::new(), other_sort.clone());
        let other = terms.mk_var("other", other_sort);
        let fake_equality = terms.mk_eq(other, fake);
        assert!(!recognize_rounding_mode_domain(&terms, &[fake_equality]));

        let missing_pair = terms.mk_distinct(modes);
        let TermData::App(_, mut pairs) = terms.get(missing_pair).clone() else {
            panic!("five-mode distinctness must expand to a conjunction");
        };
        pairs.pop();
        let incomplete_distinct = terms.mk_and(pairs);
        assert!(!recognize_rounding_mode_domain(
            &terms,
            &[incomplete_distinct]
        ));
    }

    #[test]
    fn accepts_only_complete_domain_pigeonholes() {
        let mut terms = TermStore::new();
        let sort = Sort::Uninterpreted("RoundingMode".to_string());
        let values: Vec<_> = (0..6)
            .map(|index| terms.mk_var(format!("rm_{index}"), sort.clone()))
            .collect();
        let six_distinct = terms.mk_distinct(values.clone());
        let not_six_distinct = terms.mk_not_raw(six_distinct);
        assert!(recognize_rounding_mode_domain(&terms, &[not_six_distinct]));

        let five_distinct = terms.mk_distinct(values[..5].to_vec());
        let not_five_distinct = terms.mk_not_raw(five_distinct);
        assert!(!recognize_rounding_mode_domain(
            &terms,
            &[not_five_distinct]
        ));

        let TermData::App(_, mut incomplete_pairs) = terms.get(six_distinct).clone() else {
            panic!("six-value distinctness must expand to a conjunction");
        };
        incomplete_pairs.pop();
        let incomplete = terms.mk_and(incomplete_pairs);
        let not_incomplete = terms.mk_not_raw(incomplete);
        assert!(!recognize_rounding_mode_domain(&terms, &[not_incomplete]));
    }
}
