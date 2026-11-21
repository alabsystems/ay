// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reconstruct unary congruence carried by an arithmetic certificate.
//!
//! An LIA conflict can use substitution through a unary UF and record
//! `(cl (= (f a) (f b)) (not (= b a)))` as `LiaGeneric` with positional
//! Farkas evidence. That evidence remains attached to its original clause;
//! this independent EUF derivation consumes none of it.

use super::eq_congruent::{printed_eq_congruent_holds, PrintedCongruence};
use super::*;

/// Whether the exporter can independently prove this exact, typed unary
/// congruence clause, including its effective printed surface and order.
#[must_use]
pub fn checked_unary_congruence_lowering_supported(
    terms: &TermStore,
    kind: &ay_core::TheoryLemmaKind,
    clause: &[TermId],
    overrides: Option<&HashMap<TermId, String>>,
) -> bool {
    let printer =
        AlethePrinter::new_with_overrides_and_budget(terms, overrides, Some(4 * 1024 * 1024));
    printer
        .format_checked_unary_congruence(ProofId(0), kind, clause)
        .is_some()
}

fn equality(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), operands) = terms.get(term) else {
        return None;
    };
    let [left, right] = operands.as_slice() else {
        return None;
    };
    (name == "="
        && terms.sort(term) == &ay_core::Sort::Bool
        && terms.sort(*left) == terms.sort(*right))
    .then_some((*left, *right))
}

fn typed_unary_order(terms: &TermStore, clause: &[TermId]) -> Option<[TermId; 2]> {
    let [first, second] = clause else {
        return None;
    };
    for ordered in [[*first, *second], [*second, *first]] {
        let [premise, conclusion] = ordered;
        let TermData::Not(guard) = terms.get(premise) else {
            continue;
        };
        if terms.sort(premise) != &ay_core::Sort::Bool {
            continue;
        }
        let Some((a, b)) = equality(terms, *guard) else {
            continue;
        };
        let Some((left, right)) = equality(terms, conclusion) else {
            continue;
        };
        let (TermData::App(f, left_args), TermData::App(g, right_args)) =
            (terms.get(left), terms.get(right))
        else {
            continue;
        };
        let ([x], [y]) = (left_args.as_slice(), right_args.as_slice()) else {
            continue;
        };
        if f == g
            && terms.sort(*x) == terms.sort(*y)
            && ((a == *x && b == *y) || (a == *y && b == *x))
            && crate::recognize_euf_congruent(terms, &ordered)
        {
            return Some(ordered);
        }
    }
    None
}

impl AlethePrinter<'_> {
    pub(super) fn format_checked_unary_congruence(
        &self,
        id: ProofId,
        kind: &ay_core::TheoryLemmaKind,
        clause: &[TermId],
    ) -> Option<String> {
        // This is a bounded complement to the observed arithmetic bridge,
        // not authority for Generic or for every arithmetic certificate.
        if !matches!(kind, ay_core::TheoryLemmaKind::LiaGeneric) {
            return None;
        }
        let ordered = typed_unary_order(self.terms, clause)?;
        let printed: Vec<String> = ordered
            .iter()
            .map(|&literal| {
                let mut text = String::new();
                self.write_derived_literal_into(&mut text, literal);
                text
            })
            .collect();
        if self.emission_progress.refused() || self.work_budget_exhausted() {
            return None;
        }
        // The native relation and the independently rewritten printed
        // relation must both be exact instances of the standard rule.
        if printed_eq_congruent_holds(&[&printed[0], &printed[1]]) != Ok(PrintedCongruence::Exact) {
            return None;
        }
        let canonical = format!("(cl {} {})", printed[0], printed[1]);
        if ordered.as_slice() == clause {
            return Some(format!("(step {id} {canonical} :rule eq_congruent)"));
        }
        Some(format!(
            "(step {id}.unary {canonical} :rule eq_congruent)\n\
             (step {id} (cl {} {}) :rule reordering :premises ({id}.unary))",
            printed[1], printed[0]
        ))
    }
}

#[cfg(test)]
mod tests;
