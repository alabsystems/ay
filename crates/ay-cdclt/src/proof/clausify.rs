// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Alethe clause of a clausification tautology.
//!
//! The encoder records, for each input clause, the rule and the term it came
//! from. Alethe fixes each rule's literal order (`or_pos` lists the
//! disjuncts in the `or`'s own order, for example), while ay-sat may permute a
//! clause. So the step is rebuilt from the rule and its source term, and it is
//! used only when it is the traced clause up to order and repetition; anything
//! else is not authority for that clause.

use ay_core::{AletheRule, Constant, TermData, TermId, TermStore};

fn neg(terms: &mut TermStore, t: TermId) -> TermId {
    if let TermData::Not(inner) = terms.get(t) {
        return *inner;
    }
    terms.mk_not_raw(t)
}

/// The rule's clause for `source`, in the rule's literal order, when it is
/// `traced` up to order and repetition.
pub(super) fn canonical(
    terms: &mut TermStore,
    rule: &AletheRule,
    source: TermId,
    traced: &[TermId],
) -> Option<Vec<TermId>> {
    let (op, args): (&str, Vec<TermId>) = match terms.get(source) {
        TermData::App(sym, args) => (
            match sym.name() {
                "and" => "and",
                "or" => "or",
                "xor" => "xor",
                "=" => "=",
                _ => "",
            },
            args.clone(),
        ),
        TermData::Ite(c, t, e) => ("ite", vec![*c, *t, *e]),
        _ => ("", Vec::new()),
    };
    let not_source = neg(terms, source);
    let expected: Vec<TermId> = match (rule, op) {
        (AletheRule::AndPos(i), "and") => vec![not_source, *args.get(*i as usize)?],
        (AletheRule::AndNeg, "and") => {
            let mut v = vec![source];
            for a in args {
                v.push(neg(terms, a));
            }
            v
        }
        (AletheRule::OrPos(_), "or") => {
            let mut v = vec![not_source];
            v.extend(args);
            v
        }
        (AletheRule::OrNeg, "or") => {
            // The annotation does not name the disjunct; the traced clause does.
            let [a, b] = traced else {
                return None;
            };
            let other = if *a == source { *b } else { *a };
            let mut found = false;
            for arg in args {
                found |= neg(terms, arg) == other;
            }
            if !found {
                return None;
            }
            vec![source, other]
        }
        (AletheRule::True, _)
            if matches!(terms.get(source), TermData::Const(Constant::Bool(true))) =>
        {
            vec![source]
        }
        (AletheRule::False, _)
            if matches!(terms.get(source), TermData::Const(Constant::Bool(false))) =>
        {
            vec![not_source]
        }
        _ => three_literal(terms, rule, op, source, not_source, &args)?,
    };
    (set(&expected) == set(traced)).then_some(expected)
}

/// The three-literal templates of `xor`, `=` (equivalence) and `ite`.
fn three_literal(
    terms: &mut TermStore,
    rule: &AletheRule,
    op: &str,
    source: TermId,
    not_source: TermId,
    args: &[TermId],
) -> Option<Vec<TermId>> {
    Some(match (rule, op) {
        (AletheRule::XorPos1, "xor") => {
            let [a, b] = args[..] else { return None };
            vec![not_source, a, b]
        }
        (AletheRule::XorPos2, "xor") => {
            let [a, b] = args[..] else { return None };
            let (na, nb) = (neg(terms, a), neg(terms, b));
            vec![not_source, na, nb]
        }
        (AletheRule::XorNeg1, "xor") => {
            let [a, b] = args[..] else { return None };
            let nb = neg(terms, b);
            vec![source, a, nb]
        }
        (AletheRule::XorNeg2, "xor") => {
            let [a, b] = args[..] else { return None };
            let na = neg(terms, a);
            vec![source, na, b]
        }
        (AletheRule::EquivPos1, "=") => {
            let [a, b] = args[..] else { return None };
            let nb = neg(terms, b);
            vec![not_source, a, nb]
        }
        (AletheRule::EquivPos2, "=") => {
            let [a, b] = args[..] else { return None };
            let na = neg(terms, a);
            vec![not_source, na, b]
        }
        (AletheRule::EquivNeg2, "=") => {
            let [a, b] = args[..] else { return None };
            vec![source, a, b]
        }
        (AletheRule::EquivNeg1, "=") => {
            let [a, b] = args[..] else { return None };
            let (na, nb) = (neg(terms, a), neg(terms, b));
            vec![source, na, nb]
        }
        (AletheRule::ItePos1, "ite") => {
            let [c, _, e] = args[..] else { return None };
            vec![not_source, c, e]
        }
        (AletheRule::ItePos2, "ite") => {
            let [c, t, _] = args[..] else { return None };
            let nc = neg(terms, c);
            vec![not_source, nc, t]
        }
        (AletheRule::IteNeg1, "ite") => {
            let [c, _, e] = args[..] else { return None };
            let ne = neg(terms, e);
            vec![source, c, ne]
        }
        (AletheRule::IteNeg2, "ite") => {
            let [c, t, _] = args[..] else { return None };
            let (nc, nt) = (neg(terms, c), neg(terms, t));
            vec![source, nc, nt]
        }
        _ => return None,
    })
}

fn set(clause: &[TermId]) -> Vec<TermId> {
    let mut v = clause.to_vec();
    v.sort_unstable();
    v.dedup();
    v
}

#[cfg(test)]
mod tests;
