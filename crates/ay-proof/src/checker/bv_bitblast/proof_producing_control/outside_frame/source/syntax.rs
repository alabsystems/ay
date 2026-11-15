// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Match equivalent authored and frontend-normalized spellings. These helpers
//! identify candidates only; the complete source and offset theorem are checked.

use super::*;

pub(super) fn binary(terms: &TermStore, term: TermId, op: &str) -> Option<[TermId; 2]> {
    terms.entry_stamp(term)?;
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    let [a, b] = args.as_slice() else { return None };
    (name == op).then_some([*a, *b])
}

pub(super) fn ge(terms: &TermStore, term: TermId) -> Option<[TermId; 2]> {
    binary(terms, term, "bvuge").or_else(|| binary(terms, term, "bvule").map(|[a, b]| [b, a]))
}

fn lt(terms: &TermStore, term: TermId) -> Option<[TermId; 2]> {
    binary(terms, term, "bvult").or_else(|| binary(terms, term, "bvugt").map(|[a, b]| [b, a]))
}

pub(super) fn conditional(terms: &TermStore, property: TermId) -> Option<[TermId; 2]> {
    let [a, b] = binary(terms, property, "or")?;
    for [negative, equality] in [[a, b], [b, a]] {
        terms.entry_stamp(negative)?;
        if let TermData::Not(outside) = terms.get(negative) {
            if binary(terms, equality, "=").is_some() {
                return Some([*outside, equality]);
            }
        }
    }
    None
}

pub(super) fn outside(terms: &TermStore, outside: TermId, end: TermId) -> Option<[TermId; 2]> {
    let [a, b] = binary(terms, outside, "or")?;
    for [below, above] in [[a, b], [b, a]] {
        if let Some([observe, start]) = lt(terms, below) {
            if ge(terms, above) == Some([observe, end]) {
                return Some([observe, start]);
            }
        }
    }
    None
}

pub(super) fn property(
    terms: &TermStore,
    property: TermId,
    end: TermId,
) -> Option<(TermId, TermId, bool)> {
    if let Some([outside, equality]) = conditional(terms, property) {
        return Some((outside, equality, true));
    }
    let TermData::App(Symbol::Named(op), args) = terms.get(property) else {
        return None;
    };
    if op != "and" || args.len() > 128 {
        return None;
    }
    // Frontend De Morgan normalization turns a failed preservation property
    // into an AND containing outside and NOT(read_after = read_before). Its
    // value is false under the same positive root guard, even if flattened
    // alongside more conjuncts. No sibling is discarded before full lowering.
    for &outside_term in args {
        if outside(terms, outside_term, end).is_none() {
            continue;
        }
        for &negative in args {
            terms.entry_stamp(negative)?;
            if let TermData::Not(equality) = terms.get(negative) {
                if binary(terms, *equality, "=").is_some() {
                    return Some((outside_term, *equality, false));
                }
            }
        }
    }
    None
}
