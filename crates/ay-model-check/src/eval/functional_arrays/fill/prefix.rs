// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact unsigned prefixes after the frontend erases the tautology 0 <= i.
//! Recognition is DATA only; the existing whole grammar and capture checks
//! still authenticate both arms, the bound, and every original occurrence.

use super::*;

#[derive(Clone, Copy)]
pub(super) struct Interval {
    pub(super) lo: Option<TermId>,
    pub(super) hi: TermId,
    pub(super) destination: Option<TermId>,
    pub(super) frame: TermId,
    pub(super) inclusive: bool,
}

pub(super) struct Recipe {
    pub(super) bound: TermId,
    pub(super) value: TermId,
    pub(super) interval: Option<Interval>,
}

impl From<crate::FillLambda> for Recipe {
    fn from(value: crate::FillLambda) -> Self {
        Self {
            bound: value.bound,
            value: value.value,
            interval: value.interval.map(|range| Interval {
                lo: Some(range.lo),
                hi: range.hi,
                destination: range.destination,
                frame: range.frame,
                inclusive: false,
            }),
        }
    }
}

fn app<'a>(terms: &'a TermStore, term: TermId, name: &str, arity: usize) -> Option<&'a [TermId]> {
    if (term.0 as usize) >= terms.len() {
        return None;
    }
    match terms.get(term) {
        TermData::App(Symbol::Named(symbol), args)
            if symbol.as_str() == name
                && args.len() == arity
                && args.iter().all(|child| (child.0 as usize) < terms.len()) =>
        {
            Some(args)
        }
        _ => None,
    }
}

fn conditional(terms: &TermStore, term: TermId) -> Option<[TermId; 3]> {
    if (term.0 as usize) >= terms.len() {
        return None;
    }
    let parts = match terms.get(term) {
        TermData::Ite(c, t, e) => [*c, *t, *e],
        _ => {
            let args = app(terms, term, "ite", 3)?;
            [args[0], args[1], args[2]]
        }
    };
    parts
        .iter()
        .all(|child| (child.0 as usize) < terms.len())
        .then_some(parts)
}

pub(super) fn recognize(terms: &TermStore, term: TermId) -> Option<Recipe> {
    if (term.0 as usize) >= terms.len() {
        return None;
    }
    let Sort::Array(sort) = terms.sort(term) else {
        return None;
    };
    if !matches!(&sort.index_sort, Sort::BitVec(index) if index.width == 64)
        || !(sort.element_sort == Sort::Bool
            || matches!(&sort.element_sort, Sort::BitVec(cell)
                if cell.width > 0 && cell.width <= 128))
    {
        return None;
    }
    let lambda = app(terms, term, "lambda-array", 2)?;
    let bound = lambda[0];
    if !matches!(terms.get(bound), TermData::Var(..))
        || terms.sort(bound) != &sort.index_sort
        || terms.sort(lambda[1]) != &sort.element_sort
    {
        return None;
    }
    let [condition, value, frame] = conditional(terms, lambda[1])?;
    if terms.sort(condition) != &Sort::Bool
        || terms.sort(value) != &sort.element_sort
        || terms.sort(frame) != &sort.element_sort
    {
        return None;
    }
    let (hi, inclusive) = if let Some(args) = app(terms, condition, "bvult", 2) {
        if args[0] != bound {
            return None;
        }
        (args[1], false)
    } else if let Some(args) = app(terms, condition, "bvule", 2) {
        if args[0] != bound {
            return None;
        }
        (args[1], true)
    } else if let Some(args) = app(terms, condition, "bvugt", 2) {
        if args[1] != bound {
            return None;
        }
        (args[0], false)
    } else {
        let args = app(terms, condition, "bvuge", 2)?;
        if args[1] != bound {
            return None;
        }
        (args[0], true)
    };
    if terms.sort(hi) != &sort.index_sort {
        return None;
    }
    let destination = match app(terms, frame, "select", 2) {
        Some(read) if read[1] == bound && terms.sort(read[0]) == terms.sort(term) => Some(read[0]),
        _ => None,
    };
    Some(Recipe {
        bound,
        value,
        interval: Some(Interval {
            lo: None,
            hi,
            destination,
            frame,
            inclusive,
        }),
    })
}
