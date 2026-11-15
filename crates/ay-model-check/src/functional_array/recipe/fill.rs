// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Whole-domain scalar fill descriptors; source syntax DATA, not credentials.

use super::*;

/// Exact unsigned half-open fill and old frame. A scalar frame is the closed
/// form produced when a constant-array select beta-reduces during replay.
#[derive(Clone, Copy, Debug)]
pub struct FillInterval {
    pub lo: TermId,
    pub hi: TermId,
    pub destination: Option<TermId>,
    pub frame: TermId,
}

/// `lambda i. value`, or `lambda i. ite(lo <= i < hi, value, old[i])`.
/// Recognition does not establish binder independence or model availability;
/// the independent evaluator authenticates ALL captures before returning DATA.
#[derive(Clone, Copy, Debug)]
pub struct FillLambda {
    pub bound: TermId,
    pub value: TermId,
    pub interval: Option<FillInterval>,
}

pub fn recognize_fill_lambda(terms: &TermStore, term: TermId) -> Option<FillLambda> {
    if (term.0 as usize) >= terms.len()
        || recognize_range_lambda(terms, term).is_some()
        || recognize_identity_lambda(terms, term).is_some()
    {
        return None;
    }
    let Sort::Array(sort) = terms.sort(term) else {
        return None;
    };
    if !matches!(&sort.index_sort, Sort::BitVec(index) if index.width == 64)
        || !(sort.element_sort == Sort::Bool
            || matches!(&sort.element_sort, Sort::BitVec(cell) if cell.width > 0 && cell.width <= 128))
    {
        return None;
    }
    let lambda = app(terms, term, "lambda-array", 2)?;
    let (bound, body) = (lambda[0], lambda[1]);
    if !matches!(terms.get(bound), TermData::Var(..))
        || terms.sort(bound) != &sort.index_sort
        || terms.sort(body) != &sort.element_sort
    {
        return None;
    }
    if let Some((condition, value, frame)) = conditional(terms, body) {
        if let Some((lo, hi)) = endpoints(terms, condition, bound) {
            if terms.sort(condition) != &Sort::Bool
                || terms.sort(lo) != &sort.index_sort
                || terms.sort(hi) != &sort.index_sort
                || terms.sort(value) != &sort.element_sort
                || terms.sort(frame) != &sort.element_sort
            {
                return None;
            }
            let destination = match app(terms, frame, "select", 2) {
                Some(read) if read[1] == bound && terms.sort(read[0]) == terms.sort(term) => {
                    Some(read[0])
                }
                _ => None,
            };
            return Some(FillLambda {
                bound,
                value,
                interval: Some(FillInterval {
                    lo,
                    hi,
                    destination,
                    frame,
                }),
            });
        }
    }
    Some(FillLambda {
        bound,
        value: body,
        interval: None,
    })
}

fn conditional(terms: &TermStore, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let parts = match terms.get(term) {
        TermData::Ite(condition, positive, negative) => [*condition, *positive, *negative],
        _ => {
            let args = app(terms, term, "ite", 3)?;
            [args[0], args[1], args[2]]
        }
    };
    parts
        .iter()
        .all(|child| (child.0 as usize) < terms.len())
        .then_some((parts[0], parts[1], parts[2]))
}

fn endpoints(terms: &TermStore, condition: TermId, bound: TermId) -> Option<(TermId, TermId)> {
    let guards = app(terms, condition, "and", 2)?;
    if guards.iter().any(|guard| terms.sort(*guard) != &Sort::Bool) {
        return None;
    }
    for (low, high) in [(guards[0], guards[1]), (guards[1], guards[0])] {
        if let (Some(low), Some(high)) = (app(terms, low, "bvule", 2), app(terms, high, "bvult", 2))
        {
            if low[1] == bound && high[0] == bound {
                return Some((low[0], high[1]));
            }
        }
    }
    None
}
