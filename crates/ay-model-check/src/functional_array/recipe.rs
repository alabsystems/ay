// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact syntactic recognition of the range-copy lambda, without evaluating or
//! rewriting any leaf. Scalar bounds and both captured arrays remain model data.

use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

mod fill;
pub use fill::{recognize_fill_lambda, FillInterval, FillLambda};

#[derive(Clone, Copy, Debug)]
pub struct RangeLambda {
    pub bound: TermId,
    pub destination: TermId,
    pub source: TermId,
    pub lo: TermId,
    pub hi: TermId,
    pub source_lo: Option<TermId>,
}

/// The entire function `lambda i. select(array, i)`, after sound frontend
/// simplification removes an empty range. This describes data, not evidence.
#[derive(Clone, Copy, Debug)]
pub struct IdentityLambda {
    pub bound: TermId,
    pub array: TermId,
    pub read: TermId,
}

fn app<'a>(terms: &'a TermStore, term: TermId, name: &str, count: usize) -> Option<&'a [TermId]> {
    if (term.0 as usize) >= terms.len() {
        return None;
    }
    match terms.get(term) {
        TermData::App(symbol, args)
            if matches!(symbol, Symbol::Named(_))
                && symbol.name() == name
                && !terms.is_declared_function(name)
                && args.len() == count
                && args.iter().all(|child| (child.0 as usize) < terms.len()) =>
        {
            Some(args)
        }
        _ => None,
    }
}

pub fn recognize_identity_lambda(terms: &TermStore, term: TermId) -> Option<IdentityLambda> {
    if (term.0 as usize) >= terms.len() {
        return None;
    }
    let Sort::Array(sort) = terms.sort(term) else {
        return None;
    };
    if !matches!(&sort.index_sort, Sort::BitVec(index) if index.width == 64)
        || !matches!(&sort.element_sort, Sort::Bool | Sort::BitVec(_))
    {
        return None;
    }
    let lambda = app(terms, term, "lambda-array", 2)?;
    let (bound, read) = (lambda[0], lambda[1]);
    let args = app(terms, read, "select", 2)?;
    if !matches!(terms.get(bound), TermData::Var(..))
        || terms.sort(bound) != &sort.index_sort
        || args[1] != bound
        || terms.sort(read) != &sort.element_sort
        || terms.sort(args[0]) != terms.sort(term)
    {
        return None;
    }
    Some(IdentityLambda {
        bound,
        array: args[0],
        read,
    })
}

pub fn recognize_range_lambda(terms: &TermStore, term: TermId) -> Option<RangeLambda> {
    if (term.0 as usize) >= terms.len() {
        return None;
    }
    let Sort::Array(sort) = terms.sort(term) else {
        return None;
    };
    if !matches!(&sort.index_sort, Sort::BitVec(index) if index.width == 64)
        || !matches!(&sort.element_sort, Sort::Bool | Sort::BitVec(_))
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
    let (condition, positive, negative) = match terms.get(body) {
        TermData::Ite(c, t, e) => (*c, *t, *e),
        _ => {
            let args = app(terms, body, "ite", 3)?;
            (args[0], args[1], args[2])
        }
    };
    if [condition, positive, negative]
        .iter()
        .any(|child| (child.0 as usize) >= terms.len())
    {
        return None;
    }
    if terms.sort(condition) != &Sort::Bool
        || terms.sort(positive) != &sort.element_sort
        || terms.sort(negative) != &sort.element_sort
    {
        return None;
    }
    let guards = app(terms, condition, "and", 2)?;
    if guards.iter().any(|guard| terms.sort(*guard) != &Sort::Bool) {
        return None;
    }
    let (low, high) = if let (Some(low), Some(high)) = (
        app(terms, guards[0], "bvule", 2),
        app(terms, guards[1], "bvult", 2),
    ) {
        (low, high)
    } else {
        (
            app(terms, guards[1], "bvule", 2)?,
            app(terms, guards[0], "bvult", 2)?,
        )
    };
    if low[1] != bound || high[0] != bound || terms.sort(condition) != &Sort::Bool {
        return None;
    }
    let (lo, hi) = (low[0], high[1]);
    if terms.sort(lo) != &sort.index_sort || terms.sort(hi) != &sort.index_sort {
        return None;
    }
    let source_read = app(terms, positive, "select", 2)?;
    let destination_read = app(terms, negative, "select", 2)?;
    if destination_read[1] != bound
        || terms.sort(source_read[0]) != terms.sort(term)
        || terms.sort(destination_read[0]) != terms.sort(term)
        || terms.sort(positive) != &sort.element_sort
        || terms.sort(negative) != &sort.element_sort
    {
        return None;
    }
    let (shift, source_lo) = match app(terms, source_read[1], "bvadd", 2) {
        Some(args) => {
            if app(terms, args[0], "bvsub", 2).is_some() {
                (args[0], Some(args[1]))
            } else {
                (args[1], Some(args[0]))
            }
        }
        None => (source_read[1], None),
    };
    let subtraction = app(terms, shift, "bvsub", 2)?;
    if subtraction != [bound, lo]
        || terms.sort(shift) != &sort.index_sort
        || terms.sort(source_read[1]) != &sort.index_sort
        || source_lo.is_some_and(|offset| terms.sort(offset) != &sort.index_sort)
    {
        return None;
    }
    // Bounds/array captures must not depend on the local lambda binder. The
    // evaluator performs the bounded full dependency scan before capture.
    Some(RangeLambda {
        bound,
        destination: destination_read[0],
        source: source_read[0],
        lo,
        hi,
        source_lo,
    })
}
