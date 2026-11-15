// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closed-term helpers for QSAT UNSAT publication: authored closure,
//! clause shapes, sort defaults, and rational folding.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use super::super::Executor;
use crate::qsat;

/// The authored `and`-conjunct closure of `roots`, in order.
pub(super) fn and_closure(executor: &Executor, roots: &[TermId]) -> Vec<TermId> {
    let mut closure = Vec::new();
    let mut seen = HashSet::default();
    let mut stack: Vec<TermId> = roots.iter().rev().copied().collect();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match executor.ctx.terms.get(t) {
            TermData::App(sym, args) if sym.name() == "and" => {
                stack.extend(args.iter().rev().copied())
            }
            _ => closure.push(t),
        }
    }
    closure
}

/// The literals of a clause-shaped conjunct.
pub(super) fn clause_literals(executor: &mut Executor, conjunct: TermId) -> Option<Vec<TermId>> {
    match executor.ctx.terms.get(conjunct).clone() {
        TermData::App(sym, args) if sym.name() == "or" => Some(args),
        TermData::Not(inner) => match executor.ctx.terms.get(inner).clone() {
            TermData::App(sym, args) if sym.name() == "and" => Some(
                args.iter()
                    .map(|&a| executor.ctx.terms.mk_not_raw(a))
                    .collect(),
            ),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn default_term(executor: &mut Executor, sort: &Sort) -> TermId {
    match sort {
        Sort::Bool => executor.ctx.terms.mk_bool(false),
        Sort::Int => executor.ctx.terms.mk_int(0.into()),
        _ => executor
            .ctx
            .terms
            .mk_rational(num_rational::BigRational::from_integer(0.into())),
    }
}

/// A closed arithmetic term as the numeral it evaluates to: projections
/// compose replacement terms (`(+ 0.0 1.0)` once the free side is pinned), and
/// the ground probe refutes an instance over numerals where it would need
/// arithmetic rewriting over the composed term. Anything else is returned as is.
pub(super) fn fold_closed(terms: &mut TermStore, t: TermId) -> TermId {
    let sort = terms.sort(t).clone();
    if !matches!(sort, Sort::Int | Sort::Real) {
        return t;
    }
    let empty = qsat::lin::Model::default();
    let Some(value) = qsat::lin::Eval::new(terms, &empty).number(t) else {
        return t;
    };
    match sort {
        Sort::Int if value.is_integer() => terms.mk_int(value.to_integer()),
        Sort::Real => terms.mk_rational(value),
        _ => t,
    }
}
