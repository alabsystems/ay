// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
pub(super) enum Route {
    Disjoint,
    Outside,
    Combined,
}

#[derive(Clone, Copy)]
pub(super) enum Value {
    Valid,
    OverwrittenMalformed,
}

pub(super) struct Fixture {
    pub(super) terms: TermStore,
    pub(super) clause: TermId,
}

fn app(terms: &mut TermStore, op: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(op), args, sort)
}

pub(super) fn fixture(route: Route, value: Value) -> Fixture {
    match route {
        Route::Disjoint => disjoint(value),
        Route::Outside | Route::Combined => outside(route, value),
    }
}

fn disjoint(value: Value) -> Fixture {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(9);
    let byte = Sort::bitvec(8);
    let array = Sort::array(word.clone(), byte.clone());
    let a = terms.mk_var("a", word.clone());
    let b = terms.mk_var("b", word.clone());
    let size = terms.mk_bitvec(2.into(), 9);
    let end_a = app(&mut terms, "bvadd", &[a, size], word.clone());
    let end_b = app(&mut terms, "bvadd", &[b, size], word);
    let after_b = app(&mut terms, "bvuge", &[a, end_b], Sort::Bool);
    let after_a = app(&mut terms, "bvuge", &[b, end_a], Sort::Bool);
    let separate = app(&mut terms, "or", &[after_b, after_a], Sort::Bool);
    let bound = terms.mk_bitvec(509.into(), 9);
    let nowrap_a = app(&mut terms, "bvule", &[a, bound], Sort::Bool);
    let nowrap_b = app(&mut terms, "bvule", &[b, bound], Sort::Bool);
    let base = terms.mk_var("memory", array.clone());
    let good = terms.mk_var("value", byte.clone());
    let first = match value {
        Value::Valid => good,
        Value::OverwrittenMalformed => app(&mut terms, "bvadd", &[good], byte.clone()),
    };
    let stored = app(&mut terms, "store", &[base, a, first], array.clone());
    let stored = app(&mut terms, "store", &[stored, a, good], array);
    let after = app(&mut terms, "select", &[stored, b], byte.clone());
    let before = app(&mut terms, "select", &[base, b], byte);
    let property = app(&mut terms, "=", &[after, before], Sort::Bool);
    let negative = terms.mk_not_raw(property);
    let root = app(
        &mut terms,
        "and",
        &[separate, nowrap_a, nowrap_b, negative],
        Sort::Bool,
    );
    let clause = terms.mk_not_raw(root);
    Fixture { terms, clause }
}

fn outside(route: Route, value: Value) -> Fixture {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(9);
    let byte = Sort::bitvec(8);
    let array = Sort::array(word.clone(), byte.clone());
    let stack = terms.mk_var("stack", word.clone());
    let observe = terms.mk_var("observe", word.clone());
    let size = terms.mk_bitvec(2.into(), 9);
    let start = app(&mut terms, "bvsub", &[stack, size], word.clone());
    let guard = app(&mut terms, "bvuge", &[stack, size], Sort::Bool);
    let below = app(&mut terms, "bvult", &[observe, start], Sort::Bool);
    let above = app(&mut terms, "bvuge", &[observe, stack], Sort::Bool);
    let outside = app(&mut terms, "or", &[below, above], Sort::Bool);
    let not_outside = terms.mk_not_raw(outside);
    let mut before = terms.mk_var("memory", array.clone());
    let good = terms.mk_var("value", byte.clone());
    let first = match value {
        Value::Valid => good,
        Value::OverwrittenMalformed => app(&mut terms, "bvadd", &[good], byte.clone()),
    };
    let mut after = app(&mut terms, "store", &[before, start, first], array.clone());
    after = app(&mut terms, "store", &[after, start, good], array.clone());
    let mut guards = vec![guard];
    if let Route::Combined = route {
        let output = terms.mk_var("output", word.clone());
        after = app(&mut terms, "store", &[after, output, good], array.clone());
        before = app(&mut terms, "store", &[before, output, good], array);
        let extent = terms.mk_bitvec(40.into(), 9);
        let end = app(&mut terms, "bvadd", &[output, extent], word);
        let below = app(&mut terms, "bvule", &[end, start], Sort::Bool);
        let above = app(&mut terms, "bvuge", &[output, stack], Sort::Bool);
        let separate = app(&mut terms, "or", &[below, above], Sort::Bool);
        let bound = terms.mk_bitvec(471.into(), 9);
        let nowrap = app(&mut terms, "bvule", &[output, bound], Sort::Bool);
        guards = vec![separate, nowrap, guard];
    }
    let after = app(&mut terms, "select", &[after, observe], byte.clone());
    let before = app(&mut terms, "select", &[before, observe], byte);
    let equal = app(&mut terms, "=", &[after, before], Sort::Bool);
    let property = app(&mut terms, "or", &[not_outside, equal], Sort::Bool);
    guards.push(terms.mk_not_raw(property));
    let root = app(&mut terms, "and", &guards, Sort::Bool);
    let clause = terms.mk_not_raw(root);
    Fixture { terms, clause }
}
