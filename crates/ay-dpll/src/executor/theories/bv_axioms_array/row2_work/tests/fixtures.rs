// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use std::collections::BTreeMap;

pub(super) struct Fixture {
    pub(super) executor: Executor,
    pub(super) roots: Vec<TermId>,
    pub(super) probes: Vec<(TermId, TermId)>,
    names: BTreeMap<&'static str, TermId>,
}

impl Fixture {
    pub(super) fn empty() -> Self {
        Self {
            executor: Executor::new(),
            roots: vec![],
            probes: vec![],
            names: BTreeMap::new(),
        }
    }

    pub(super) fn named(&self, name: &str) -> TermId {
        self.names[name]
    }
}

pub(super) fn raw_select(terms: &mut TermStore, array: TermId, index: TermId) -> TermId {
    let sort = terms.sort(array).array_element().unwrap().clone();
    terms.mk_app(Symbol::named("select"), [array, index], sort)
}

pub(super) fn ordered() -> Fixture {
    let mut fixture = Fixture::empty();
    let terms = &mut fixture.executor.ctx.terms;
    let sort = Sort::array(Sort::bitvec(2), Sort::bitvec(1));
    let a = terms.mk_var("a", sort.clone());
    let b = terms.mk_var("b", sort);
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let k = terms.mk_var("k", Sort::bitvec(2));
    let va = terms.mk_var("va", Sort::bitvec(1));
    let vb = terms.mk_var("vb", Sort::bitvec(1));
    let condition = terms.mk_var("condition", Sort::Bool);
    let sa = terms.mk_store(a, i, va);
    let sb = terms.mk_store(b, i, vb);
    let choice = terms.mk_ite_raw(condition, sa, sb);
    let choice_read = raw_select(terms, choice, j);
    let first_read = raw_select(terms, sa, j);
    let second_read = raw_select(terms, sb, k);
    let left = terms.mk_app(Symbol::named("="), [choice_read, first_read], Sort::Bool);
    let right = terms.mk_app(Symbol::named("="), [second_read, first_read], Sort::Bool);
    let assertion = terms.mk_app(Symbol::named("and"), [left, right, left], Sort::Bool);
    fixture
        .executor
        .ctx
        .assertions
        .extend([assertion, assertion]);
    fixture.roots.extend([second_read, second_read]);
    fixture
        .probes
        .extend([(sa, j), (sb, j), (a, j), (b, k), (b, j)]);
    fixture.names = BTreeMap::from([
        ("a", a),
        ("b", b),
        ("j", j),
        ("k", k),
        ("first-read", first_read),
        ("second-store", sb),
    ]);
    fixture
}

pub(super) fn folded() -> Fixture {
    let mut fixture = Fixture::empty();
    let terms = &mut fixture.executor.ctx.terms;
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let value = terms.mk_var("value", Sort::bitvec(1));
    let inner_value = terms.mk_var("inner-value", Sort::bitvec(1));
    let zero = terms.mk_bitvec(BigInt::from(0), 1);
    let one = terms.mk_bitvec(BigInt::from(1), 1);
    let a = terms.mk_const_array(Sort::bitvec(2), zero);
    let b = terms.mk_const_array(Sort::bitvec(2), one);
    let condition = terms.mk_var("condition", Sort::Bool);
    let choice = terms.mk_ite_raw(condition, a, b);
    let chosen = raw_select(terms, choice, j);
    let inner = terms.mk_store(a, j, inner_value);
    let outer = terms.mk_store(inner, i, value);
    let stored = raw_select(terms, outer, j);
    let mapped = terms.mk_array_map("bvnot", vec![a], terms.sort(a).clone());
    let map_store = terms.mk_store(mapped, i, value);
    let map_read = raw_select(terms, map_store, j);
    let duplicate_store = terms.mk_store(a, i, value);
    let duplicate_read = raw_select(terms, duplicate_store, j);
    let equalities: Vec<_> = [chosen, stored, map_read, duplicate_read]
        .into_iter()
        .map(|read| terms.mk_app(Symbol::named("="), [read, value], Sort::Bool))
        .collect();
    let assertion = terms.mk_app(Symbol::named("and"), equalities, Sort::Bool);
    fixture.executor.ctx.assertions.push(assertion);
    fixture.roots.extend([zero, zero]);
    fixture
        .probes
        .extend([(a, j), (b, j), (inner, j), (mapped, j)]);
    fixture.names = BTreeMap::from([
        ("j", j),
        ("zero", zero),
        ("one", one),
        ("inner-value", inner_value),
        ("zero-array", a),
        ("inner-store", inner),
        ("map", mapped),
    ]);
    fixture
}
