// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) struct Fixture {
    pub(super) terms: TermStore,
    pub(super) array: TermId,
    pub(super) out: TermId,
    pub(super) guard: TermId,
    pub(super) base: TermId,
    pub(super) key: TermId,
    pub(super) high: TermId,
    pub(super) next: TermId,
    pub(super) store: TermId,
    pub(super) read: TermId,
}

impl Fixture {
    pub(super) fn new() -> Self {
        let mut terms = TermStore::new();
        let sort = Sort::array(Sort::bitvec(8), Sort::bitvec(129));
        let array = terms.mk_var("a", sort.clone());
        let out = terms.mk_var("x", Sort::bitvec(129));
        let guard = terms.mk_var("g", Sort::Bool);
        let high_value: BigInt = BigInt::from(1u8) << 128usize;
        let high = terms.mk_bitvec(high_value.clone(), 129);
        let next = terms.mk_bitvec(high_value + 1, 129);
        let zero = terms.mk_bitvec(BigInt::from(0u8), 129);
        let base = terms.mk_app(Symbol::named("const-array"), [zero], sort.clone());
        let key = terms.mk_bitvec(BigInt::from(7u8), 8);
        let payload = terms.mk_ite_raw(guard, high, next);
        let store = terms.mk_app(Symbol::named("store"), [base, key, payload], sort);
        let read = terms.mk_app(Symbol::named("select"), [array, key], Sort::bitvec(129));
        Self {
            terms,
            array,
            out,
            guard,
            base,
            key,
            high,
            next,
            store,
            read,
        }
    }

    pub(super) fn array_sort(&self) -> Sort {
        self.terms.sort(self.array).clone()
    }
    pub(super) fn store(&mut self, base: TermId, key: TermId, value: TermId) -> TermId {
        self.terms.mk_app(
            Symbol::named("store"),
            [base, key, value],
            self.array_sort(),
        )
    }
    pub(super) fn read(&mut self, array: TermId, key: TermId) -> TermId {
        self.terms
            .mk_app(Symbol::named("select"), [array, key], Sort::bitvec(129))
    }
}

pub(super) fn model() -> BvModel {
    BvModel {
        values: HashMap::default(),
        bool_overrides: HashMap::default(),
        term_to_bits: HashMap::default(),
    }
}

pub(super) fn lookup<'a>(interp: &'a ArrayInterpretation, key: &str) -> &'a str {
    interp
        .stores
        .iter()
        .find(|(index, _)| index == key)
        .map(|(_, value)| value.as_str())
        .or(interp.default.as_deref())
        .expect("complete candidate array")
}
