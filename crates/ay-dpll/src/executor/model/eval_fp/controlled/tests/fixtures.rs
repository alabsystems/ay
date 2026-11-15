// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::Symbol;
use num_bigint::BigInt;

use super::*;

pub(super) fn fp(terms: &mut TermStore, exponent: u64, significand: u64) -> TermId {
    let sign = terms.mk_bitvec(BigInt::from(0), 1);
    let exponent = terms.mk_bitvec(BigInt::from(exponent), 5);
    let significand = terms.mk_bitvec(BigInt::from(significand), 10);
    terms.mk_app(
        Symbol::named("fp"),
        [sign, exponent, significand],
        Sort::FloatingPoint(5, 11),
    )
}

pub(super) fn division(mode: &str) -> (Executor, Model, TermId) {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let one = fp(terms, 15, 0);
    let three = fp(terms, 16, 512);
    let rm = terms.mk_app(
        Symbol::named(mode),
        [],
        Sort::Uninterpreted("RoundingMode".to_string()),
    );
    let term = terms.mk_app(
        Symbol::named("fp.div"),
        [rm, one, three],
        Sort::FloatingPoint(5, 11),
    );
    (executor, crate::executor::model::tests::empty_model(), term)
}

pub(super) fn pinned_fp(sort: Sort, value: FpModelValue) -> (Executor, Model, TermId) {
    let mut executor = Executor::new();
    let term = executor.ctx.terms.mk_var("pinned", sort);
    let mut values = HashMap::default();
    values.insert(term, value);
    let mut model = crate::executor::model::tests::empty_model();
    model.fp_model = Some(ay_fp::FpModel {
        values,
        rm_values: HashMap::default(),
    });
    (executor, model, term)
}

pub(super) fn bits(value: &FpModelValue) -> BigInt {
    assert_eq!((value.eb(), value.sb()), (5, 11));
    value.to_ieee_bv().0
}

pub(super) fn healthy(executor: &Executor, model: &Model, term: TermId, expected: u64) {
    let value = executor
        .evaluate_fp_term_via_bitblast_controlled(model, term, &|_| {})
        .unwrap()
        .unwrap();
    assert_eq!(bits(&value), BigInt::from(expected));
}
