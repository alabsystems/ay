// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::RM_ORDER;
use crate::{FpBuildError, FpBuildProgress, FpBuiltEncoding, FpConstruction, FpEncodingCache};
use ay_core::term::TermStore;
use ay_core::{Sort, Symbol};
use std::cell::{Cell, RefCell};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::time::{Duration, Instant};

mod ownership;
mod parity;
mod reference;
mod semantics;
mod support;

fn root(terms: &mut TermStore, eb: u32, sb: u32, mode: RoundingMode) -> (TermId, [TermId; 3]) {
    let sort = Sort::FloatingPoint(eb, sb);
    let inputs = ["original-fma-x", "original-fma-y", "original-fma-z"]
        .map(|name| terms.mk_var(name, sort.clone()));
    let rm = terms.mk_app(
        Symbol::named(mode.name()),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let term = terms.mk_app(
        Symbol::named("fp.fma"),
        [rm, inputs[0], inputs[1], inputs[2]],
        sort,
    );
    (term, inputs)
}

fn zero_root(terms: &mut TermStore, recursive: bool) -> TermId {
    let sort = Sort::FloatingPoint(5, 11);
    let zero = terms.mk_app(Symbol::named("+zero"), [], sort.clone());
    let y = terms.mk_var("original-zero-fma-y", sort.clone());
    let z = terms.mk_var("original-zero-fma-z", sort.clone());
    let rm = terms.mk_app(
        Symbol::named("RNE"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let other = if recursive {
        let u = terms.mk_var("original-zero-fma-u", sort.clone());
        terms.mk_app(Symbol::named("fp.div"), [rm, y, u], sort.clone())
    } else {
        y
    };
    terms.mk_app(Symbol::named("fp.fma"), [rm, zero, other, z], sort)
}

fn assert_monotone(history: &[FpBuildProgress]) {
    assert_eq!(history.first().unwrap().stage, FpBuildStage::Setup);
    for pair in history.windows(2) {
        assert!(pair[0].variables <= pair[1].variables);
        assert!(pair[0].clauses <= pair[1].clauses);
    }
}

fn assert_fp(actual: &FpDecomposed, expected: &FpDecomposed) {
    assert_eq!(actual.sign, expected.sign);
    assert_eq!(actual.exponent, expected.exponent);
    assert_eq!(actual.significand, expected.significand);
    assert_eq!(actual.precision, expected.precision);
}

fn assert_cache(actual: &FpEncodingCache, expected: &FpEncodingCache) {
    assert_eq!(actual.term_to_fp.len(), expected.term_to_fp.len());
    for (term, fp) in &actual.term_to_fp {
        assert_fp(fp, &expected.term_to_fp[term]);
    }
    assert_eq!(actual.bv_term_bits, expected.bv_term_bits);
    assert_eq!(actual.next_var, expected.next_var);
    assert_eq!(actual.cached_false, expected.cached_false);
    assert_eq!(actual.cached_true, expected.cached_true);
    assert_eq!(actual.bool_input_lits, expected.bool_input_lits);
    assert_eq!(actual.ieee_nan_encodings, expected.ieee_nan_encodings);
    assert_eq!(actual.rm_terms, expected.rm_terms);
    // This pure FMA fixture admits no conversion site or missing cache field.
    assert!(actual.to_bv_unspec_sites.is_empty());
    assert!(expected.to_bv_unspec_sites.is_empty());
}
