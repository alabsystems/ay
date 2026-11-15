// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::construction::control::{uninterrupted, BuildControl};
use crate::construction::{FpBuildError, FpBuildProgress, FpBuildStage, FpConstruction};
use crate::{FpDecomposed, FpPrecision, FpSolver, RoundingMode};
use ay_core::{Sort, Symbol, TermId, TermStore};
use std::cell::Cell;
use std::time::{Duration, Instant};

mod oracle;
mod ownership;
mod parity;

fn frame() -> (Instant, Option<ay_core::resource::CheckStop>) {
    (
        Instant::now() + Duration::from_secs(20),
        ay_core::resource::current_check_stop().unwrap(),
    )
}

fn stopped(end: Instant, enclosing: &Option<ay_core::resource::CheckStop>) -> bool {
    Instant::now() >= end
        || ay_core::resource::process_cancelled()
        || enclosing.as_ref().is_some_and(|stop| stop())
}

fn fixture(
    signed: bool,
    precision: FpPrecision,
    width: u32,
    mode: Option<RoundingMode>,
) -> (TermStore, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let rm_sort = Sort::Uninterpreted("RoundingMode".into());
    let rm = match mode {
        Some(mode) => terms.mk_app(Symbol::named(mode.name()), [], rm_sort),
        None => terms.mk_var("original_rm", rm_sort),
    };
    let word = terms.mk_var("original_word", Sort::bitvec(width));
    let name = if signed { "to_fp" } else { "to_fp_unsigned" };
    let result = terms.mk_app(
        Symbol::indexed(
            name,
            vec![precision.exponent_bits(), precision.significand_bits()],
        ),
        [rm, word],
        Sort::FloatingPoint(precision.exponent_bits(), precision.significand_bits()),
    );
    (terms, rm, word, result)
}

fn assert_fp(actual: &FpDecomposed, expected: &FpDecomposed) {
    assert_eq!(actual.sign, expected.sign);
    assert_eq!(actual.exponent, expected.exponent);
    assert_eq!(actual.significand, expected.significand);
    assert_eq!(actual.precision, expected.precision);
}
