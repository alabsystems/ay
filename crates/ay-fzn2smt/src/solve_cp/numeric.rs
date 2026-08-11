// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked numeric helpers shared by direct-CP translators.

use crate::error::{Fzn2smtError, Result};

/// Maximum number of owned element references or rectangle pairs created by
/// a quadratic global encoding.
const MAX_QUADRATIC_GLOBAL_WORK: u128 = 1 << 20;

pub(super) fn linear_encoding_overflow(context: &str) -> Fzn2smtError {
    Fzn2smtError::LinearEncodingOverflow {
        constraint: context.to_string(),
    }
}

pub(super) fn encoding_i64(value: i128, context: &str) -> Result<i64> {
    i64::try_from(value).map_err(|_| linear_encoding_overflow(context))
}

pub(super) fn positive_big_m(value: i128, context: &str) -> Result<i64> {
    encoding_i64(value.max(1), context)
}

/// Whether every value in an inclusive interval can be enumerated within the
/// supplied limit. The i128 subtraction represents the full i64 range.
pub(super) fn interval_size_within(lo: i64, hi: i64, limit: i128) -> bool {
    hi >= lo && i128::from(hi) - i128::from(lo) < limit
}

/// Whether an inclusive two-dimensional Cartesian product fits a limit,
/// without multiplying two potentially full-width i64 cardinalities.
pub(super) fn product_size_within(left: (i64, i64), right: (i64, i64), limit: i128) -> bool {
    let left_size = i128::from(left.1) - i128::from(left.0) + 1;
    let right_size = i128::from(right.1) - i128::from(right.0) + 1;
    left_size > 0
        && right_size > 0
        && left_size <= limit
        && right_size <= limit
        && left_size * right_size <= limit
}

/// Whether a quadratic global encoding is within its checked translation
/// budget. Kept here so circuit, inverse, and Diffn remain peer translators.
pub(super) fn quadratic_global_work_supported(len: usize) -> bool {
    let len = len as u128;
    len.saturating_mul(len) <= MAX_QUADRATIC_GLOBAL_WORK
}
