// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MPS and CPLEX LP parsers.
//!
//! Both parsers normalize their output to [`crate::model::Problem`]. The
//! parsers are deliberately tolerant of whitespace (MPS free form) but
//! reject structurally invalid files.

pub(crate) mod lp;
pub(crate) mod lp_tok;
pub(crate) mod mps;

pub use lp::parse_lp;
pub use mps::parse_mps;

/// Add two parser-produced finite values without letting an aggregate overflow
/// smuggle an infinity into the normalized problem.
pub(crate) fn checked_finite_add(
    left: f64,
    right: f64,
    line: usize,
    field: &str,
) -> Result<f64, crate::error::LpError> {
    let sum = left + right;
    if sum.is_finite() {
        Ok(sum)
    } else {
        Err(crate::error::LpError::Parse {
            line,
            msg: format!("{field} exceeds the finite numeric range"),
        })
    }
}
