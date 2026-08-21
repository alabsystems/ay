// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parser for the Model Counting Competition DIMACS-like input format
//! (format spec v1.2, 2026).
//!
//! Supports all five problem types: `mc`, `wmc`, `pmc`, `pwmc`, and
//! `amc-complex`. Weights are parsed to exact rationals (decimal, scientific
//! notation, or `a/b` fraction; complex `a+bi`). When present, the `c t` type
//! line is authoritative; otherwise the type is inferred from `c p show` and
//! `c p weight` records.
//! Projected tracks without a show record use the empty projection (a SAT
//! decision), while projection records are rejected for `amc-complex`.
//!
//! Parsing is intentionally tolerant only where established competition files
//! require it: a final clause may omit `0` (with a warning), and a weight line
//! may omit its final `0`. Identifiers, record boundaries, contradictory
//! declarations, allocation-amplifying dimensions, and expanded-weight memory
//! are validated before the counting engine observes them.

use std::fmt;
use std::str::FromStr;

use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// Bound compact decimal-exponent expansion. Longer mantissas remain
/// input-proportional, but a handful of exponent digits must not request a
/// multi-gigabyte `BigInt` allocation.
const MAX_DECIMAL_EXPONENT_ABS: u64 = 1_000_000;

/// Model-counting engines keep multiple dense arrays per variable. This
/// consumer-specific ceiling is intentionally lower than the syntax-only
/// DIMACS bound so an accepted header remains practically allocatable.
const MAX_COUNT_VARS: usize = 1 << 20;

/// A compact weight token may retain at most this many expanded integer bits
/// per input byte (at most 128 bytes of raw limbs per source byte).
const WEIGHT_EXPANSION_BITS_PER_INPUT_BYTE: u64 = 1_024;

/// Bound all retained raw weights to roughly 128 MiB of integer limbs. The
/// limit scales with the engine's maximum variable count but is independent of
/// how many duplicate declarations an input contains.
const MAX_TOTAL_WEIGHT_BITS: u64 = (MAX_COUNT_VARS as u64) * WEIGHT_EXPANSION_BITS_PER_INPUT_BYTE;

/// Problem type of a counting instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProblemType {
    /// Exact unweighted model counting.
    Mc,
    /// Weighted model counting.
    Wmc,
    /// Projected model counting.
    Pmc,
    /// Projected weighted model counting.
    Pwmc,
    /// Algebraic model counting over complex numbers.
    AmcComplex,
}

impl ProblemType {
    /// Competition string for the `c s type` output line.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Mc => "mc",
            Self::Wmc => "wmc",
            Self::Pmc => "pmc",
            Self::Pwmc => "pwmc",
            Self::AmcComplex => "amc-complex",
        }
    }

    fn from_token(token: &str) -> Option<Self> {
        if token.eq_ignore_ascii_case("mc") {
            Some(Self::Mc)
        } else if token.eq_ignore_ascii_case("wmc") {
            Some(Self::Wmc)
        } else if token.eq_ignore_ascii_case("pmc") {
            Some(Self::Pmc)
        } else if token.eq_ignore_ascii_case("pwmc") {
            Some(Self::Pwmc)
        } else if token.eq_ignore_ascii_case("amc-complex")
            || token.eq_ignore_ascii_case("amc_complex")
            || token.eq_ignore_ascii_case("amc")
        {
            Some(Self::AmcComplex)
        } else {
            None
        }
    }
}

/// A parsed literal weight: real rational or complex rational.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RawWeight {
    /// Real rational weight.
    Rat(BigRational),
    /// Complex rational weight `(real, imaginary)`.
    Complex(BigRational, BigRational),
}

/// A parsed counting instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instance {
    /// Number of variables from the `p cnf` header.
    pub num_vars: usize,
    /// Clauses as signed DIMACS literals (validated in range, no zeros).
    pub clauses: Vec<Vec<i32>>,
    /// Effective problem type (type line authoritative, else inferred).
    pub ptype: ProblemType,
    /// Projection variables from `c p show`, represented as 1-based indices.
    /// Parsed values are sorted and deduplicated. `None` denotes an
    /// unprojected track. Projected tracks use `Some(Vec::new())` when the
    /// show record is absent or explicitly empty.
    pub show: Option<Vec<u32>>,
    /// Raw weight lines in file order as `(literal, weight)` pairs.
    pub weights: Vec<(i32, RawWeight)>,
    /// Format and compatibility warnings accumulated while parsing.
    pub warnings: Vec<String>,
}

/// Parse or format error with a competition-appropriate message.
///
/// The tuple field remains public for source compatibility. New code should
/// normally use [`std::error::Error`] or [`fmt::Display`] rather than inspecting
/// message text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError(pub String);

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for ParseError {}

fn err<T>(msg: impl Into<String>) -> Result<T, ParseError> {
    Err(ParseError(msg.into()))
}

include!("parse/number.rs");
include!("parse/instance.rs");
include!("parse/weights.rs");

#[cfg(test)]
mod tests {
    use super::*;

    include!("parse/tests.rs");
}
