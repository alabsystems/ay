// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Error types for CHC solving

use thiserror::Error;

/// CHC solver errors
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ChcError {
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),

    #[error("parse error: {0}")]
    Parse(String),

    #[error("undefined predicate: {0}")]
    UndefinedPredicate(String),

    #[error("arity mismatch for predicate {name}: expected {expected}, got {actual}")]
    ArityMismatch {
        name: String,
        expected: usize,
        actual: usize,
    },

    #[error("sort mismatch: expected {expected:?}, got {actual:?}")]
    SortMismatch { expected: String, actual: String },

    #[error("no query clause found")]
    NoQuery,

    #[error("timeout after {0} iterations")]
    Timeout(usize),

    #[error("internal error: {0}")]
    Internal(String),

    #[error("verification error: {0}")]
    Verification(String),

    #[error("unsupported CHC floating-point input: native ay-chc accepts Bool/Int/Real/BV/Array only; lower FP/RoundingMode terms to BV before HORN solving (found token: {0})")]
    UnsupportedFloatingPoint(String),
}

/// Result type for CHC operations.
///
/// Consumers can use this to handle structured errors from CHC solving
/// (parse failures, sort mismatches, internal panics caught by `try_solve()`).
pub type ChcResult<T> = Result<T, ChcError>;
