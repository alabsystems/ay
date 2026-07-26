// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Error types for the `ay-lp` crate.

use thiserror::Error;

/// Errors produced by MPS/LP parsing and the solver driver.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum LpError {
    /// Parse error with 1-based line number and a human message.
    #[error("parse error at line {line}: {msg}")]
    Parse {
        /// 1-based line number where the error occurred.
        line: usize,
        /// Human-readable message.
        msg: String,
    },

    /// Numeric field could not be parsed as a real number.
    #[error("invalid number '{raw}' at line {line}")]
    InvalidNumber {
        /// 1-based line number.
        line: usize,
        /// Raw text that failed to parse.
        raw: String,
    },

    /// Reference to a row/column that was never declared.
    #[error("unknown identifier '{name}' at line {line}")]
    UnknownIdent {
        /// 1-based line number.
        line: usize,
        /// Identifier that was not previously declared.
        name: String,
    },

    /// The instance is structurally invalid (e.g., duplicate row).
    #[error("invalid instance: {0}")]
    InvalidInstance(String),

    /// Problem uses features not yet supported by the Phase 1 solver.
    #[error("unsupported: {0}")]
    Unsupported(String),

    /// The (sub-)problem is infeasible.
    #[error("infeasible")]
    Infeasible,

    /// The problem is unbounded (objective goes to -inf for min / +inf for max).
    #[error("unbounded")]
    Unbounded,

    /// Solver hit the iteration limit before reaching a conclusion.
    #[error("iteration limit reached")]
    IterationLimit,

    /// Solver produced an internally inconsistent answer.
    #[error("numerical failure: {0}")]
    NumericalFailure(String),

    /// I/O error while reading the instance.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}
