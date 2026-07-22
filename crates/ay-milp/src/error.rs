// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Error types for ay-milp.

/// A model that cannot be solved as given.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ModelError {
    /// A NaN bound/coefficient or an infinite objective coefficient.
    #[error("invalid number in model (col {col:?}, row {row:?})")]
    InvalidNumber {
        /// Offending column index, if column-local.
        col: Option<usize>,
        /// Offending row index, if row-local.
        row: Option<usize>,
    },
    /// The model uses a feature the selected lane does not support.
    #[error("unsupported model for this session: {reason}")]
    Unsupported {
        /// What was unsupported.
        reason: String,
    },
}

/// Errors from session construction and solving.
///
/// Note the deliberate absence of any "wrong answer" channel: verdicts are
/// [`crate::Outcome`] values, and anything the engine cannot warrant is
/// `Outcome::Unknown` — never an error and never a fabricated verdict.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum MilpError {
    /// The model was rejected.
    #[error(transparent)]
    Model(#[from] ModelError),
    /// The underlying solver reported a hard error (not a verdict).
    #[error("solver error: {message}")]
    Solver {
        /// Stable description of the failure.
        message: String,
    },
    /// A session operation was used outside its contract (e.g. `pop` at
    /// scope depth 0).
    #[error("session misuse: {message}")]
    Session {
        /// What was misused.
        message: String,
    },
}
