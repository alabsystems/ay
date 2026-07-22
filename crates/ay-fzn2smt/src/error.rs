// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Typed errors for the `ay-fzn2smt` library.
//!
//! Per `rust_excellence.md`: libraries use `thiserror` and a concrete `Error`
//! enum so callers can pattern-match on failure modes without stringly-typed
//! comparisons.
//!
//! The variants below cover every failure mode surfaced by the public
//! library API (`solve::cmd_solve`, `solve_cp::cmd_solve_cp`,
//! `solve_cp::unsupported_constraints`) and the internal FlatZinc → CP
//! translation pipeline. Ad-hoc contextual messages previously produced
//! via `anyhow::bail!` / `anyhow::anyhow!` map to [`Fzn2smtError::Message`]
//! so the migration is behaviour-preserving at the error-text level while
//! giving downstream callers a concrete type to match on.
//!
//! History: ported from `anyhow::Result` per issue #8849.
//!
//! [`Fzn2smtError::Message`] remains as a compatibility escape hatch for
//! future contextual translator failures, but current library callsites use
//! structured variants.

/// Errors produced by the `ay-fzn2smt` library.
///
/// This enum is `#[non_exhaustive]` — new variants may be added in the
/// future. Match with a `_ =>` arm or match on specific variants you care
/// about (for example [`Fzn2smtError::UnknownVariable`] to distinguish
/// user-input errors from infrastructure failures).
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Fzn2smtError {
    /// The ay-flatzinc-smt solver returned an error while driving the
    /// external ay subprocess.
    #[error("solver error: {0}")]
    Solver(String),

    /// An identifier referenced a variable or parameter that has not been
    /// declared in the current context.
    #[error("unknown variable or parameter: {name}")]
    UnknownVariable { name: String },

    /// An identifier expected to resolve to an array did not match any
    /// known array variable or parameter.
    #[error("cannot resolve identifier as array: {name}")]
    UnknownArray { name: String },

    /// A constant-integer array parameter lookup failed.
    #[error("unknown int array parameter: {name}")]
    UnknownIntArray { name: String },

    /// A set-variable lookup failed while translating a set constraint.
    #[error("{constraint}: unknown set variable: {name}")]
    UnknownSetVariable {
        /// The FlatZinc constraint name (e.g. `"set_card"`).
        constraint: String,
        /// The set variable identifier that could not be resolved.
        name: String,
    },

    /// A set constraint expected an identifier naming a set variable.
    #[error("{constraint}: expected set variable identifier")]
    ExpectedSetVariableIdentifier {
        /// The FlatZinc constraint name (e.g. `"set_card"`).
        constraint: String,
    },

    /// A constant set-array parameter lookup failed.
    #[error("{constraint}: unknown parameter set array: {name}")]
    UnknownSetArray {
        /// The FlatZinc constraint name (e.g. `"array_set_element"`).
        constraint: String,
        /// The set-array parameter identifier that could not be resolved.
        name: String,
    },

    /// A set-array constraint received an expression shape it cannot handle.
    #[error("{constraint}: expected identifier or array literal")]
    ExpectedSetArray {
        /// The FlatZinc constraint name (e.g. `"array_set_element"`).
        constraint: String,
    },

    /// An inverse constraint received two arrays with different lengths.
    #[error(
        "inverse constraint requires arrays of equal length: left has {left}, right has {right}"
    )]
    InverseArrayLengthMismatch {
        /// Number of entries in the first inverse array.
        left: usize,
        /// Number of entries in the second inverse array.
        right: usize,
    },

    /// A global_cardinality constraint received cover/count arrays with
    /// different lengths.
    #[error(
        "global_cardinality requires cover/count arrays of equal length: cover has {cover}, counts has {counts}"
    )]
    GlobalCardinalityLengthMismatch {
        /// Number of covered values.
        cover: usize,
        /// Number of count variables.
        counts: usize,
    },

    /// A table_int constraint received a flat tuple array whose length is
    /// not divisible by the variable arity.
    #[error(
        "table_int requires flat tuple value count to be divisible by arity: values has {values}, arity is {arity}"
    )]
    TableTupleLengthMismatch {
        /// Number of entries in the flat tuple array.
        values: usize,
        /// Number of variables in each tuple.
        arity: usize,
    },

    /// A cumulative constraint received start/duration/resource arrays with
    /// different lengths.
    #[error(
        "cumulative requires start/duration/resource arrays of equal length: starts has {starts}, durations has {durations}, resources has {resources}"
    )]
    CumulativeArrayLengthMismatch {
        /// Number of task start variables.
        starts: usize,
        /// Number of task duration variables or constants.
        durations: usize,
        /// Number of task resource variables or constants.
        resources: usize,
    },

    /// A diffn constraint received rectangle coordinate/size arrays with
    /// different lengths.
    #[error(
        "diffn requires x/y/dx/dy arrays of equal length: x has {x}, y has {y}, dx has {dx}, dy has {dy}"
    )]
    DiffnArrayLengthMismatch {
        /// Number of x-coordinate variables.
        x: usize,
        /// Number of y-coordinate variables.
        y: usize,
        /// Number of width variables or constants.
        dx: usize,
        /// Number of height variables or constants.
        dy: usize,
    },

    /// An array element constraint received an empty array argument.
    #[error("{constraint}: empty array")]
    ArrayElementEmptyArray {
        /// The FlatZinc constraint name.
        constraint: String,
    },

    /// The direct CP portfolio received an unusable worker count.
    #[error("parallel worker count must be in 1..={maximum}, got {requested}")]
    InvalidWorkerCount {
        /// Requested number of workers.
        requested: usize,
        /// Maximum number of distinct worker configurations available.
        maximum: usize,
    },

    /// A translation step received an expression shape it cannot handle
    /// (e.g. a literal where an identifier was required).
    #[error("{0}")]
    UnsupportedExpression(String),

    /// Generic contextual message used for failures that do not fit one
    /// of the structured variants above. These correspond to the former
    /// `anyhow::bail!` / `anyhow::anyhow!` call sites.
    #[error("{0}")]
    Message(String),

    /// I/O failure while writing DZN output or diagnostic messages.
    #[error(transparent)]
    Io(#[from] std::io::Error),
}

impl Fzn2smtError {
    /// Construct a [`Fzn2smtError::Message`] from anything printable.
    ///
    /// Shorthand for `Fzn2smtError::Message(format!(...))`. Prefer a
    /// structured variant when one fits.
    #[must_use]
    pub fn msg(message: impl Into<String>) -> Self {
        Self::Message(message.into())
    }
}

/// Library-wide `Result` alias.
pub type Result<T, E = Fzn2smtError> = std::result::Result<T, E>;
