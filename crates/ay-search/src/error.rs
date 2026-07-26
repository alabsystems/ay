// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use thiserror::Error;

/// Errors raised while constructing, parsing, or executing a search model.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum SearchError {
    #[error("invalid domain for `{name}`: {reason}")]
    InvalidDomain { name: String, reason: String },

    #[error(
        "domain `{name}` has dense encoded span {span}, exceeding the fixed safety limit {limit}"
    )]
    DomainTooLarge {
        name: String,
        span: u128,
        limit: u64,
    },

    #[error("model exceeds the fixed {resource} safety limit of {limit}")]
    ModelTooLarge { resource: &'static str, limit: u64 },

    #[error("invalid variable name `{0}`; use [A-Za-z_][A-Za-z0-9_]*")]
    InvalidVariableName(String),

    #[error("a variable named `{0}` already exists")]
    DuplicateVariable(String),

    #[error("unknown variable `{0}`")]
    UnknownVariable(String),

    #[error("variable handle belongs to another model")]
    ForeignVariable,

    #[error("linear expression exceeds the exact i64 range supported by AY CP-SAT")]
    ExpressionOverflow,

    #[error("linear expression is too wide for overflow-free CP-SAT lowering")]
    ExpressionTooWide,

    #[error(
        "{resource} has magnitude {magnitude}, exceeding AY CP-SAT's fixed safe numeric limit {limit}"
    )]
    NumericEnvelopeExceeded {
        resource: String,
        magnitude: u128,
        limit: u64,
    },

    #[error("model's estimated backend lowering work exceeds the fixed safety limit {limit}")]
    BackendWorkLimit { limit: u64 },

    #[error("all_different requires at least one variable")]
    EmptyAllDifferent,

    #[error("table requires at least one variable")]
    EmptyTableVariables,

    #[error("table requires at least one allowed tuple")]
    EmptyTableTuples,

    #[error("table has {cells} cells, exceeding the fixed safety limit {limit}")]
    TableTooLarge { cells: u128, limit: u64 },

    #[error("table tuple {tuple} has arity {actual}, expected {expected}")]
    TableArity {
        tuple: usize,
        actual: usize,
        expected: usize,
    },

    #[error("table tuple {tuple} gives `{variable}` the out-of-domain value {value}")]
    TableValueOutsideDomain {
        tuple: usize,
        variable: String,
        value: i64,
    },

    #[error("element requires a non-empty array")]
    EmptyElementArray,

    #[error(
        "element index `{variable}` has domain [{min}, {max}], outside the required range [0, {largest_index}]"
    )]
    InvalidElementIndexDomain {
        variable: String,
        min: i64,
        max: i64,
        largest_index: usize,
    },

    #[error("choice label value {value} is outside the domain of `{variable}`")]
    LabelOutsideDomain { variable: String, value: i64 },

    #[error("expression parse error at byte {position}: {message}")]
    ExpressionParse { position: usize, message: String },

    #[error("expression exceeds the fixed {resource} limit of {limit}")]
    ExpressionLimit {
        resource: &'static str,
        limit: usize,
    },

    #[error("constraint expression needs exactly one of ==, !=, <=, or >=")]
    MissingRelation,

    #[error("nonlinear multiplication is not supported; one operand of `*` must be constant")]
    NonlinearExpression,

    #[error("SearchSpec version {0} is unsupported; expected version 1")]
    UnsupportedVersion(u32),

    #[error("limit `{name}` is out of range: {value}")]
    InvalidLimit { name: &'static str, value: u64 },

    #[error(
        "SearchSpec enumeration could retain {cells} assignment cells, exceeding the fixed limit {limit}"
    )]
    EnumerationResultTooLarge { cells: u128, limit: u64 },

    #[error(
        "SearchSpec enumeration could serialize up to {estimated_bytes} bytes, exceeding the fixed limit {limit}"
    )]
    EnumerationOutputTooLarge { estimated_bytes: u128, limit: u64 },

    #[error(
        "SearchSpec SMT-LIB rendering would require {estimated_bytes} bytes, exceeding the fixed limit {limit}"
    )]
    SmtOutputTooLarge { estimated_bytes: u128, limit: u64 },

    #[error("`objective` and `limits.max_solutions` select conflicting execution modes")]
    ConflictingExecutionModes,

    #[error("invalid JSON search specification: {0}")]
    Json(#[from] serde_json::Error),

    #[error("solver returned an incomplete assignment")]
    IncompleteAssignment,

    #[error("solver returned an assignment that failed independent model validation")]
    InvalidSolverAssignment,
}
