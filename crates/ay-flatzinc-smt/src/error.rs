// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// FlatZinc-to-SMT translation error types

use thiserror::Error;

#[derive(Debug, Error)]
pub enum TranslateError {
    #[error("unknown identifier: {0}")]
    UnknownIdentifier(String),

    #[error("unsupported constraint: {0}")]
    UnsupportedConstraint(String),

    #[error("wrong argument count for `{name}`: expected {expected}, got {got}")]
    WrongArgCount {
        name: String,
        expected: usize,
        got: usize,
    },

    #[error("expected integer literal, got: {0}")]
    ExpectedIntLiteral(String),

    #[error("expected array expression, got scalar")]
    ExpectedArray,

    #[error("array index out of bounds: {name}[{index}]")]
    ArrayIndexOutOfBounds { name: String, index: i64 },

    #[error("unsupported type for SMT translation: {0}")]
    UnsupportedType(String),
}
