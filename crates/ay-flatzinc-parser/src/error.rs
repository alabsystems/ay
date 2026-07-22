// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// FlatZinc parser error types

use thiserror::Error;

#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum ParseError {
    #[error("unexpected token at line {line}, col {col}: expected {expected}, found {found}")]
    UnexpectedToken {
        line: usize,
        col: usize,
        expected: String,
        found: String,
    },
    #[error("unexpected end of input: expected {expected}")]
    UnexpectedEof { expected: String },
    #[error("invalid integer literal at line {line}: {value}")]
    InvalidInt { line: usize, value: String },
    #[error("invalid float literal at line {line}: {value}")]
    InvalidFloat { line: usize, value: String },
    #[error("missing solve item")]
    MissingSolveItem,
    #[error("duplicate solve item at line {line}")]
    DuplicateSolveItem { line: usize },
}
