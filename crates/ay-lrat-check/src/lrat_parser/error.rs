// Copyright 2026 Andrew Yates
// Typed parse errors for LRAT proof parsing.

use thiserror::Error;

/// Errors from parsing LRAT proof files (text or binary format).
#[derive(Debug, Error, PartialEq, Eq)]
#[non_exhaustive]
pub enum LratParseError {
    #[error("invalid LRAT step: {detail}")]
    InvalidStep { detail: String },

    #[error("invalid binary LRAT data at byte {position}: {detail}")]
    InvalidBinary { position: usize, detail: String },

    #[error(transparent)]
    Literal(#[from] ay_proof_common::literal::LiteralError),

    #[error("{0}")]
    Common(#[from] ay_proof_common::ParseError),
}
