// Copyright 2026 Andrew Yates
// Typed parse errors for ay-proof-common (DIMACS, LEB128).

use thiserror::Error;

/// Errors from parsing DIMACS CNF files or LEB128-encoded binary proof data.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParseError {
    #[error("invalid DIMACS header: {detail}")]
    InvalidHeader { detail: String },

    #[error("invalid literal: {detail}")]
    InvalidLiteral { detail: String },

    #[error(transparent)]
    Literal(#[from] crate::literal::LiteralError),

    #[error("unexpected end of input at byte {position}")]
    UnexpectedEof { position: usize },

    #[error("LEB128 value too large at byte {position}")]
    Leb128Overflow { position: usize },

    /// The input declares more clauses than the parser will number.
    ///
    /// Clause IDs are 1-indexed `u64`s; refusing here is what keeps their
    /// generation provably overflow-free. Refusal rather than clamping is
    /// deliberate: reusing an ID would silently corrupt LRAT hint resolution.
    #[error("clause count exceeds the maximum supported {maximum}; refusing to parse")]
    TooManyClauses { maximum: u64 },

    /// I/O error (stored as string to preserve PartialEq/Eq).
    #[error("I/O error: {detail}")]
    Io { detail: String },
}

impl From<std::io::Error> for ParseError {
    fn from(e: std::io::Error) -> Self {
        Self::Io {
            detail: e.to_string(),
        }
    }
}
