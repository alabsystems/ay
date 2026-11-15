//! Definitions of parsing errors.

use std::ops::Range;

use thiserror::Error;

use crate::pbp_parser::utils::Position;

/// An error from the VeriPB parsing library.
#[derive(Debug, Error)]
pub enum ParserError {
    /// Error related to reading the file.
    #[error("Failed to open file!")]
    IOError(
        #[from]
        #[source]
        std::io::Error,
    ),

    #[error("Failed to open file! File '{0}' might not exist?")]
    FileError(String),

    /// Reading a single line of an already-opened file failed.
    ///
    /// [`std::io::BufRead::lines`] yields an [`Err`] for any line that is not
    /// valid UTF-8 as well as for genuine I/O failures. Such an error must be
    /// propagated: treating it as end-of-input silently discards the rest of
    /// the file, which for a formula means checking a proof against a strict
    /// subset of the constraints.
    #[error("Failed to read {filename}:{}: {source}", .line + 1)]
    LineReadError {
        filename: String,
        line: usize,
        #[source]
        source: std::io::Error,
    },

    /// A clause was still open when the end of the file was reached.
    ///
    /// In DIMACS CNF and WCNF every clause is terminated by `0`; a file that
    /// ends mid-clause has been truncated, and dropping the partial clause
    /// would leave the checker with a weaker formula than the real one.
    #[error(
        "The last clause of '{filename}' is not terminated by '0' \
         ({num_lits} literal(s) were read after the last '0'); the file ends mid-clause!"
    )]
    UnterminatedClause { filename: String, num_lits: usize },

    /// The `p cnf <vars> <clauses>` header does not describe the file contents.
    #[error("Header of '{filename}' declares {declared} {kind}, but the file contains {actual}!")]
    HeaderCountMismatch {
        filename: String,
        kind: &'static str,
        declared: usize,
        actual: usize,
    },

    /// A DIMACS literal names a variable index that [`Lit`](veripb_formula::lit::Lit) cannot
    /// represent.
    ///
    /// `Lit` packs the variable index and the sign into a single `usize`; indices above
    /// `Lit::MAX_VAR_IDX` either collide with the reserved `Lit::new_undef()` sentinel or alias
    /// another variable outright, which silently rewrites the clause. Accepting one is a soundness
    /// bug rather than a formatting quirk, so this is rejected regardless of
    /// [`CnfParserOptions`](crate::cnf_parser::CnfParserOptions).
    #[error(
        "{filename}:{}: variable index {index} exceeds the largest representable index {max}!",
        .line + 1
    )]
    VariableIndexOutOfRange {
        filename: String,
        line: usize,
        index: usize,
        max: usize,
    },

    /// A DIMACS file names (or declares) a variable index that is representable but far larger
    /// than the dense per-variable tables this checker is willing to build.
    ///
    /// See [`MAX_DENSE_VAR_IDX`](veripb_formula::prelude::MAX_DENSE_VAR_IDX) for why the bound
    /// exists and how the number was chosen. Like
    /// [`VariableIndexOutOfRange`](ParserError::VariableIndexOutOfRange), this is rejected
    /// regardless of [`CnfParserOptions`](crate::cnf_parser::CnfParserOptions): the header check
    /// is a truncation heuristic and must not double as the guard for anything else.
    #[error(
        "{filename}:{}: variable index {index} exceeds {max}, the largest variable index this \
         checker builds a dense variable space for! The checker allocates roughly 90 bytes per \
         variable index up to the largest one used, whether or not the file constrains that \
         variable, so this file would need about {} GiB before the first proof line is checked.",
        .line + 1,
        .index / (11 * 1024 * 1024)
    )]
    VariableSpaceTooLarge {
        filename: String,
        line: usize,
        index: usize,
        max: usize,
    },

    #[error("Unexpected token starting at position {}! Expected: {expected}!", .span.start + 1)]
    TokenError {
        span: Range<usize>,
        expected: String,
    },

    #[error("Unexpected token starting at {filename}:{}:{}! Expected {expected}!", .line+1, .span.start + 1, )]
    TokenErrorFile {
        span: Range<usize>,
        expected: String,
        line: usize,
        filename: String,
    },

    #[error{"Constraint ID parsing error!"}]
    ParseIntError(
        #[from]
        #[source]
        std::num::ParseIntError,
    ),

    #[error("The file did not contain a header, which is required for this input file format!")]
    NoHeader,

    #[error("{message} at line {} col {}.\n{code}", .pos.line, .pos.col)]
    ProofFormatError {
        message: String,
        pos: Position,
        code: String,
    },
}

impl ParserError {
    pub fn is_version_error(&self) -> bool {
        matches!(
            self,
            ParserError::ProofFormatError {
                pos: Position {
                    pos: 0,
                    col: 1,
                    line: 0,
                },
                ..
            }
        )
    }

    pub fn token_error(span: Range<usize>, expected: &str) -> Self {
        Self::TokenError {
            span,
            expected: expected.to_string(),
        }
    }

    pub fn token_error_with_file(
        span: Range<usize>,
        expected: &str,
        filename: String,
        line: usize,
    ) -> Self {
        Self::TokenErrorFile {
            span,
            expected: expected.to_string(),
            line,
            filename,
        }
    }

    /// Attach `filename` and `line` to an error that does not carry them yet.
    ///
    /// **Total by construction.** A variant that already names its own
    /// position -- or that has no span to attach one to -- is returned
    /// unchanged. This used to return `Option<Self>`, `None` for exactly
    /// those variants, and all ten call sites `.unwrap()`ed it: a partial
    /// function unwrapped in the *error-reporting* path, so the day one of
    /// these parse helpers grew a second error variant, a syntax error in a
    /// user's formula would have aborted the process (the release profile is
    /// `panic = "abort"`) instead of being printed. Today every one of those
    /// helpers produces `TokenError` only, so this changes no observable
    /// behaviour; it removes the trap rather than a live crash.
    pub fn add_file_and_line(self, filename: String, line: usize) -> Self {
        match self {
            Self::TokenError { span, expected } => Self::TokenErrorFile {
                span,
                expected,
                line,
                filename,
            },
            already_positioned => already_positioned,
        }
    }

    pub fn pbp_error(message: String, pos: Position, len: usize, line: String) -> ParserError {
        if line.is_empty() {
            Self::ProofFormatError {
                message,
                pos,
                code: String::new(),
            }
        } else {
            Self::ProofFormatError {
                message,
                pos,
                code: format!(
                    "{}\n{}{}",
                    line,
                    " ".repeat(std::cmp::max(line.len(), 1) - len),
                    "^".repeat(std::cmp::max(len, 1)),
                ),
            }
        }
    }
}
