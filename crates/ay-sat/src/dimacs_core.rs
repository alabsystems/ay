// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared DIMACS-family parser core.
//!
//! Handles header parsing, comment/blank-line skipping, `%` termination,
//! clause tokenization with multiline accumulation, and tagged-line records
//! (`x` for XOR, `e`/`a` for QBF quantifiers). Crate-specific semantics
//! (variable indexing, quantifier interpretation) live in thin adapters.

use std::io::{BufRead, BufReader, Read};

/// Parsed DIMACS `p cnf` header.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DimacsHeader {
    /// Number of variables declared.
    pub num_vars: usize,
    /// Number of clauses declared.
    pub num_clauses: usize,
}

/// Error from the core DIMACS parser.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DimacsCoreError {
    /// No `p cnf` header found before clause data.
    MissingHeader,
    /// Invalid `p cnf` header format.
    InvalidHeader {
        /// The invalid header line content.
        line_content: String,
        /// 1-based line number where the error occurred.
        line_number: usize,
    },
    /// More than one problem line appeared in a single input.
    DuplicateHeader {
        /// 1-based line number of the repeated problem line.
        line_number: usize,
    },
    /// Non-numeric token in a clause line.
    InvalidLiteral {
        /// The invalid token.
        token: String,
        /// 1-based line number where the error occurred.
        line_number: usize,
    },
    /// I/O error (stringified).
    IoError(String),
    /// Literal variable exceeds declared `num_vars`.
    VariableOutOfRange {
        /// The out-of-range variable.
        var: u32,
        /// Maximum allowed variable from header.
        max: u32,
        /// 1-based line number where the error occurred.
        line_number: usize,
    },
    /// A consumer found an implausibly large actual variable count, which
    /// would drive an unbounded per-variable allocation (OOM). The shared
    /// parser preserves over-declared headers as metadata; allocating
    /// consumers reject actual content above their dense-state limit.
    HeaderCountTooLarge {
        /// Which count (currently always `"variable"`).
        what: &'static str,
        /// The declared value from the header.
        declared: usize,
        /// The maximum accepted value ([`MAX_DIMACS_VARS`]).
        max: usize,
    },
    /// A tagged line (e.g. a QDIMACS quantifier prefix `a`/`e`) appeared in
    /// input consumed as plain CNF, which does not support tagged lines.
    UnsupportedTaggedLine {
        /// The tag character that introduced the line (e.g. 'a', 'e').
        tag: char,
    },
}

/// Backstop on the number of distinct DIMACS variables a solver/checker will
/// allocate dense per-variable state for.
///
/// The declared `p cnf` header count is NOT used for allocation — consumers size
/// their state by the variables that actually appear (content-driven). This
/// constant only bounds that *actual* count: because DIMACS uses dense `1..=N`
/// numbering, the per-variable arrays are inherently O(max variable index), so a
/// pathological input that explicitly references an astronomically large index
/// (e.g. a single clause `4000000000 0`) is still refused here rather than
/// allocating hundreds of GB. The 64-million-variable ceiling retains the
/// repository's documented 58.6M-variable SAT Competition giant while ruling
/// out the previous 268M-variable multi-array allocation envelope. Runtime
/// memory limits remain the tighter authority for ordinary runs.
pub const MAX_DIMACS_VARS: usize = 1 << 26;

impl std::fmt::Display for DimacsCoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingHeader => write!(
                f,
                "missing problem line (p cnf ...), expected \"p cnf <num_vars> <num_clauses>\""
            ),
            Self::InvalidHeader {
                line_content,
                line_number,
            } => {
                write!(f, "line {line_number}: invalid problem line: {line_content} (expected \"p cnf <num_vars> <num_clauses>\")")
            }
            Self::DuplicateHeader { line_number } => {
                write!(f, "line {line_number}: duplicate problem line")
            }
            Self::InvalidLiteral { token, line_number } => {
                write!(
                    f,
                    "line {line_number}: invalid literal \"{token}\", expected integer"
                )
            }
            Self::IoError(s) => write!(f, "I/O error: {s}"),
            Self::VariableOutOfRange {
                var,
                max,
                line_number,
            } => {
                write!(f, "line {line_number}: variable {var} out of range (declared max {max} in header)")
            }
            Self::HeaderCountTooLarge {
                what,
                declared,
                max,
            } => {
                write!(
                    f,
                    "declared {what} count {declared} exceeds the maximum supported {max}; \
                     refusing to allocate (possible malformed/adversarial header)"
                )
            }
            Self::UnsupportedTaggedLine { tag } => {
                write!(
                    f,
                    "tagged line '{tag}' is not valid CNF (QDIMACS or WCNF input? \
                     use `ay qbf solve FILE` / `ay maxsat solve FILE`)"
                )
            }
        }
    }
}

impl std::error::Error for DimacsCoreError {}

/// A parsed DIMACS record (clause or tagged line).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DimacsRecord {
    /// Clause: raw signed literals (positive = true, negative = false).
    /// Empty vec represents the empty clause (signals UNSAT).
    Clause(Vec<i32>),
    /// Tagged line: single-character prefix followed by integer values.
    /// Used for XOR (`x`), existential (`e`), and universal (`a`) quantifiers.
    Tagged {
        /// The tag character (e.g., 'x', 'e', 'a').
        tag: char,
        /// Raw integer values after the tag, before the terminating 0.
        values: Vec<i32>,
    },
}

/// Borrowed DIMACS record emitted by the streaming parser.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum DimacsRecordRef<'a> {
    /// Clause: raw signed literals (positive = true, negative = false).
    Clause(&'a [i32]),
    /// Tagged line: single-character prefix followed by integer values.
    Tagged {
        /// The tag character (e.g., 'x', 'e', 'a').
        tag: char,
        /// Raw integer values after the tag, before the terminating 0.
        values: &'a [i32],
    },
}

/// DIMACS parser event emitted in input order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum DimacsEvent<'a> {
    /// Parsed `p cnf` header.
    Header(DimacsHeader),
    /// Parsed clause or tagged line.
    Record(DimacsRecordRef<'a>),
}

/// Parse a DIMACS-family input and stream parser events to `sink`.
///
/// This is the single-pass form of [`parse_dimacs_records`]. It preserves the
/// same tokenization and validation behavior without materializing the full
/// record list.
pub fn parse_dimacs_events<R, F>(reader: R, mut sink: F) -> Result<DimacsHeader, DimacsCoreError>
where
    R: Read,
    F: FnMut(DimacsEvent<'_>) -> Result<(), DimacsCoreError>,
{
    let mut reader = BufReader::new(reader);
    let mut header: Option<DimacsHeader> = None;
    let mut current_clause: Vec<i32> = Vec::new();
    let mut tagged_values: Vec<i32> = Vec::new();
    let mut line_number: usize = 0;
    let mut line_buf: Vec<u8> = Vec::with_capacity(4096);

    loop {
        line_buf.clear();
        let read = reader
            .read_until(b'\n', &mut line_buf)
            .map_err(|e| DimacsCoreError::IoError(e.to_string()))?;
        if read == 0 {
            break;
        }
        line_number += 1;
        let line = trim_ascii(&line_buf);

        // Skip empty lines and comments
        if line.is_empty() || line[0] == b'c' {
            continue;
        }

        // `%` is an end-of-file marker in SAT competition DIMACS files
        if line[0] == b'%' {
            break;
        }

        // Problem header line
        if line[0] == b'p' {
            if header.is_some() {
                return Err(DimacsCoreError::DuplicateHeader { line_number });
            }
            // Header counts are untrusted metadata and do not size allocations
            // in parser consumers. Actual-content caps are applied by the
            // allocating adapters after this streaming pass.
            let parsed = parse_header_line(line, line_number)?;
            header = Some(parsed);
            sink(DimacsEvent::Header(parsed))?;
            continue;
        }

        // DIMACS literals are i32, but an over-declared header may exceed u32
        // on a 64-bit host. Saturate instead of truncating the header modulo
        // 2^32, which would spuriously reject otherwise tiny valid content.
        let max_var = u32::try_from(header.ok_or(DimacsCoreError::MissingHeader)?.num_vars)
            .unwrap_or(u32::MAX);

        // Tagged line: first non-whitespace char is a letter
        let first_byte = line[0]; // line is non-empty (checked above)
        if first_byte.is_ascii_alphabetic() {
            let tag = first_byte as char;
            tagged_values.clear();
            // Strip the tag character; remainder may start with a digit or space
            let content = &line[1..];
            for token in ByteTokens::new(content) {
                let val =
                    parse_i32_token(token).ok_or_else(|| invalid_literal(token, line_number))?;
                if val == 0 {
                    break;
                }
                tagged_values.push(val);
            }
            sink(DimacsEvent::Record(DimacsRecordRef::Tagged {
                tag,
                values: &tagged_values,
            }))?;
            continue;
        }

        // Clause line: parse i32 tokens, accumulate across lines until 0
        for token in ByteTokens::new(line) {
            let lit_val =
                parse_i32_token(token).ok_or_else(|| invalid_literal(token, line_number))?;

            if lit_val == 0 {
                // Flush accumulated clause (empty clauses are preserved)
                sink(DimacsEvent::Record(DimacsRecordRef::Clause(
                    &current_clause,
                )))?;
                current_clause.clear();
            } else {
                // Validate variable range
                let var = lit_val.unsigned_abs();
                if var > max_var {
                    return Err(DimacsCoreError::VariableOutOfRange {
                        var,
                        max: max_var,
                        line_number,
                    });
                }
                current_clause.push(lit_val);
            }
        }
    }

    // Handle final clause not terminated by 0
    if !current_clause.is_empty() {
        sink(DimacsEvent::Record(DimacsRecordRef::Clause(
            &current_clause,
        )))?;
    }

    header.ok_or(DimacsCoreError::MissingHeader)
}

struct ByteTokens<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> ByteTokens<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, pos: 0 }
    }
}

impl<'a> Iterator for ByteTokens<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<Self::Item> {
        while self.pos < self.bytes.len() && self.bytes[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
        if self.pos == self.bytes.len() {
            return None;
        }

        let start = self.pos;
        while self.pos < self.bytes.len() && !self.bytes[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
        Some(&self.bytes[start..self.pos])
    }
}

fn trim_ascii(bytes: &[u8]) -> &[u8] {
    let mut start = 0;
    while start < bytes.len() && bytes[start].is_ascii_whitespace() {
        start += 1;
    }

    let mut end = bytes.len();
    while end > start && bytes[end - 1].is_ascii_whitespace() {
        end -= 1;
    }

    &bytes[start..end]
}

fn parse_header_line(line: &[u8], line_number: usize) -> Result<DimacsHeader, DimacsCoreError> {
    let mut tokens = ByteTokens::new(line);
    let _problem = tokens
        .next()
        .ok_or_else(|| invalid_header(line, line_number))?;
    let kind = tokens
        .next()
        .ok_or_else(|| invalid_header(line, line_number))?;
    let vars = tokens
        .next()
        .ok_or_else(|| invalid_header(line, line_number))?;
    let clauses = tokens
        .next()
        .ok_or_else(|| invalid_header(line, line_number))?;

    if kind != b"cnf" {
        return Err(invalid_header(line, line_number));
    }

    let num_vars = parse_usize_token(vars).ok_or_else(|| invalid_header(line, line_number))?;
    let num_clauses =
        parse_usize_token(clauses).ok_or_else(|| invalid_header(line, line_number))?;

    // NOTE: the declared `num_vars` is deliberately NOT used to size any
    // allocation and is NOT range-checked here. It is untrusted metadata: an
    // over-declared header like `p cnf 4000000000 1` describes a valid instance
    // whose real variable count is tiny. Consumers size their per-variable state
    // by the variables that ACTUALLY appear (see `MAX_DIMACS_VARS` and the
    // content-driven sizing in `dimacs::parse` / the streaming path), so a lying
    // header can no longer drive an allocation.
    Ok(DimacsHeader {
        num_vars,
        num_clauses,
    })
}

fn parse_usize_token(token: &[u8]) -> Option<usize> {
    let mut pos = 0;
    if token.first() == Some(&b'+') {
        pos = 1;
    }
    if pos == token.len() {
        return None;
    }

    let mut value = 0usize;
    while pos < token.len() {
        let byte = token[pos];
        if !byte.is_ascii_digit() {
            return None;
        }
        value = value.checked_mul(10)?;
        value = value.checked_add(usize::from(byte - b'0'))?;
        pos += 1;
    }
    Some(value)
}

fn parse_i32_token(token: &[u8]) -> Option<i32> {
    let mut pos = 0;
    let mut negative = false;

    match token.first().copied() {
        Some(b'-') => {
            negative = true;
            pos = 1;
        }
        Some(b'+') => {
            pos = 1;
        }
        Some(_) => {}
        None => return None,
    }

    if pos == token.len() {
        return None;
    }

    let limit = if negative {
        i32::MAX as u32 + 1
    } else {
        i32::MAX as u32
    };
    let mut value = 0u32;
    while pos < token.len() {
        let byte = token[pos];
        if !byte.is_ascii_digit() {
            return None;
        }
        value = value.checked_mul(10)?;
        value = value.checked_add(u32::from(byte - b'0'))?;
        if value > limit {
            return None;
        }
        pos += 1;
    }

    if negative {
        if value == i32::MAX as u32 + 1 {
            Some(i32::MIN)
        } else {
            Some(-(value as i32))
        }
    } else {
        Some(value as i32)
    }
}

fn invalid_header(line: &[u8], line_number: usize) -> DimacsCoreError {
    DimacsCoreError::InvalidHeader {
        line_content: String::from_utf8_lossy(line).into_owned(),
        line_number,
    }
}

fn invalid_literal(token: &[u8], line_number: usize) -> DimacsCoreError {
    DimacsCoreError::InvalidLiteral {
        token: String::from_utf8_lossy(token).into_owned(),
        line_number,
    }
}

/// Parse a DIMACS-family input into a header and sequence of records.
///
/// Handles:
/// - Comment lines (`c ...`)
/// - Blank lines
/// - `%` end-of-file marker (terminates parsing)
/// - `p cnf <vars> <clauses>` header
/// - Multiline clause accumulation (tokens split by whitespace, 0 terminates)
/// - Tagged lines (first non-whitespace is a letter other than `c`/`p`):
///   single-line, values parsed until 0 or end-of-line
///
/// Variable range checking is applied to clause literals only. Tagged-line
/// values are passed through without validation (adapters validate them).
pub fn parse_dimacs_records<R: Read>(
    reader: R,
) -> Result<(DimacsHeader, Vec<DimacsRecord>), DimacsCoreError> {
    let mut header: Option<DimacsHeader> = None;
    let mut records: Vec<DimacsRecord> = Vec::new();
    let parsed_header = parse_dimacs_events(reader, |event| {
        match event {
            DimacsEvent::Header(parsed) => header = Some(parsed),
            DimacsEvent::Record(DimacsRecordRef::Clause(raw)) => {
                records.push(DimacsRecord::Clause(raw.to_vec()));
            }
            DimacsEvent::Record(DimacsRecordRef::Tagged { tag, values }) => {
                records.push(DimacsRecord::Tagged {
                    tag,
                    values: values.to_vec(),
                });
            }
        }
        Ok(())
    })?;

    Ok((header.unwrap_or(parsed_header), records))
}

/// Parse DIMACS-family records from a string (convenience wrapper).
pub fn parse_dimacs_records_str(
    input: &str,
) -> Result<(DimacsHeader, Vec<DimacsRecord>), DimacsCoreError> {
    parse_dimacs_records(input.as_bytes())
}

#[cfg(test)]
#[path = "dimacs_core_tests.rs"]
mod tests;
