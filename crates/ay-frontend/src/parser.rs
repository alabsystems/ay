// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![deny(clippy::unwrap_used)]

//! SMT-LIB parser
//!
//! Parses SMT-LIB 2.7 input into commands.

use crate::command::Command;
use crate::sexp::{ParseError, SExpr, SExprParser};

/// SMT-LIB parser
pub(crate) struct Parser<'a> {
    sexp_parser: SExprParser<'a>,
}

impl<'a> Parser<'a> {
    /// Create a new parser for the given input
    #[must_use]
    pub(crate) fn new(input: &'a str) -> Self {
        Parser {
            sexp_parser: SExprParser::new(input),
        }
    }

    /// Parse the next command from the input
    ///
    /// Returns `None` when the input is exhausted.
    ///
    /// # Errors
    ///
    /// Returns an error if the input is malformed SMT-LIB.
    pub(crate) fn parse_command(&mut self) -> Result<Option<Command>, ParseError> {
        if self.sexp_parser.is_eof() {
            return Ok(None);
        }

        let sexp = self.sexp_parser.parse_sexp()?;
        let cmd = Command::from_sexp(&sexp)?;
        Ok(Some(cmd))
    }

    /// Parse all commands from the input
    ///
    /// # Errors
    ///
    /// Returns an error if the input is malformed SMT-LIB.
    pub(crate) fn parse_all(&mut self) -> Result<Vec<Command>, ParseError> {
        let mut commands = Vec::new();
        while let Some(cmd) = self.parse_command()? {
            commands.push(cmd);
        }
        Ok(commands)
    }
}

/// Parse SMT-LIB input into a list of commands
///
/// # Errors
///
/// Returns an error if the input is malformed SMT-LIB.
pub fn parse(input: &str) -> Result<Vec<Command>, ParseError> {
    let mut parser = Parser::new(input);
    parser.parse_all()
}

/// The outcome of pulling a single command from a [`CommandStream`].
///
/// A stream never aborts on a malformed command: it reports the error, resyncs
/// to the next top-level command boundary, and lets the caller decide whether
/// to keep going (z3-style continued-execution / `:error-behavior
/// continued-execution`).
#[derive(Debug)]
pub enum CommandStreamItem {
    /// A command parsed and elaborated successfully.
    Command(Box<Command>),
    /// A parse or elaboration error for one command. The stream has already
    /// skipped past the offending command, so the next call resumes with the
    /// command that follows it.
    Error(ParseError),
}

/// Maximum characters of a stray token echoed back in a
/// [`CommandStream`] error message before truncation.
const MAX_TOKEN_DISPLAY: usize = 32;

/// A command-by-command SMT-LIB parser with per-command error recovery.
///
/// Unlike [`parse`], which fails the whole input on the first malformed
/// command, a `CommandStream` isolates each top-level command: a syntax or
/// elaboration error on one command yields [`CommandStreamItem::Error`] and the
/// stream continues with subsequent commands. This mirrors z3's behavior of
/// printing `(error "...")` for a bad command and executing the rest of the
/// file.
///
/// The same parser internals (`parse_sexp` + `Command::from_sexp`) back this
/// driver, so accepted inputs and produced commands are identical to [`parse`];
/// only the error handling differs.
pub struct CommandStream<'a> {
    input: &'a str,
    /// Byte offset into `input` where the next command begins.
    cursor: usize,
}

impl<'a> CommandStream<'a> {
    /// Create a command stream over `input`.
    #[must_use]
    pub fn new(input: &'a str) -> Self {
        CommandStream { input, cursor: 0 }
    }

    /// Byte offset into the input where the NEXT command will be read from.
    ///
    /// Capturing this immediately before and after a [`Self::next_command`] call
    /// delimits the exact slice that command consumed — including, on a
    /// [`CommandStreamItem::Error`], the malformed text that was skipped. The CLI
    /// uses this to decide whether a discarded command contributed to the problem
    /// (so a later `check-sat` must fail closed) without relying on a separate,
    /// possibly-misaligned re-chunking of the source.
    #[must_use]
    pub fn position(&self) -> usize {
        self.cursor
    }

    /// Pull the next command (or per-command error) from the stream.
    ///
    /// Returns `None` once the input is exhausted. On error, the stream has
    /// already resynced past the offending command, so the following call
    /// resumes cleanly with the next command.
    pub fn next_command(&mut self) -> Option<CommandStreamItem> {
        // Skip leading whitespace/comments cheaply via the parser's own
        // tokenizer; an empty remaining slice means we're done.
        let remaining = self.input.get(self.cursor..)?;
        if remaining.is_empty() {
            return None;
        }

        let mut parser = SExprParser::new(remaining);
        if parser.is_eof() {
            // Only whitespace/comments left.
            self.cursor = self.input.len();
            return None;
        }

        // Absolute byte offset of this command's first token (the parser keeps
        // a one-token lookahead, so before parsing `consumed_offset` is the
        // start of that token). Used to attribute errors to the offending
        // token rather than to whatever the consumer guesses.
        let command_start = parser.consumed_offset();
        let token_start = self.cursor + command_start;

        match parser.parse_sexp() {
            Ok(sexp) => {
                // `parse_sexp` cleanly consumed one top-level S-expression and
                // positioned the lexer at the next command. Advance the cursor
                // by exactly what was consumed so recovery is independent of
                // how the command elaborates below.
                self.cursor += parser.consumed_offset();
                if sexp.as_list().is_none() {
                    // A bare atom at the top level is stray text, not a
                    // command. Coalesce the whole consecutive run of stray
                    // atoms into ONE positioned error instead of repeating an
                    // identical "Command must be a list" per token.
                    return Some(CommandStreamItem::Error(
                        self.stray_token_error(&sexp, token_start),
                    ));
                }
                match Command::from_sexp(&sexp) {
                    Ok(cmd) => Some(CommandStreamItem::Command(Box::new(cmd))),
                    Err(mut err) => {
                        // Attach the command's own position when the error
                        // carries none, so the report can point at the
                        // offending command.
                        if err.position.is_none() {
                            err.position = Some(token_start);
                            err.line = Some(line_col(self.input, token_start).0);
                        }
                        Some(CommandStreamItem::Error(err))
                    }
                }
            }
            Err(mut err) => {
                // Rebase the parser's slice-relative position onto the whole
                // input so the reported line number is absolute rather than
                // relative to this command's slice.
                if let Some(rel) = err.position {
                    let abs = self.cursor + rel;
                    err.position = Some(abs);
                    err.line = Some(line_col(self.input, abs).0);
                }
                // Distinguish an error *inside* a parenthesized command from a
                // stray top-level token. For a malformed command we discard its
                // balanced group. For a stray token (`)`, an invalid lexer
                // token, etc.) we stop at the next command's opening `(` and do
                // not consume that otherwise-valid command.
                let command_input = remaining.get(command_start..).unwrap_or_default();
                let next = if command_input.starts_with('(') {
                    end_of_parenthesized_command(command_input)
                } else {
                    next_command_start(command_input)
                };
                match next {
                    Some(offset) => self.cursor += command_start + offset,
                    None => self.cursor = self.input.len(),
                }
                Some(CommandStreamItem::Error(err))
            }
        }
    }

    /// Build a single positioned error for a run of stray top-level atoms,
    /// advancing the cursor past every consecutive atom (stopping at the next
    /// `(`-command, malformed text, or EOF). The first atom has already been
    /// consumed; `token_start` is its absolute byte offset.
    fn stray_token_error(&mut self, first: &SExpr, token_start: usize) -> ParseError {
        let mut skipped = 1usize;
        while let Some(remaining) = self.input.get(self.cursor..) {
            let mut parser = SExprParser::new(remaining);
            if parser.is_eof() {
                self.cursor = self.input.len();
                break;
            }
            match parser.parse_sexp() {
                // Only further atoms extend the run; a list is the next real
                // command and malformed text is reported on the next call.
                Ok(sexp) if sexp.as_list().is_none() => {
                    self.cursor += parser.consumed_offset();
                    skipped += 1;
                }
                _ => break,
            }
        }
        let (line, column) = line_col(self.input, token_start);
        let mut token = first.to_raw_string();
        if token.chars().count() > MAX_TOKEN_DISPLAY {
            token = token.chars().take(MAX_TOKEN_DISPLAY).collect();
            token.push_str("...");
        }
        let suffix = if skipped > 1 {
            format!(" (skipped {skipped} consecutive stray tokens)")
        } else {
            String::new()
        };
        ParseError::with_line(
            format!(
                "stray token '{token}' at line {line} column {column} is not a command; \
                 expected a parenthesized command such as (assert ...){suffix}"
            ),
            token_start,
            line,
        )
    }
}

/// 1-based line and column of byte offset `pos` within `input`.
///
/// Only used on error paths, so the O(input) scan is acceptable. `pos` is
/// clamped to the input length; columns count characters, matching the CLI's
/// own source-position accounting.
fn line_col(input: &str, pos: usize) -> (usize, usize) {
    let clamped = pos.min(input.len());
    let prefix = &input[..clamped];
    let line = prefix.bytes().filter(|&b| b == b'\n').count() + 1;
    let line_start = prefix.rfind('\n').map_or(0, |nl| nl + 1);
    let column = prefix[line_start..].chars().count() + 1;
    (line, column)
}

impl Iterator for CommandStream<'_> {
    type Item = CommandStreamItem;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_command()
    }
}

/// Find the byte offset, within `remaining`, where the next top-level command
/// plausibly begins after a malformed command.
///
/// Recovery strategy: the malformed command started at the first `(` in
/// `remaining`. We skip past its matching `)` (tracking nesting, string
/// literals, and `;` comments) and return the offset just after it. When the
/// parens never balance (truncated input), there is no further command, so we
/// return `None` and the caller drops the rest of the input.
fn end_of_parenthesized_command(remaining: &str) -> Option<usize> {
    let bytes = remaining.as_bytes();
    if bytes.first() != Some(&b'(') {
        return None;
    }

    let mut i = 0usize;
    let mut depth = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b';' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                continue;
            }
            b'"' => {
                i += 1;
                i = skip_string_literal(bytes, i);
                continue;
            }
            b'|' => {
                // Quoted symbol: skip escaped `\|` / `\\` as well as any
                // other Z3-compatible backslash escape. Parentheses and bars
                // inside the symbol are data, never command boundaries.
                i += 1;
                i = skip_quoted_symbol(bytes, i);
                continue;
            }
            b'(' => depth += 1,
            b')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    // Return the offset just past the matching ')'.
                    return Some(i + 1);
                }
            }
            _ => {}
        }
        i += 1;
    }
    // Parens never balanced: the rest of the input is one truncated command.
    None
}

/// Find the next unquoted, uncommented `(` without consuming it.
///
/// Used after a stray top-level token. Returning the opening parenthesis (not
/// the end of its group) is what preserves the following valid command.
fn next_command_start(remaining: &str) -> Option<usize> {
    let bytes = remaining.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => return Some(i),
            b';' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                continue;
            }
            b'"' => {
                i += 1;
                i = skip_string_literal(bytes, i);
                continue;
            }
            b'|' => {
                i += 1;
                i = skip_quoted_symbol(bytes, i);
                continue;
            }
            _ => i += 1,
        }
    }
    None
}

/// Advance `i` past the body of a string literal (the opening `"` already
/// consumed). Handles SMT-LIB's doubled-quote (`""`) escape.
fn skip_string_literal(bytes: &[u8], mut i: usize) -> usize {
    while i < bytes.len() {
        if bytes[i] == b'"' {
            // `""` is an escaped quote, not the terminator.
            if bytes.get(i + 1) == Some(&b'"') {
                i += 2;
                continue;
            }
            return i + 1;
        }
        i += 1;
    }
    i
}

/// Advance past a quoted symbol body (the opening `|` was already consumed).
/// A backslash quotes the following character in Z3's compatible extension,
/// so an escaped `|` cannot terminate the symbol.
fn skip_quoted_symbol(bytes: &[u8], mut i: usize) -> usize {
    while i < bytes.len() {
        match bytes[i] {
            b'\\' => {
                i += 1;
                if i < bytes.len() {
                    i += 1;
                }
            }
            b'|' => return i + 1,
            _ => i += 1,
        }
    }
    i
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::panic)]
#[path = "parser_tests.rs"]
mod tests;
