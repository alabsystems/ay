// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Token/character-level helpers for the CHC parser.
//!
//! Pure cursor management over `input`/`pos`. Reused by every other parser
//! submodule.

use super::ChcParser;
use crate::{ChcError, ChcResult};

impl ChcParser {
    /// Parse a symbol
    pub(super) fn parse_symbol(&mut self) -> ChcResult<String> {
        self.skip_whitespace_and_comments();

        let start = self.pos;

        // Check for quoted symbol
        if self.peek_char() == Some('|') {
            self.pos += 1;
            let content_start = self.pos;
            while self.pos < self.input.len() && self.current_char() != Some('|') {
                self.pos += 1;
            }
            let symbol = self.input[content_start..self.pos].to_string();
            if self.current_char() == Some('|') {
                self.pos += 1;
            }
            return Ok(symbol);
        }

        // Regular symbol
        while self.pos < self.input.len() {
            match self.current_char() {
                Some(c) if is_symbol_char(c) => self.pos += 1,
                _ => break,
            }
        }

        if start == self.pos {
            return Err(ChcError::Parse("Expected symbol".into()));
        }

        Ok(self.input[start..self.pos].to_string())
    }

    /// Parse a numeral
    pub(super) fn parse_numeral(&mut self) -> ChcResult<String> {
        self.skip_whitespace_and_comments();

        let start = self.pos;
        let mut has_sign = false;

        // Optional sign
        if self.peek_char() == Some('-') {
            self.pos += 1;
            has_sign = true;
        }

        // Digits
        while self.pos < self.input.len() {
            match self.current_char() {
                Some(c) if c.is_ascii_digit() => self.pos += 1,
                _ => break,
            }
        }

        if start == self.pos || (has_sign && self.pos == start + 1) {
            return Err(ChcError::Parse("Expected numeral".into()));
        }

        Ok(self.input[start..self.pos].to_string())
    }

    /// Parse an integer or decimal numeric literal in expression position.
    pub(super) fn parse_numeric_literal(&mut self) -> ChcResult<String> {
        self.skip_whitespace_and_comments();

        let start = self.pos;
        let mut has_sign = false;

        if self.peek_char() == Some('-') {
            self.pos += 1;
            has_sign = true;
        }

        let digit_start = self.pos;
        while self.pos < self.input.len() {
            match self.current_char() {
                Some(c) if c.is_ascii_digit() => self.pos += 1,
                _ => break,
            }
        }
        let digits_before_dot = self.pos - digit_start;

        if self.peek_char() == Some('.') {
            self.pos += 1;
            let frac_start = self.pos;
            while self.pos < self.input.len() {
                match self.current_char() {
                    Some(c) if c.is_ascii_digit() => self.pos += 1,
                    _ => break,
                }
            }
            if digits_before_dot == 0 || self.pos == frac_start {
                return Err(ChcError::Parse("Invalid decimal numeral".into()));
            }
        }

        if start == self.pos || (has_sign && self.pos == start + 1) {
            return Err(ChcError::Parse("Expected numeral".into()));
        }

        Ok(self.input[start..self.pos].to_string())
    }

    /// Skip whitespace and comments
    pub(super) fn skip_whitespace_and_comments(&mut self) {
        while self.pos < self.input.len() {
            match self.current_char() {
                Some(c) if c.is_whitespace() => self.pos += c.len_utf8(),
                Some(';') => {
                    // Skip until end of line (handle multi-byte UTF-8 chars in comments)
                    while self.pos < self.input.len() {
                        if let Some(c) = self.current_char() {
                            if c == '\n' {
                                break;
                            }
                            self.pos += c.len_utf8();
                        } else {
                            break;
                        }
                    }
                }
                _ => break,
            }
        }
    }

    /// Expect and consume a specific character
    pub(super) fn expect_char(&mut self, expected: char) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        match self.current_char() {
            Some(c) if c == expected => {
                self.pos += 1;
                Ok(())
            }
            Some(c) => Err(ChcError::Parse(format!(
                "Expected '{expected}', found '{c}'"
            ))),
            None => Err(ChcError::Parse(format!(
                "Expected '{expected}', found end of input"
            ))),
        }
    }

    /// Get current character
    pub(super) fn current_char(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    /// Peek at current character without consuming
    pub(super) fn peek_char(&self) -> Option<char> {
        self.current_char()
    }
}

/// Check if a character is valid in a symbol
/// Note: includes `'` for primed variables (e.g., x' for next-state)
pub(super) fn is_symbol_char(c: char) -> bool {
    c.is_alphanumeric()
        || matches!(
            c,
            '_' | '-'
                | '+'
                | '*'
                | '/'
                | '.'
                | '!'
                | '@'
                | '#'
                | '$'
                | '%'
                | '^'
                | '&'
                | '<'
                | '>'
                | '='
                | '?'
                | '~'
                | '\''
        )
}
