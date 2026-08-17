// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FlatZinc numeric literal tokenization.

use super::{Lexer, Token};
use crate::error::ParseError;

impl Lexer<'_> {
    pub(super) fn read_number(&mut self) -> Result<Token, ParseError> {
        let start = self.pos;
        let line = self.line;
        let negative = self.peek() == Some(b'-');
        if negative {
            self.advance();
        }

        if let Some(token) = self.read_prefixed_integer(start, line, negative)? {
            return Ok(token);
        }
        self.read_decimal_number(start, line)
    }

    /// Parse FlatZinc's lower-case hexadecimal and octal integer forms.
    fn read_prefixed_integer(
        &mut self,
        start: usize,
        line: usize,
        negative: bool,
    ) -> Result<Option<Token>, ParseError> {
        if self.peek() != Some(b'0') {
            return Ok(None);
        }
        let radix = match self.input.get(self.pos + 1).copied() {
            Some(b'x') => 16,
            Some(b'o') => 8,
            _ => return Ok(None),
        };

        self.advance();
        self.advance();
        let digits_start = self.pos;
        while self.peek().is_some_and(|ch| match radix {
            16 => ch.is_ascii_hexdigit(),
            8 => matches!(ch, b'0'..=b'7'),
            _ => false,
        }) {
            self.advance();
        }
        let literal = std::str::from_utf8(&self.input[start..self.pos]).map_err(|_| {
            ParseError::InvalidInt {
                line,
                value: "invalid UTF-8 integer literal".to_string(),
            }
        })?;
        if self.pos == digits_start {
            return Err(ParseError::InvalidInt {
                line,
                value: literal.to_string(),
            });
        }
        let digits = std::str::from_utf8(&self.input[digits_start..self.pos]).map_err(|_| {
            ParseError::InvalidInt {
                line,
                value: literal.to_string(),
            }
        })?;
        // Parse through i128 so -0x8000000000000000 can represent i64::MIN
        // before the final checked conversion.
        let magnitude =
            i128::from_str_radix(digits, radix).map_err(|_| ParseError::InvalidInt {
                line,
                value: literal.to_string(),
            })?;
        let signed = if negative { -magnitude } else { magnitude };
        let value = i64::try_from(signed).map_err(|_| ParseError::InvalidInt {
            line,
            value: literal.to_string(),
        })?;
        Ok(Some(Token::IntLit(value)))
    }

    fn read_decimal_number(&mut self, start: usize, line: usize) -> Result<Token, ParseError> {
        while self.peek().is_some_and(|ch| ch.is_ascii_digit()) {
            self.advance();
        }
        let has_fraction = self.peek() == Some(b'.')
            && self.input.get(self.pos + 1).is_some_and(u8::is_ascii_digit);
        if has_fraction {
            self.advance();
            while self.peek().is_some_and(|ch| ch.is_ascii_digit()) {
                self.advance();
            }
        }

        // The exponent-only form (for example `3e8`) is a float too.
        let has_exponent = self.peek() == Some(b'e') || self.peek() == Some(b'E');
        if has_exponent {
            self.advance();
            if self.peek() == Some(b'+') || self.peek() == Some(b'-') {
                self.advance();
            }
            while self.peek().is_some_and(|ch| ch.is_ascii_digit()) {
                self.advance();
            }
        }

        let literal = std::str::from_utf8(&self.input[start..self.pos]);
        if has_fraction || has_exponent {
            let value = literal.map_err(|_| ParseError::InvalidFloat {
                line,
                value: "invalid UTF-8 float literal".to_string(),
            })?;
            let parsed: f64 = value.parse().map_err(|_| ParseError::InvalidFloat {
                line,
                value: value.to_string(),
            })?;
            if !parsed.is_finite() {
                return Err(ParseError::InvalidFloat {
                    line,
                    value: value.to_string(),
                });
            }
            Ok(Token::FloatLit(parsed))
        } else {
            let value = literal.map_err(|_| ParseError::InvalidInt {
                line,
                value: "invalid UTF-8 integer literal".to_string(),
            })?;
            let parsed = value.parse().map_err(|_| ParseError::InvalidInt {
                line,
                value: value.to_string(),
            })?;
            Ok(Token::IntLit(parsed))
        }
    }
}
