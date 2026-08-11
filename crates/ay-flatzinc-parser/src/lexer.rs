// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// FlatZinc 2.8.5 lexer — hand-written tokenizer

use crate::error::ParseError;

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Literals
    IntLit(i64),
    FloatLit(f64),
    StringLit(String),
    // Keywords
    Array,
    Bool,
    Constraint,
    False,
    Float,
    Int,
    Maximize,
    Minimize,
    Of,
    Par,
    Predicate,
    Satisfy,
    Set,
    Solve,
    True,
    Var,
    // Identifiers
    Ident(String),
    // Punctuation
    Semicolon,
    Colon,
    Comma,
    Assign, // =
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    DotDot,     // ..
    ColonColon, // ::
    // End
    Eof,
}

#[derive(Debug, Clone)]
pub struct Located {
    pub token: Token,
    pub line: usize,
    pub col: usize,
}

pub struct Lexer<'a> {
    input: &'a [u8],
    pos: usize,
    line: usize,
    col: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input: input.as_bytes(),
            pos: 0,
            line: 1,
            col: 1,
        }
    }

    fn peek(&self) -> Option<u8> {
        self.input.get(self.pos).copied()
    }

    fn advance(&mut self) -> Option<u8> {
        let ch = self.input.get(self.pos).copied()?;
        self.pos += 1;
        if ch == b'\n' {
            self.line += 1;
            self.col = 1;
        } else if ch & 0b1100_0000 != 0b1000_0000 {
            // Count UTF-8 scalar values, not continuation bytes, so columns
            // remain meaningful after the Unicode allowed in string literals.
            self.col += 1;
        }
        Some(ch)
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            // Skip whitespace
            while let Some(ch) = self.peek() {
                if ch == b' ' || ch == b'\t' || ch == b'\n' || ch == b'\r' {
                    self.advance();
                } else {
                    break;
                }
            }
            // Skip line comments: % ...
            if self.peek() == Some(b'%') {
                while let Some(ch) = self.advance() {
                    if ch == b'\n' {
                        break;
                    }
                }
                continue;
            }
            break;
        }
    }

    fn read_number(&mut self) -> Result<Token, ParseError> {
        let start = self.pos;
        let line = self.line;
        let negative = self.peek() == Some(b'-');
        if negative {
            self.advance();
        }

        // FlatZinc integer literals include lower-case hexadecimal and octal
        // prefixes. Parse through i128 so -0x8000000000000000 can represent
        // i64::MIN before the final checked conversion.
        if self.peek() == Some(b'0') {
            let prefix = self.input.get(self.pos + 1).copied();
            let radix = match prefix {
                Some(b'x') => Some(16),
                Some(b'o') => Some(8),
                _ => None,
            };
            if let Some(radix) = radix {
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
                let digits =
                    std::str::from_utf8(&self.input[digits_start..self.pos]).map_err(|_| {
                        ParseError::InvalidInt {
                            line,
                            value: literal.to_string(),
                        }
                    })?;
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
                return Ok(Token::IntLit(value));
            }
        }

        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                self.advance();
            } else {
                break;
            }
        }
        // Check for float: digits followed by '.' and more digits
        let has_fraction = self.peek() == Some(b'.')
            && self.input.get(self.pos + 1).is_some_and(u8::is_ascii_digit);
        if has_fraction {
            self.advance(); // consume '.'
            while let Some(ch) = self.peek() {
                if ch.is_ascii_digit() {
                    self.advance();
                } else {
                    break;
                }
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

        if has_fraction || has_exponent {
            let s = std::str::from_utf8(&self.input[start..self.pos]).map_err(|_| {
                ParseError::InvalidFloat {
                    line,
                    value: "invalid UTF-8 float literal".to_string(),
                }
            })?;
            let val: f64 = s.parse().map_err(|_| ParseError::InvalidFloat {
                line,
                value: s.to_string(),
            })?;
            if !val.is_finite() {
                return Err(ParseError::InvalidFloat {
                    line,
                    value: s.to_string(),
                });
            }
            Ok(Token::FloatLit(val))
        } else {
            let s = std::str::from_utf8(&self.input[start..self.pos]).map_err(|_| {
                ParseError::InvalidInt {
                    line,
                    value: "invalid UTF-8 integer literal".to_string(),
                }
            })?;
            let val: i64 = s.parse().map_err(|_| ParseError::InvalidInt {
                line,
                value: s.to_string(),
            })?;
            Ok(Token::IntLit(val))
        }
    }

    fn read_string(&mut self) -> Result<Token, ParseError> {
        self.advance(); // consume opening quote
        let mut s = String::new();
        loop {
            let char_line = self.line;
            let char_col = self.col;
            match self.advance() {
                Some(b'"') => return Ok(Token::StringLit(s)),
                Some(b'\n' | b'\r') => {
                    return Err(ParseError::UnexpectedToken {
                        line: char_line,
                        col: char_col,
                        expected: "escaped newline or closing quote".to_string(),
                        found: "raw newline in string literal".to_string(),
                    });
                }
                Some(b'\\') => match self.advance() {
                    Some(b'n') => s.push('\n'),
                    Some(b't') => s.push('\t'),
                    Some(b'\\') => s.push('\\'),
                    Some(b'"') => s.push('"'),
                    Some(b'\n' | b'\r') => {
                        return Err(ParseError::UnexpectedToken {
                            line: char_line,
                            col: char_col,
                            expected: "escaped string character".to_string(),
                            found: "newline after backslash".to_string(),
                        });
                    }
                    Some(c) if c.is_ascii() => {
                        s.push('\\');
                        s.push(char::from(c));
                    }
                    Some(_) => {
                        // Unknown escapes are preserved verbatim. Decode the
                        // complete UTF-8 scalar rather than treating its first
                        // byte as a Latin-1 character.
                        let char_start = self.pos - 1;
                        let rest =
                            std::str::from_utf8(&self.input[char_start..]).map_err(|_| {
                                ParseError::UnexpectedToken {
                                    line: self.line,
                                    col: self.col.saturating_sub(1),
                                    expected: "valid UTF-8 escaped character".to_string(),
                                    found: "invalid UTF-8".to_string(),
                                }
                            })?;
                        let ch = rest
                            .chars()
                            .next()
                            .ok_or_else(|| ParseError::UnexpectedEof {
                                expected: "escaped string character".to_string(),
                            })?;
                        for _ in 1..ch.len_utf8() {
                            self.advance();
                        }
                        s.push('\\');
                        s.push(ch);
                    }
                    None => {
                        return Err(ParseError::UnexpectedEof {
                            expected: "string character".to_string(),
                        })
                    }
                },
                Some(c) if c.is_ascii() => s.push(char::from(c)),
                Some(_) => {
                    // `input` originated as `&str`, so the byte just consumed
                    // starts a valid UTF-8 scalar. Decode the complete scalar
                    // instead of treating each UTF-8 byte as a Latin-1 char.
                    let char_start = self.pos - 1;
                    let rest = std::str::from_utf8(&self.input[char_start..]).map_err(|_| {
                        ParseError::UnexpectedToken {
                            line: self.line,
                            col: self.col.saturating_sub(1),
                            expected: "valid UTF-8 string character".to_string(),
                            found: "invalid UTF-8".to_string(),
                        }
                    })?;
                    let ch = rest
                        .chars()
                        .next()
                        .ok_or_else(|| ParseError::UnexpectedEof {
                            expected: "string character".to_string(),
                        })?;
                    for _ in 1..ch.len_utf8() {
                        self.advance();
                    }
                    s.push(ch);
                }
                None => {
                    return Err(ParseError::UnexpectedEof {
                        expected: "closing quote".to_string(),
                    })
                }
            }
        }
    }

    fn read_punctuation(&mut self, ch: u8) -> Result<Option<Token>, ParseError> {
        let (line, col) = (self.line, self.col);
        match ch {
            b';' => {
                self.advance();
                Ok(Some(Token::Semicolon))
            }
            b',' => {
                self.advance();
                Ok(Some(Token::Comma))
            }
            b'(' => {
                self.advance();
                Ok(Some(Token::LParen))
            }
            b')' => {
                self.advance();
                Ok(Some(Token::RParen))
            }
            b'[' => {
                self.advance();
                Ok(Some(Token::LBracket))
            }
            b']' => {
                self.advance();
                Ok(Some(Token::RBracket))
            }
            b'{' => {
                self.advance();
                Ok(Some(Token::LBrace))
            }
            b'}' => {
                self.advance();
                Ok(Some(Token::RBrace))
            }
            b'=' => {
                self.advance();
                Ok(Some(Token::Assign))
            }
            b':' => {
                self.advance();
                Ok(Some(if self.peek() == Some(b':') {
                    self.advance();
                    Token::ColonColon
                } else {
                    Token::Colon
                }))
            }
            b'.' => {
                self.advance();
                if self.peek() == Some(b'.') {
                    self.advance();
                    Ok(Some(Token::DotDot))
                } else {
                    Err(ParseError::UnexpectedToken {
                        line,
                        col,
                        expected: "..".to_string(),
                        found: ".".to_string(),
                    })
                }
            }
            _ => Ok(None),
        }
    }

    fn read_ident_or_keyword(&mut self) -> Result<Token, ParseError> {
        let start = self.pos - 1; // first char already consumed
        while let Some(ch) = self.peek() {
            if ch.is_ascii_alphanumeric() || ch == b'_' {
                self.advance();
            } else {
                break;
            }
        }
        let word = std::str::from_utf8(&self.input[start..self.pos]).map_err(|_| {
            ParseError::UnexpectedToken {
                line: self.line,
                col: self.col,
                expected: "valid UTF-8 identifier".to_string(),
                found: "invalid UTF-8".to_string(),
            }
        })?;
        Ok(match word {
            "array" => Token::Array,
            "bool" => Token::Bool,
            "constraint" => Token::Constraint,
            "false" => Token::False,
            "float" => Token::Float,
            "int" => Token::Int,
            "maximize" => Token::Maximize,
            "minimize" => Token::Minimize,
            "of" => Token::Of,
            "par" => Token::Par,
            "predicate" => Token::Predicate,
            "satisfy" => Token::Satisfy,
            "set" => Token::Set,
            "solve" => Token::Solve,
            "true" => Token::True,
            "var" => Token::Var,
            _ => Token::Ident(word.to_string()),
        })
    }

    fn located(&self, token: Token, line: usize, col: usize) -> Located {
        Located { token, line, col }
    }

    pub fn next_token(&mut self) -> Result<Located, ParseError> {
        self.skip_whitespace_and_comments();
        let line = self.line;
        let col = self.col;

        let Some(ch) = self.peek() else {
            return Ok(self.located(Token::Eof, line, col));
        };

        // Punctuation
        if let Some(tok) = self.read_punctuation(ch)? {
            return Ok(self.located(tok, line, col));
        }

        // String literals
        if ch == b'"' {
            let tok = self.read_string()?;
            return Ok(self.located(tok, line, col));
        }

        // Numbers (including negative)
        let is_negative_num =
            ch == b'-' && self.input.get(self.pos + 1).is_some_and(u8::is_ascii_digit);
        if ch.is_ascii_digit() || is_negative_num {
            let tok = self.read_number()?;
            return Ok(self.located(tok, line, col));
        }

        // Identifiers and keywords
        if ch.is_ascii_alphabetic() || ch == b'_' {
            self.advance();
            let tok = self.read_ident_or_keyword()?;
            return Ok(self.located(tok, line, col));
        }

        self.advance();
        Err(ParseError::UnexpectedToken {
            line,
            col,
            expected: "valid token".to_string(),
            found: format!("{}", ch as char),
        })
    }

    pub fn tokenize_all(&mut self) -> Result<Vec<Located>, ParseError> {
        let mut tokens = Vec::new();
        loop {
            let loc = self.next_token()?;
            if loc.token == Token::Eof {
                tokens.push(loc);
                break;
            }
            tokens.push(loc);
        }
        Ok(tokens)
    }
}
