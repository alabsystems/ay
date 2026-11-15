// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pinned Carcara's LEXER (`carcara/src/parser/lexer.rs` at 9a352ee) replayed
//! on one command's exact source text.
//!
//! Carcara tokenizes every command of the problem, including the ones its
//! `parse_problem` skips (`set-info`, `echo`, `get-value`, ...) and the
//! attributes `parse_annotated_term` skips (`:pattern`, `:qid`, ...). The
//! parsed command AY hands the rest of the scanner has lost what only the
//! lexer sees, so these are judged here:
//!
//! * a `\` inside a quoted symbol (`quoted symbol contains backslash`), which
//!   the AY/Z3 escape extension accepts, e.g. `(set-info :source |C:\x|)`;
//! * a string escape that decodes to a surrogate (`\u{d800}`, `\ud800`:
//!   `invalid Unicode value`);
//! * a numeral with a leading zero (`leading zero in numeral`);
//! * a number immediately followed by a symbol character: Carcara reads
//!   `-1x`, a legal SMT-LIB simple symbol, as the numeral `-1` and then `x`;
//! * `#` not followed by a non-empty `b`/`x` literal, and any character
//!   outside Carcara's symbol alphabet (`unexpected character`).

use std::iter::Peekable;
use std::str::Chars;

/// Why pinned Carcara's lexer cannot read `source` token for token as
/// SMT-LIB does, if it cannot.
pub(super) fn lexer_gap(source: &str) -> Option<String> {
    let mut lexer = Lexer {
        chars: source.chars().peekable(),
    };
    lexer.run().err()
}

struct Lexer<'a> {
    chars: Peekable<Chars<'a>>,
}

/// `carcara::utils::is_symbol_character`.
fn is_symbol_character(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || matches!(
            c,
            '+' | '-'
                | '/'
                | '*'
                | '='
                | '%'
                | '?'
                | '!'
                | '.'
                | '$'
                | '_'
                | '~'
                | '&'
                | '^'
                | '<'
                | '>'
                | '@'
                | '\''
        )
}

fn refuse(what: &str) -> String {
    format!("the problem text contains {what}, which pinned Carcara 1.1.0's lexer rejects")
}

impl Lexer<'_> {
    fn run(&mut self) -> Result<(), String> {
        loop {
            self.skip_whitespace_and_comments();
            let Some(c) = self.chars.peek().copied() else {
                return Ok(());
            };
            match c {
                '(' | ')' => {
                    self.chars.next();
                }
                '"' => self.string()?,
                '|' => self.quoted_symbol()?,
                ':' => {
                    self.chars.next();
                    self.take_while(is_symbol_character);
                }
                '#' => self.bitvector()?,
                '-' => {
                    self.chars.next();
                    if self.chars.peek().is_some_and(char::is_ascii_digit) {
                        self.number()?;
                    } else {
                        self.take_while(is_symbol_character);
                    }
                }
                c if c.is_ascii_digit() => self.number()?,
                c if is_symbol_character(c) => {
                    self.take_while(is_symbol_character);
                }
                other => return Err(refuse(&format!("the character `{other}`"))),
            }
        }
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            self.take_while(char::is_whitespace);
            if self.chars.peek() != Some(&';') {
                return;
            }
            self.take_while(|c| c != '\n');
        }
    }

    fn take_while(&mut self, predicate: impl Fn(char) -> bool) -> String {
        let mut taken = String::new();
        while let Some(&c) = self.chars.peek() {
            if !predicate(c) {
                break;
            }
            taken.push(c);
            self.chars.next();
        }
        taken
    }

    /// `Lexer::read_number`, then the token boundary SMT-LIB requires.
    fn number(&mut self) -> Result<(), String> {
        let whole = self.take_while(|c| c.is_ascii_digit());
        if whole.len() > 1 && whole.starts_with('0') {
            return Err(refuse(&format!(
                "the numeral `{whole}` with a leading zero"
            )));
        }
        if let Some(&delimiter @ ('/' | '.')) = self.chars.peek() {
            self.chars.next();
            let fraction = self.take_while(|c| c.is_ascii_digit());
            if matches!(self.chars.peek(), Some('/' | '.')) {
                return Err(refuse("a number with two `.` or `/` delimiters"));
            }
            if delimiter == '/' && fraction.bytes().all(|b| b == b'0') {
                return Err(refuse("a rational literal with a zero denominator"));
            }
        }
        if self.chars.peek().copied().is_some_and(is_symbol_character) {
            return Err(refuse(
                "a symbol that begins like a number (such as `-1x`), which Carcara splits \
                 into a numeral and a second token",
            ));
        }
        Ok(())
    }

    /// `Lexer::read_bitvector`, then the token boundary.
    fn bitvector(&mut self) -> Result<(), String> {
        self.chars.next();
        let radix = match self.chars.next() {
            Some('b') => 2,
            Some('x') => 16,
            _ => return Err(refuse("a `#` literal that is not `#b` or `#x`")),
        };
        if self.take_while(|c| c.is_digit(radix)).is_empty() {
            return Err(refuse("an empty bit-vector literal"));
        }
        if self.chars.peek().copied().is_some_and(is_symbol_character) {
            return Err(refuse(
                "a bit-vector literal followed by a symbol character",
            ));
        }
        Ok(())
    }

    /// `Lexer::read_quoted_symbol`.
    fn quoted_symbol(&mut self) -> Result<(), String> {
        self.chars.next();
        self.take_while(|c| c != '|' && c != '\\');
        match self.chars.next() {
            Some('|') => Ok(()),
            Some(_) => Err(refuse("a quoted symbol with a `\\`")),
            None => Err(refuse("an unterminated quoted symbol")),
        }
    }

    /// `Lexer::read_string` and `read_unicode_escape_sequence`.
    fn string(&mut self) -> Result<(), String> {
        self.chars.next();
        loop {
            match self.chars.next() {
                None => return Err(refuse("an unterminated string literal")),
                Some('"') if self.chars.peek() == Some(&'"') => {
                    self.chars.next();
                }
                Some('"') => return Ok(()),
                // Carcara does not consume the character after a `\` that
                // does not start `\u`; it is read as an ordinary one next.
                Some('\\') if self.chars.peek() == Some(&'u') => {
                    self.chars.next();
                    self.unicode_escape()?;
                }
                Some(_) => {}
            }
        }
    }

    fn unicode_escape(&mut self) -> Result<(), String> {
        let braced = self.chars.peek() == Some(&'{');
        if braced {
            self.chars.next();
        }
        let limit = if braced { 5 } else { 4 };
        let mut digits = String::new();
        while digits.len() < limit {
            match self.chars.peek() {
                Some(&c) if c.is_ascii_hexdigit() => {
                    digits.push(c);
                    self.chars.next();
                }
                None => return Err(refuse("an unterminated string literal")),
                Some(_) => break,
            }
        }
        if braced {
            if self.chars.peek() != Some(&'}') || digits.is_empty() {
                return Ok(());
            }
            self.chars.next();
        } else if digits.len() != 4 {
            return Ok(());
        }
        let code = u32::from_str_radix(&digits, 16).unwrap_or(u32::MAX);
        if braced && code > 0x2FFFF {
            return Ok(());
        }
        match char::from_u32(code) {
            Some(_) => Ok(()),
            None => Err(refuse(&format!(
                "the string escape for code point {code:#x}"
            ))),
        }
    }
}
