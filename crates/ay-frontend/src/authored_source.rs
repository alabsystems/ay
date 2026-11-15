// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lossless lexical capture before the ordinary parser discards quotation.
//!
//! This mirrors `lexer::Token` without folding, decoding or rendering tokens.
//! Every scanned byte uses the caller's shared authored-query work ledger, so
//! long comments, strings and quoted identifiers remain interruptible too.
//! Capturing tokens does NOT establish valid commands, typing or proof/source
//! authority. The normal parser and controlled semantic mapper must still bind
//! these occurrences to the complete original query.

use ay_core::original_query::{LiteralKind, QueryError, SymbolKind, WorkBudget};
use std::collections::BTreeMap;
use std::ops::Range;

mod cursor;
pub use cursor::SourceCursor;

/// Original lexical class, including reserved-looking quoted identifiers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceTokenKind {
    /// An opening list delimiter.
    LeftParen,
    /// A closing list delimiter.
    RightParen,
    /// A keyword, retaining the leading colon in its raw text.
    Keyword,
    /// A literal, retaining delimiters and its exact digit spelling.
    Literal(LiteralKind),
    /// A simple or quoted symbol, retaining original delimiters/escapes.
    Symbol(SymbolKind),
}

/// One original token, borrowing unchanged source bytes rather than Display.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceToken<'a> {
    /// Its original lexical classification.
    pub kind: SourceTokenKind,
    /// Exact raw token, including any quotation or literal prefix.
    pub raw: &'a str,
    /// Byte offsets into the separately retained complete original source.
    pub span: Range<usize>,
}

/// Lexical capture failure; neither refusal nor interruption grants authority.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum AuthoredSourceError {
    /// The original shared work/cancellation/deadline ledger refused admission.
    #[error(transparent)]
    Control(#[from] QueryError),
    /// Input cannot be tokenized by the native lexical grammar.
    #[error("invalid original source token at byte {offset}: {message}")]
    Lexical {
        /// Original byte offset, not an offset into a rendered expression.
        offset: usize,
        /// A fixed lexical rejection reason.
        message: &'static str,
    },
}

/// Immutable lexical occurrences and the exact complete original bytes.
#[derive(Debug)]
pub struct AuthoredSource<'a> {
    original: &'a str,
    tokens: BTreeMap<usize, SourceToken<'a>>,
}

impl<'a> AuthoredSource<'a> {
    /// Capture tokens with the same finite ledger used by semantic mapping.
    ///
    /// Whitespace/comments remain in `original`, not separate semantic tokens.
    /// No recursive tree, numeric conversion, token renderer or decoded copy is
    /// constructed. Balanced lists and valid command shapes are not implied.
    /// This compatibility capture retains a B-tree without storage admission;
    /// even a full-cost budget does not make it allocation-closed. Use
    /// `SourceCursor` when retained token storage is unnecessary.
    pub fn capture(
        original: &'a str,
        work: &mut WorkBudget<'_>,
    ) -> Result<Self, AuthoredSourceError> {
        work.charge(0)?;
        let mut scanner = Scanner {
            input: original,
            at: 0,
            work,
        };
        let mut tokens = BTreeMap::new();
        while scanner.at < original.len() {
            let byte = scanner.byte();
            if matches!(byte, b' ' | b'\t' | b'\n' | b'\r') {
                scanner.advance()?;
                continue;
            }
            if byte == b';' {
                scanner.comment()?;
                continue;
            }
            let start = scanner.at;
            let kind = scanner.token()?;
            // Constant-size keys/entries and bounded node splits avoid the
            // uninterruptible O(n) relocation of a growing token Vec. A binary
            // tree height upper-bounds BTree height; 16 node/key operations per
            // level conservatively price search/splits before allocation.
            let count = tokens.len();
            let height = usize::BITS - count.leading_zeros();
            scanner.work.charge(16 * (height as usize + 1))?;
            tokens.insert(
                count,
                SourceToken {
                    kind,
                    raw: &original[start..scanner.at],
                    span: start..scanner.at,
                },
            );
        }
        scanner.work.charge(0)?;
        Ok(Self { original, tokens })
    }

    /// Borrow exact original bytes, including comments and whitespace.
    pub fn original(&self) -> &'a str {
        self.original
    }

    /// Borrow ordered lexical occurrences without creating a contiguous copy.
    pub fn tokens(&self) -> impl ExactSizeIterator<Item = &SourceToken<'a>> {
        self.tokens.values()
    }

    /// Number of retained lexical occurrences, without scanning the capture.
    pub fn token_count(&self) -> usize {
        self.tokens.len()
    }
}

struct Scanner<'source, 'work, 'callback> {
    input: &'source str,
    at: usize,
    work: &'work mut WorkBudget<'callback>,
}

fn symbol_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || b"~!@$%^&*_+=<>.?/-".contains(&byte)
}

impl Scanner<'_, '_, '_> {
    fn byte(&self) -> u8 {
        self.input.as_bytes()[self.at]
    }

    fn advance(&mut self) -> Result<(), AuthoredSourceError> {
        self.work.charge(1)?;
        self.at += 1;
        Ok(())
    }

    fn error(&self, message: &'static str) -> AuthoredSourceError {
        AuthoredSourceError::Lexical {
            offset: self.at,
            message,
        }
    }

    fn while_bytes(&mut self, predicate: impl Fn(u8) -> bool) -> Result<(), AuthoredSourceError> {
        while self.at < self.input.len() && predicate(self.byte()) {
            self.advance()?;
        }
        Ok(())
    }

    fn comment(&mut self) -> Result<(), AuthoredSourceError> {
        self.while_bytes(|byte| !matches!(byte, b'\r' | b'\n'))
    }

    fn token(&mut self) -> Result<SourceTokenKind, AuthoredSourceError> {
        let start = self.at;
        match self.byte() {
            b'(' => {
                self.advance()?;
                Ok(SourceTokenKind::LeftParen)
            }
            b')' => {
                self.advance()?;
                Ok(SourceTokenKind::RightParen)
            }
            b'"' => {
                self.quoted(b'"')?;
                Ok(SourceTokenKind::Literal(LiteralKind::String))
            }
            b'|' => {
                self.quoted(b'|')?;
                Ok(SourceTokenKind::Symbol(SymbolKind::Quoted))
            }
            b'#' => self.bitvector(),
            b':' => {
                self.advance()?;
                if self.at == self.input.len() || !symbol_start(self.byte()) {
                    return Err(self.error("keyword requires a symbol"));
                }
                self.symbol()?;
                Ok(SourceTokenKind::Keyword)
            }
            byte if byte.is_ascii_digit() => self.number(),
            byte if symbol_start(byte) => {
                self.symbol()?;
                Ok(if matches!(&self.input[start..self.at], "true" | "false") {
                    SourceTokenKind::Literal(LiteralKind::Boolean)
                } else {
                    SourceTokenKind::Symbol(SymbolKind::Simple)
                })
            }
            _ => Err(self.error("unsupported token start")),
        }
    }

    fn symbol(&mut self) -> Result<(), AuthoredSourceError> {
        self.while_bytes(|byte| symbol_start(byte) || byte.is_ascii_digit())
    }

    fn number(&mut self) -> Result<SourceTokenKind, AuthoredSourceError> {
        let start = self.at;
        self.while_bytes(|byte| byte.is_ascii_digit())?;
        if self.input.as_bytes()[start] == b'0' && self.at - start > 1 {
            return Err(self.error("leading-zero numeral"));
        }
        let decimal = self.at + 1 < self.input.len()
            && self.byte() == b'.'
            && self.input.as_bytes()[self.at + 1].is_ascii_digit();
        if decimal {
            self.advance()?;
            self.while_bytes(|byte| byte.is_ascii_digit())?;
        }
        Ok(SourceTokenKind::Literal(if decimal {
            LiteralKind::Decimal
        } else {
            LiteralKind::Numeral
        }))
    }

    fn bitvector(&mut self) -> Result<SourceTokenKind, AuthoredSourceError> {
        self.advance()?;
        let kind = match self.input.as_bytes().get(self.at) {
            Some(b'x') => LiteralKind::Hexadecimal,
            Some(b'b') => LiteralKind::Binary,
            _ => return Err(self.error("bitvector requires #x or #b")),
        };
        self.advance()?;
        let start = self.at;
        self.while_bytes(|byte| {
            if kind == LiteralKind::Hexadecimal {
                byte.is_ascii_hexdigit()
            } else {
                matches!(byte, b'0' | b'1')
            }
        })?;
        if self.at == start {
            return Err(self.error("empty bitvector literal"));
        }
        Ok(SourceTokenKind::Literal(kind))
    }

    fn quoted(&mut self, delimiter: u8) -> Result<(), AuthoredSourceError> {
        self.advance()?;
        while self.at < self.input.len() {
            let byte = self.byte();
            self.advance()?;
            if delimiter == b'|' && byte == b'\\' {
                if self.at == self.input.len() || self.byte() == 0 {
                    return Err(self.error("invalid quoted-symbol escape"));
                }
                self.advance()?;
            } else if byte == delimiter {
                if delimiter == b'"' && self.at < self.input.len() && self.byte() == b'"' {
                    self.advance()?;
                } else {
                    return Ok(());
                }
            }
        }
        Err(self.error("unterminated quoted token"))
    }
}

#[cfg(test)]
mod tests;
