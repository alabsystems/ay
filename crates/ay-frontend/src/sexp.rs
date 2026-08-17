// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! S-expression representation and parsing
//!
//! SMT-LIB syntax is based on S-expressions.

use crate::lexer::Token;
use ay_core::{quote_symbol, string_literal, unescape_string_contents};
use logos::Logos;
use std::fmt;

/// An S-expression
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum SExpr {
    /// A symbol (identifier)
    Symbol(String),
    /// A keyword (:name)
    Keyword(String),
    /// A numeral
    Numeral(String),
    /// A decimal number
    Decimal(String),
    /// A hexadecimal bitvector
    Hexadecimal(String),
    /// A binary bitvector
    Binary(String),
    /// A string literal
    String(String),
    /// Boolean true
    True,
    /// Boolean false
    False,
    /// A list of S-expressions
    List(Vec<Self>),
}

/// Iterative drop to prevent stack overflow on deeply nested S-expressions.
/// Without this, dropping a deeply nested `List(vec![List(vec![...])])` would
/// recurse through `Vec::drop` → `SExpr::drop` for each nesting level.
impl Drop for SExpr {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        if let Self::List(items) = self {
            stack.append(items); // moves all children out; self becomes List(empty)
        }
        while let Some(mut item) = stack.pop() {
            if let Self::List(ref mut items) = item {
                stack.append(items); // extract children before item drops
            }
            // `item` drops here as either an atom or an empty List — O(1).
        }
    }
}

impl fmt::Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Symbol(s) => write!(f, "{}", quote_symbol(s)),
            Self::Keyword(k) => write!(f, "{k}"),
            Self::Numeral(n) => write!(f, "{n}"),
            Self::Decimal(d) => write!(f, "{d}"),
            Self::Hexadecimal(h) => write!(f, "{h}"),
            Self::Binary(b) => write!(f, "{b}"),
            Self::String(s) => write!(f, "{}", string_literal(s)),
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
            Self::List(items) => {
                write!(f, "(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{item}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Whether a bare symbol would fail to lex back as the SAME single symbol.
///
/// This is the *structural* half of SMT-LIB's quoting rule only. It covers the
/// empty symbol, a leading digit, and any character outside the simple-symbol
/// alphabet — the cases that actually corrupt a response:
///
/// ```text
/// |a b|  bare -> `a b`  splits into TWO tokens, changing the list's arity
/// |(|    bare -> `(`    opens a list, leaving the response unbalanced
/// ```
///
/// It deliberately omits the reserved-word half of `ay_core::quote_symbol`,
/// because a raw render emits those words in operator position where quoting
/// them changes the term.
fn raw_symbol_needs_quoting(name: &str) -> bool {
    // SMT-LIB simple-symbol alphabet: alphanumerics plus this punctuation set.
    const EXTRA: &[char] = &[
        '+', '-', '/', '*', '=', '%', '?', '!', '.', '$', '_', '~', '&', '^', '<', '>', '@',
    ];
    name.is_empty()
        || name.starts_with(|c: char| c.is_ascii_digit())
        || name.contains(|c: char| !c.is_ascii_alphanumeric() && !EXTRA.contains(&c))
}

impl SExpr {
    /// Check if this is a symbol with the given name
    #[must_use]
    pub fn is_symbol(&self, name: &str) -> bool {
        matches!(self, Self::Symbol(s) if s == name)
    }

    /// Get the symbol name if this is a symbol
    #[must_use]
    pub fn as_symbol(&self) -> Option<&str> {
        match self {
            Self::Symbol(s) => Some(s),
            _ => None,
        }
    }

    /// Get the list contents if this is a list
    #[must_use]
    pub fn as_list(&self) -> Option<&[Self]> {
        match self {
            Self::List(items) => Some(items),
            _ => None,
        }
    }

    /// Get the numeral value if this is a numeral
    #[must_use]
    pub fn as_numeral(&self) -> Option<&str> {
        match self {
            Self::Numeral(n) => Some(n),
            _ => None,
        }
    }

    /// Serialize this S-expression to a string without `quote_symbol` quoting.
    ///
    /// Unlike `Display`, which quotes reserved symbols (`as` → `|as|`, `_` → `|_|`),
    /// this produces the canonical SMT-LIB form with raw symbol names. Use this when
    /// the string will be re-parsed downstream (e.g., for sort extraction in the
    /// elaborator) to avoid needing dual-prefix workarounds.
    pub fn to_raw_string(&self) -> String {
        match self {
            // Re-quote. The lexer STRIPS the `|…|` delimiters when it builds a
            // `Symbol`, so echoing the bare name does not round-trip: `|a b|`
            // came back as `a b`, which changes the arity of the enclosing list,
            // and `|(|` came back as a bare `(`, which makes the whole response
            // unbalanced and unreadable to any s-expression parser:
            //
            //   (get-value (|a b|))   z3: ((|a b| false))   was: ((a b false))
            //   (get-value (|(|))     z3: ((|(| false))     was: ((( false))
            //
            // Quoted only when the bare text would not LEX BACK as one symbol.
            // Deliberately NOT `ay_core::quote_symbol`, which also quotes the
            // reserved words: a raw render puts `forall`, `exists`, `let`, `as`,
            // `_`, `!`, `par` and `match` in OPERATOR position, where `|forall|`
            // is a different term than `forall` and breaks the form outright.
            // (A user symbol genuinely named `forall` is indistinguishable here
            // because the lexer discards the delimiters — a pre-existing
            // round-trip limitation of `SExpr`, not one introduced by quoting.)
            Self::Symbol(s) => {
                if raw_symbol_needs_quoting(s) {
                    let mut quoted = String::with_capacity(s.len() + 2);
                    quoted.push('|');
                    for character in s.chars() {
                        // Z3 5.0.0 accepts `\|` and `\\` inside quoted symbols.
                        if matches!(character, '|' | '\\') {
                            quoted.push('\\');
                        }
                        quoted.push(character);
                    }
                    quoted.push('|');
                    quoted
                } else {
                    s.clone()
                }
            }
            Self::Keyword(k) => k.clone(),
            Self::Numeral(n) => n.clone(),
            Self::Decimal(d) => d.clone(),
            Self::Hexadecimal(h) => h.clone(),
            Self::Binary(b) => b.clone(),
            Self::String(s) => string_literal(s),
            Self::True => "true".to_string(),
            Self::False => "false".to_string(),
            Self::List(items) => {
                let mut out = String::from("(");
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    out.push_str(&item.to_raw_string());
                }
                out.push(')');
                out
            }
        }
    }
}

/// Parse error
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub struct ParseError {
    /// Error message
    pub message: String,
    /// Byte position in input (if available)
    pub position: Option<usize>,
    /// 1-based line number (if available)
    pub line: Option<usize>,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.line {
            Some(line) => write!(f, "line {line}: Parse error: {}", self.message),
            None => match self.position {
                Some(pos) => write!(f, "Parse error at position {pos}: {}", self.message),
                None => write!(f, "Parse error: {}", self.message),
            },
        }
    }
}

impl ParseError {
    /// Create a new parse error (no location info)
    #[must_use]
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            position: None,
            line: None,
        }
    }

    /// Create a new parse error with byte position (no line number)
    #[must_use]
    pub fn with_position(message: impl Into<String>, position: usize) -> Self {
        Self {
            message: message.into(),
            position: Some(position),
            line: None,
        }
    }

    /// Create a new parse error with byte position and line number
    #[must_use]
    pub fn with_line(message: impl Into<String>, position: usize, line: usize) -> Self {
        Self {
            message: message.into(),
            position: Some(position),
            line: Some(line),
        }
    }
}

/// Maximum nesting depth for S-expression parsing.
/// Protects against excessive memory allocation on pathologically nested input.
/// The parser uses iterative (heap-allocated stack) rather than recursive descent,
/// so this limit guards memory usage, not call-stack overflow.
/// At 1M depth the stack vector uses ~24MB (24 bytes per Vec entry), which is
/// negligible for a solver processing 100MB+ BMC benchmark files (#4602, #6888).
const MAX_PARSE_DEPTH: usize = 1_000_000;

/// Red zone size for `stacker::maybe_grow` in the parser.
/// When remaining stack space falls below this, stacker allocates a new segment.
pub(crate) const PARSE_STACK_RED_ZONE: usize = if cfg!(debug_assertions) {
    128 * 1024
} else {
    32 * 1024
};

/// Stack segment size allocated by stacker for parser recursion.
pub(crate) const PARSE_STACK_SIZE: usize = 2 * 1024 * 1024;

include!("sexp/parser.rs");

#[cfg(test)]
#[path = "sexp_tests.rs"]
mod tests;
