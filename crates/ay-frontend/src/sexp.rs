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

/// Pre-computed table of byte offsets where each line starts.
/// Used for O(log N) byte-offset-to-line-number conversion.
struct LineOffsets {
    /// Byte offset of the start of each line (0-indexed).
    /// `offsets[0]` is always 0 (start of first line).
    offsets: Vec<usize>,
}

impl LineOffsets {
    /// Build the line-offset table from the input string.
    fn new(input: &str) -> Self {
        let mut offsets = vec![0];
        for (i, byte) in input.bytes().enumerate() {
            if byte == b'\n' {
                offsets.push(i + 1);
            }
        }
        Self { offsets }
    }

    /// Convert a byte offset to a 1-based line number.
    fn line_number(&self, byte_offset: usize) -> usize {
        // Binary search: find the last line start <= byte_offset
        match self.offsets.binary_search(&byte_offset) {
            Ok(idx) => idx + 1, // exact match: line starts here
            Err(idx) => idx,    // idx is the insertion point; line is idx (1-based)
        }
    }
}

/// S-expression parser
pub(crate) struct SExprParser<'a> {
    lexer: logos::Lexer<'a, Token<'a>>,
    current: Option<Result<Token<'a>, ()>>,
    /// Source text, retained so the line-offset table can be built lazily on
    /// the (rare) error path. Building it eagerly in `new` scanned the entire
    /// remaining input for every command — O(n^2) on large incremental files
    /// (e.g. QF_UF 2018-Goel-hwbench: ~36s, ~99% of runtime). It is only ever
    /// needed to render a line number in a `ParseError`, so defer it.
    input: &'a str,
}

impl<'a> SExprParser<'a> {
    /// Create a new parser for the given input
    #[must_use]
    pub(crate) fn new(input: &'a str) -> Self {
        let mut lexer = Token::lexer(input);
        let current = lexer.next();
        SExprParser {
            lexer,
            current,
            input,
        }
    }

    /// Create a parse error with line number from the current lexer span.
    fn error_at_current(&self, message: impl Into<String>) -> ParseError {
        let pos = self.lexer.span().start;
        // Build the line-offset table lazily here: errors are rare, so the
        // O(input length) scan happens at most once per failed parse rather
        // than once per command.
        let line = LineOffsets::new(self.input).line_number(pos);
        ParseError::with_line(message, pos, line)
    }

    /// Parse a single S-expression.
    ///
    /// List parsing is iterative (explicit heap stack) to support arbitrarily
    /// deep nesting without risking call-stack overflow.
    pub(crate) fn parse_sexp(&mut self) -> Result<SExpr, ParseError> {
        // Non-list atoms: handle directly (no nesting)
        match &self.current {
            None => return Err(self.error_at_current("Unexpected end of input")),
            Some(Err(())) => return Err(self.error_at_current("Invalid token")),
            Some(Ok(Token::RParen)) => return Err(self.error_at_current("Unexpected ')'")),
            Some(Ok(Token::LParen)) => {} // lists handled iteratively below
            _ => return self.parse_atom(),
        }

        // Iterative list parsing with explicit stack.
        // Each entry is the in-progress element list for one nesting level.
        let mut stack: Vec<Vec<SExpr>> = Vec::new();
        self.advance(); // consume opening '('
        stack.push(Vec::new());

        loop {
            match &self.current {
                None => return Err(self.error_at_current("Unexpected end of input in list")),
                Some(Err(())) => return Err(self.error_at_current("Invalid token in list")),
                Some(Ok(Token::RParen)) => {
                    self.advance(); // consume ')'
                    let Some(elements) = stack.pop() else {
                        return Err(self.error_at_current("Internal parser stack underflow"));
                    };
                    let completed = SExpr::List(elements);
                    match stack.last_mut() {
                        Some(parent) => parent.push(completed),
                        None => return Ok(completed), // outermost list complete
                    }
                }
                Some(Ok(Token::LParen)) => {
                    if stack.len() >= MAX_PARSE_DEPTH {
                        return Err(self.error_at_current(format!(
                            "Maximum nesting depth ({MAX_PARSE_DEPTH}) exceeded"
                        )));
                    }
                    self.advance(); // consume '('
                    stack.push(Vec::new());
                }
                _ => {
                    let atom = self.parse_atom()?;
                    let Some(current_list) = stack.last_mut() else {
                        return Err(self.error_at_current("Internal parser stack underflow"));
                    };
                    current_list.push(atom);
                }
            }
        }
    }

    /// Parse a non-list atom (symbol, keyword, numeral, etc.).
    /// Caller must ensure current token is not LParen or RParen.
    fn parse_atom(&mut self) -> Result<SExpr, ParseError> {
        match &self.current {
            None => Err(self.error_at_current("Unexpected end of input")),
            Some(Err(())) => Err(self.error_at_current("Invalid token")),
            Some(Ok(token)) => {
                let result =
                    match token {
                        Token::Symbol(s) => SExpr::Symbol((*s).to_string()),
                        Token::Keyword(k) => SExpr::Keyword((*k).to_string()),
                        Token::Numeral(n) => SExpr::Numeral((*n).to_string()),
                        Token::Decimal(d) => SExpr::Decimal((*d).to_string()),
                        Token::Hexadecimal(h) => SExpr::Hexadecimal((*h).to_string()),
                        Token::Binary(b) => SExpr::Binary((*b).to_string()),
                        Token::String(s) => {
                            let contents = &s[1..s.len() - 1];
                            if let Some(character) = contents
                                .chars()
                                .find(|&character| !is_smtlib_string_character(character))
                            {
                                return Err(self.error_at_current(format!(
                                    "string literal contains forbidden character U+{:04X}",
                                    u32::from(character)
                                )));
                            }
                            // Fail closed on a literal we cannot represent exactly.
                            // Substituting a replacement character (or dropping the
                            // escape) would change the string's length and silently
                            // flip every str.len/membership verdict mentioning it.
                            match unescape_string_contents(contents) {
                                Ok(decoded) => SExpr::String(decoded),
                                Err(err) => return Err(self.error_at_current(err.to_string())),
                            }
                        }
                        Token::QuotedSymbol(s) => {
                            let inner = &s[1..s.len() - 1];
                            match unescape_quoted_symbol_contents(inner) {
                                Ok(decoded) => SExpr::Symbol(decoded),
                                Err(character) => {
                                    return Err(self.error_at_current(format!(
                                        "quoted symbol contains forbidden character U+{:04X}",
                                        u32::from(character)
                                    )))
                                }
                            }
                        }
                        Token::True => SExpr::True,
                        Token::False => SExpr::False,
                        Token::InvalidLeadingZeroNumeral => return Err(self.error_at_current(
                            "numerals and the integer part of decimals may not have leading zeros",
                        )),
                        Token::LParen | Token::RParen => {
                            return Err(self.error_at_current("Expected atom, got parenthesis"))
                        }
                    };
                self.advance();
                Ok(result)
            }
        }
    }

    /// Advance to the next token
    fn advance(&mut self) {
        self.current = self.lexer.next();
    }

    /// Check if there are more tokens
    #[must_use]
    pub(crate) fn is_eof(&self) -> bool {
        self.current.is_none()
    }

    /// Byte offset (into the original input) of the next unconsumed token.
    ///
    /// The parser keeps a one-token lookahead in `current`, so after
    /// [`parse_sexp`](Self::parse_sexp) returns this is the start of the token
    /// that follows the S-expression just parsed (i.e. the start of the next
    /// command). At end of input it returns the input length.
    ///
    /// Used by the command-by-command driver to know how much of the input a
    /// single command consumed so it can resume parsing after the boundary.
    #[must_use]
    pub(crate) fn consumed_offset(&self) -> usize {
        if self.current.is_none() {
            self.lexer.source().len()
        } else {
            self.lexer.span().start
        }
    }

    /// Parse all S-expressions from the input
    pub(crate) fn parse_all(&mut self) -> Result<Vec<SExpr>, ParseError> {
        let mut result = Vec::new();
        while !self.is_eof() {
            result.push(self.parse_sexp()?);
        }
        Ok(result)
    }
}

fn is_smtlib_white_space(character: char) -> bool {
    matches!(character, '\t' | '\n' | '\r' | ' ')
}

fn is_smtlib_printable(character: char) -> bool {
    matches!(character, '\u{20}'..='\u{7e}') || u32::from(character) >= 0x80
}

fn is_smtlib_string_character(character: char) -> bool {
    is_smtlib_white_space(character) || is_smtlib_printable(character)
}

fn is_smtlib_quoted_symbol_character(character: char) -> bool {
    (is_smtlib_white_space(character) || is_smtlib_printable(character))
        && !matches!(character, '|' | '\\')
}

/// Decode Z3 5.0.0 quoted-symbol escapes. `\|` and `\\` denote the escaped
/// character; a backslash before any other printable character is retained,
/// matching Z3's scanner rather than silently changing the identifier.
fn unescape_quoted_symbol_contents(contents: &str) -> Result<String, char> {
    let mut decoded = String::with_capacity(contents.len());
    let mut characters = contents.chars();
    while let Some(character) = characters.next() {
        if character == '\\' {
            let escaped = characters.next().ok_or('\\')?;
            if matches!(escaped, '|' | '\\') {
                decoded.push(escaped);
            } else {
                if !is_smtlib_white_space(escaped) && !is_smtlib_printable(escaped) {
                    return Err(escaped);
                }
                decoded.push('\\');
                decoded.push(escaped);
            }
        } else {
            if !is_smtlib_quoted_symbol_character(character) {
                return Err(character);
            }
            decoded.push(character);
        }
    }
    Ok(decoded)
}

/// Parse a string into a single S-expression
pub fn parse_sexp(input: &str) -> Result<SExpr, ParseError> {
    let mut parser = SExprParser::new(input);
    let sexp = parser.parse_sexp()?;
    if parser.is_eof() {
        Ok(sexp)
    } else {
        Err(parser.error_at_current("Unexpected trailing input after S-expression"))
    }
}

/// Parse a string into multiple S-expressions
pub fn parse_sexps(input: &str) -> Result<Vec<SExpr>, ParseError> {
    let mut parser = SExprParser::new(input);
    parser.parse_all()
}

#[cfg(test)]
#[path = "sexp_tests.rs"]
mod tests;
