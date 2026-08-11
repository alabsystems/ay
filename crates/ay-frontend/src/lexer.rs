// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB lexer
//!
//! Tokenizes SMT-LIB 2.6 input using the logos crate for high performance.

use logos::Logos;

/// SMT-LIB tokens
#[derive(Logos, Debug, PartialEq, Eq, Clone)]
#[logos(skip r"[ \t\n\r]+")]
#[logos(skip r";[^\n\r]*")]
pub(crate) enum Token<'a> {
    /// Left parenthesis
    #[token("(")]
    LParen,

    /// Right parenthesis
    #[token(")")]
    RParen,

    /// Numeral (non-negative integer)
    #[regex(r"0|[1-9][0-9]*", |lex| lex.slice())]
    Numeral(&'a str),

    /// A digit run with a forbidden leading zero.
    ///
    /// This explicit longest-match token is needed because otherwise `00`
    /// would be tokenized as two adjacent legal `0` numerals.  In a variadic
    /// term such as `(= 00 0)` that would turn malformed lexical input into a
    /// different, well-formed term instead of rejecting it.
    #[regex(r"0[0-9]+(\.[0-9]+)?")]
    InvalidLeadingZeroNumeral,

    /// Decimal number
    #[regex(r"(0|[1-9][0-9]*)\.[0-9]+", |lex| lex.slice())]
    Decimal(&'a str),

    /// Hexadecimal bitvector literal (#xABCD)
    #[regex(r"#x[0-9a-fA-F]+", |lex| lex.slice())]
    Hexadecimal(&'a str),

    /// Binary bitvector literal (#b0101)
    #[regex(r"#b[01]+", |lex| lex.slice())]
    Binary(&'a str),

    /// String literal.
    ///
    /// SMT-LIB 2.6: the ONLY in-literal escape is `""`, which denotes one literal
    /// quote. Backslash is an ordinary printable character, NOT an escape — so a
    /// literal ends at the first unpaired `"` even when a backslash precedes it.
    ///
    /// The previous pattern carried a `\\.` alternative, which made the lexer
    /// treat `\"` as an escaped quote and therefore SWALLOW the terminating
    /// quote: `"a\"` was scanned past its real end and on into the rest of the
    /// file, so well-formed input z3 accepts (`(str.len "a\")` = 2) was rejected
    /// with "Invalid token in list". This mirrors the same backslash-is-not-an-
    /// escape rule already enforced when decoding contents in
    /// `ay_core::unescape_string_contents`.
    #[regex(r#""([^"]|"")*""#, |lex| lex.slice())]
    String(&'a str),

    /// Symbol (identifier)
    #[regex(r"[a-zA-Z~!@$%^&*_+=<>.?/\-][a-zA-Z0-9~!@$%^&*_+=<>.?/\-]*", |lex| lex.slice())]
    Symbol(&'a str),

    /// Quoted symbol `|...|`, including Z3 5.0.0's `\|` / `\\` escapes.
    #[regex(r"\|([^|\\]|\\[^\x00])*\|", |lex| lex.slice())]
    QuotedSymbol(&'a str),

    /// Keyword (:keyword)
    #[regex(r":[a-zA-Z~!@$%^&*_+=<>.?/\-][a-zA-Z0-9~!@$%^&*_+=<>.?/\-]*", |lex| lex.slice())]
    Keyword(&'a str),

    /// Reserved words: true/false
    #[token("true")]
    True,

    /// Boolean false
    #[token("false")]
    False,
    // Note: Indexed identifiers (_ symbol numeral+) are handled by the parser, not lexer
}

#[cfg(test)]
#[path = "lexer_tests.rs"]
mod tests;
