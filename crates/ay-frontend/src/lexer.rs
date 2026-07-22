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
#[logos(skip r";[^\n]*")]
pub(crate) enum Token<'a> {
    /// Left parenthesis
    #[token("(")]
    LParen,

    /// Right parenthesis
    #[token(")")]
    RParen,

    /// Numeral (non-negative integer)
    #[regex(r"[0-9]+", |lex| lex.slice())]
    Numeral(&'a str),

    /// Decimal number
    #[regex(r"[0-9]+\.[0-9]+", |lex| lex.slice())]
    Decimal(&'a str),

    /// Hexadecimal bitvector literal (#xABCD)
    #[regex(r"#x[0-9a-fA-F]+", |lex| lex.slice())]
    Hexadecimal(&'a str),

    /// Binary bitvector literal (#b0101)
    #[regex(r"#b[01]+", |lex| lex.slice())]
    Binary(&'a str),

    /// String literal (SMT-LIB 2.6: `""` escapes a literal quote; also accepts `\"`)
    #[regex(r#""([^"\\]|\\.|"")*""#, |lex| lex.slice())]
    String(&'a str),

    /// Symbol (identifier)
    #[regex(r"[a-zA-Z~!@$%^&*_+=<>.?/\-][a-zA-Z0-9~!@$%^&*_+=<>.?/\-]*", |lex| lex.slice())]
    Symbol(&'a str),

    /// Quoted symbol |...|
    #[regex(r"\|[^|]*\|", |lex| lex.slice())]
    QuotedSymbol(&'a str),

    /// Keyword (:keyword)
    #[regex(r":[a-zA-Z0-9~!@$%^&*_+=<>.?/\-]+", |lex| lex.slice())]
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
