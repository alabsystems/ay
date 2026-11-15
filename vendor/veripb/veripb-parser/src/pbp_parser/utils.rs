//! Common parsing utilities for the VeriPB parse.

use std::fmt::Display;

use malachite_bigint::{BigInt, Sign};
use num_traits::Zero;
use veripb_formula::lit::Lit;

/// The current scope of the proof parser. The scopes are sorted by by their nesting level.
#[derive(Debug, PartialEq, PartialOrd)]
pub enum Scope {
    // TopLevel < Specification < Subproof < (Proof < Scope) < Proofgoal
    TopLevel = 0,
    Specification = 1,
    Subproof = 2,
    Proof = 3,
    #[allow(clippy::enum_variant_names)]
    Scope = 4,
    Proofgoal = 5,
}

impl Scope {
    /// Format the scope as a string.
    pub fn as_str(&self) -> &str {
        match self {
            Scope::TopLevel => "top level",
            Scope::Specification => "specification",
            Scope::Subproof => "subproof",
            Scope::Proof => "proof",
            Scope::Scope => "scope",
            Scope::Proofgoal => "proofgoal",
        }
    }
}

/// Non-operator tokens in a `pol`-rule.
#[derive(Debug, PartialEq)]
pub enum PolToken {
    ConstraintId(isize),
    NonNegativeIntegerOrID(isize),
    PositiveInteger(BigInt),
    Literal(Lit),
}

/// Position inside a proof file.
#[derive(Debug, Clone)]
pub struct Position {
    /// Byte position in the proof file.
    pub pos: usize,
    /// Position in the current line.
    pub col: usize,
    /// Line number in the file.
    pub line: usize,
}

/// Tokens considered by the VeriPB proof lexer.
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Space(usize),
    Tab(usize),
    Eol(usize),
    Comment(String),
    Identifier(String),
    Integer64(Sign, i64),
    Integer128(Sign, i128),
    IntegerAny(Sign, BigInt),
    Label(String),
    AuxiliaryVariable(String),
    ProofgoalID(usize),
    Colon,
    Semicolon,
    Tilde,
    GreaterEqual,
    LessEqual,
    LeftImplication,
    RightImplication,
    Plus,
    Star,
    MapsTo,
    Minus, // Needed to have `pseudo-Boolean` as three tokens.
    Dot,   // Needed for version number `3.0` as three tokens.
    Equal, // Needed for `=` in OPB files.
    Eof,   // Needed to avoid having options.
}

impl Token {
    /// Get the byte length of a token.
    pub fn str_len(&self) -> usize {
        match self {
            Token::Space(count) => *count,
            Token::Tab(count) => *count,
            Token::Eol(count) => *count,
            Token::Comment(comment) => comment.len() + 2,
            Token::Identifier(identifier) => identifier.len(),
            Token::Integer64(sign, value) => {
                value.to_string().len()
                    + if (*sign == Sign::Plus) || (*sign == Sign::Minus && *value == 0) {
                        1
                    } else {
                        0
                    }
            }
            Token::Integer128(sign, value) => {
                value.to_string().len()
                    + if (*sign == Sign::Plus) || (*sign == Sign::Minus && *value == 0) {
                        1
                    } else {
                        0
                    }
            }
            Token::IntegerAny(sign, value) => {
                value.to_string().len()
                    + if (*sign == Sign::Plus) || (*sign == Sign::Minus && value.is_zero()) {
                        1
                    } else {
                        0
                    }
            }
            Token::Label(label) => label.len(),
            Token::AuxiliaryVariable(name) => name.len(),
            Token::ProofgoalID(id) => id.to_string().len() + 1,
            Token::Colon => 1,
            Token::Semicolon => 1,
            Token::Tilde => 1,
            Token::GreaterEqual => 2,
            Token::LessEqual => 2,
            Token::LeftImplication => 3,
            Token::RightImplication => 3,
            Token::Plus => 1,
            Token::Star => 1,
            Token::MapsTo => 2,
            Token::Minus => 1,
            Token::Dot => 1,
            Token::Equal => 1,
            Token::Eof => 0,
        }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Space(count) => {
                write!(f, "{} space{}", count, if *count == 1 { "" } else { "s" })
            }
            Token::Tab(count) => write!(
                f,
                "{} character tabulator{}",
                count,
                if *count == 1 { "" } else { "s" }
            ),
            Token::Eol(_) => write!(f, "newline"),
            Token::Comment(comment) => write!(f, "`%{comment}`"),
            Token::Identifier(identifier) => write!(f, "`{identifier}`"),
            Token::Integer64(sign, value) => write!(
                f,
                "`{}{}`",
                if *sign == Sign::Plus {
                    "+"
                } else if *sign == Sign::Minus && *value == 0 {
                    "-"
                } else {
                    ""
                },
                value
            ),
            Token::Integer128(sign, value) => write!(
                f,
                "`{}{}`",
                if *sign == Sign::Plus {
                    "+"
                } else if *sign == Sign::Minus && *value == 0 {
                    "-"
                } else {
                    ""
                },
                value
            ),
            Token::IntegerAny(sign, value) => write!(
                f,
                "`{}{}`",
                if *sign == Sign::Plus {
                    "+"
                } else if *sign == Sign::Minus && value.is_zero() {
                    "-"
                } else {
                    ""
                },
                value
            ),
            Token::Label(label) => write!(f, "`{label}`"),
            Token::AuxiliaryVariable(name) => write!(f, "`{name}`"),
            Token::ProofgoalID(id) => write!(f, "`#{id}`"),
            Token::Colon => write!(f, "`:`"),
            Token::Semicolon => write!(f, "`;`"),
            Token::Tilde => write!(f, "`~`"),
            Token::GreaterEqual => write!(f, "`>=`"),
            Token::LessEqual => write!(f, "`<=`"),
            Token::LeftImplication => write!(f, "`<==`"),
            Token::RightImplication => write!(f, "`==>`"),
            Token::Plus => write!(f, "`+`"),
            Token::Star => write!(f, "`*`"),
            Token::MapsTo => write!(f, "`->`"),
            Token::Minus => write!(f, "`-`"),
            Token::Dot => write!(f, "`.`"),
            Token::Equal => write!(f, "`=`"),
            Token::Eof => write!(f, "end of file (EOF)"),
        }
    }
}
