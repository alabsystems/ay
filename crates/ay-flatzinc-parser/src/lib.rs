// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// FlatZinc 2.8.5 parser — standalone crate for MiniZinc Challenge entry

#![forbid(unsafe_code)]

//! FlatZinc 2.8.5 parser for constraint-programming models.
//!
//! A standalone front end (no solver dependencies) that lexes and parses
//! FlatZinc into an [`ast::FznModel`]. It backs the unified `ay flatzinc`
//! CLI and the MiniZinc Challenge entry. The pipeline is
//! [`lexer`] -> [`parser`] -> [`ast`], with typed failures reported through
//! [`error`].

pub mod ast;
pub mod error;
pub mod lexer;
pub mod parser;
mod parser_types;

use ast::FznModel;
use error::ParseError;
use parser::Parser;

/// Parse a FlatZinc model from a string.
pub fn parse_flatzinc(input: &str) -> Result<FznModel, ParseError> {
    let mut parser = Parser::new(input)?;
    parser.parse_model()
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
