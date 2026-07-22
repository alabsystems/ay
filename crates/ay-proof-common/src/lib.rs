// Copyright 2026 Andrew Yates
// Shared types and parsers for ay proof checker crates.
// Depends on thiserror for typed error enums.

#![forbid(unsafe_code)]

//! Shared types and parsers for the `ay` proof-checker crates.
//!
//! Common building blocks reused by `ay-drat-check` and `ay-lrat-check` so the
//! certificate checkers agree on formats: [`dimacs`] CNF parsing, [`literal`]
//! representation, [`leb128`] variable-length decoding for binary proofs, and
//! the shared typed [`error::ParseError`].

pub mod contracts;

pub mod dimacs;
pub mod error;
pub mod leb128;
pub mod literal;

pub use error::ParseError;
