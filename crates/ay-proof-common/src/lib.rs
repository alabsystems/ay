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

// `literal.rs` carries native Trust contract clauses, which are RAW GRAMMAR:
// cfg-stripping runs after parsing, so no `cfg` inside that file can hide them and
// a compiler without the extension rejects the file outright. It cannot move to
// answer that either — the ratchet baseline keys 15 solver-discharged obligations
// by this path, and a vanished key is a LOST PROOF to
// `scripts/trust_ratchet_accounting.py`. So the verifier reads it, and everyone else reads the
// checked-in `literal_stock.rs` twin, with `build.rs` refusing any semantic drift
// between the two forms.
#[path = "literal_stock.rs"]
pub mod literal;

pub use error::ParseError;
pub use literal::LiteralError;
