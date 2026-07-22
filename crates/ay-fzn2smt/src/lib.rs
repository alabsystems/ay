// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ay-fzn2smt library — FlatZinc solving backends.
//!
//! Re-exports the SMT and CP solve modules so they can be called from
//! the unified `ay flatzinc` subcommand in the ay CLI crate.
//! `solve` is an SMT-solver facade over the canonical
//! `ay-flatzinc-smt::TranslationResult`; this crate should not grow a second
//! FlatZinc-to-SMT translator. `solve_cp` owns the separate direct CP backend
//! that lowers FlatZinc AST nodes into `ay-cp` constraints.
//!
//! Errors surfaced by the public API use the typed [`Fzn2smtError`]
//! enum defined in [`error`]; library callers that need `anyhow::Result`
//! can absorb the typed error through `?` because [`Fzn2smtError`]
//! implements [`std::error::Error`].

#![forbid(unsafe_code)]

pub mod error;
pub mod solve;
pub mod solve_cp;

pub use error::{Fzn2smtError, Result};
