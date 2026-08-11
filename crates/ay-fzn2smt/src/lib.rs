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

use std::time::{Duration, Instant};

/// Largest timeout whose nanosecond representation fits a signed 64-bit
/// monotonic-clock interval. This is deliberately conservative across the
/// platform-specific `Instant` representations while still exceeding any
/// practical solver run (roughly 292 years).
const MAX_PORTABLE_TIMEOUT_MS: u64 = (i64::MAX as u64) / 1_000_000;

/// Convert an optional public millisecond timeout to a checked monotonic
/// deadline. Public solve entrypoints must use this instead of `Instant +
/// Duration`, whose overflow behavior is a panic and varies by platform.
pub(crate) fn checked_deadline(timeout_ms: Option<u64>) -> Result<Option<Instant>> {
    let Some(timeout_ms) = timeout_ms else {
        return Ok(None);
    };
    if timeout_ms > MAX_PORTABLE_TIMEOUT_MS {
        return Err(Fzn2smtError::InvalidTimeout { timeout_ms });
    }
    Instant::now()
        .checked_add(Duration::from_millis(timeout_ms))
        .map(Some)
        .ok_or(Fzn2smtError::InvalidTimeout { timeout_ms })
}
