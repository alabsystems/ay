// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Typed errors for the `ay-bisect` library.
//!
//! Per `rust_excellence.md`: libraries use `thiserror` and a concrete `Error`
//! enum so callers can pattern-match on failure modes without stringly-typed
//! comparisons.

use std::path::PathBuf;

/// Errors produced by the bisect library.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum BisectError {
    /// The SMT-LIB2 file given to [`crate::bisect`] does not exist.
    #[error("SMT-LIB2 file not found: {path}")]
    FileNotFound { path: PathBuf },

    /// The `ay` binary could not be located.
    #[error("ay binary not found: {path}")]
    BinaryNotFound { path: String },

    /// Spawning the `ay` child process failed.
    #[error("failed to spawn ay binary '{binary}': {source}")]
    SpawnFailed {
        binary: String,
        #[source]
        source: std::io::Error,
    },

    /// Resource admission planning failed before any solver was launched.
    #[error("resource planning failed: {message}")]
    ResourcePlan { message: String },

    /// The per-run Rayon pool could not be constructed.
    #[error("failed to build bisect thread pool: {message}")]
    ThreadPool { message: String },

    /// The baseline trial (running ay with all features enabled) did not
    /// produce a definitive verdict. Bisect needs a definite sat/unsat
    /// baseline before it can search.
    #[error(
        "baseline trial produced {actual:?}; need definitive sat/unsat before bisecting (expected {expected})"
    )]
    BaselineIndeterminate {
        expected: &'static str,
        actual: crate::runner::SolveResult,
    },

    /// Internal library invariant violation. Should never surface in practice;
    /// filed as a typed variant so callers never see a panic.
    #[error("internal bisect error: {message}")]
    Internal { message: &'static str },
}

/// Crate-local `Result` alias.
pub type Result<T> = std::result::Result<T, BisectError>;
