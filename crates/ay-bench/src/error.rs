// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Typed errors for the `ay-bench` library.
//!
//! Per `rust_excellence.md`: libraries use `thiserror` and a concrete `Error`
//! enum so callers can pattern-match on failure modes without stringly-typed
//! comparisons.
//!
//! The variants below cover every failure mode surfaced by the public
//! `cmd_*` entry points and by [`crate::db::ResultsStore`] /
//! [`crate::harvest::BaselineStore`]. Ad-hoc contextual messages previously
//! produced via `anyhow::Context::with_context` are mapped to
//! [`BenchError::Message`] so the migration is behaviour-preserving at the
//! error-text level while giving downstream callers a concrete type to match
//! on.
//!
//! History: ported from `anyhow::Result` per issue #8848.

use std::path::PathBuf;

/// Errors produced by the `ay-bench` library.
///
/// This enum is `#[non_exhaustive]` — new variants may be added in the
/// future. Match with a `_ =>` arm or match on specific variants you care
/// about (e.g. `BenchError::EvalNotFound` to distinguish user input errors
/// from infrastructure failures).
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum BenchError {
    /// The eval registry could not be located on disk.
    #[error("eval registry not found: {path}")]
    EvalRegistryMissing { path: PathBuf },

    /// One or more named eval IDs did not match any registered eval.
    #[error("unknown eval id(s): {ids}")]
    EvalNotFound {
        /// Comma-separated list of the unknown IDs.
        ids: String,
    },

    /// An eval spec YAML file could not be parsed.
    #[error("failed to parse eval spec {path}: {reason}")]
    EvalSpecParse { path: PathBuf, reason: String },

    /// A reference solver binary could not be located.
    #[error("could not find solver binary '{name}'")]
    SolverNotFound { name: String },

    /// The benchmarks directory referenced by a run does not exist.
    #[error("benchmarks directory not found: {path}")]
    BenchmarksDirMissing { path: PathBuf },

    /// Unsupported compression format for a benchmark archive.
    #[error("unsupported compression format: {path}")]
    UnsupportedFormat { path: PathBuf },

    /// Feature extraction requested for a file extension that is not yet
    /// supported (only DIMACS is wired up today).
    #[error(
        "feature extraction not implemented for .{extension} files (only DIMACS is supported)"
    )]
    UnsupportedFeatureFormat { extension: String },

    /// A required field was missing from a results JSON document.
    #[error("results JSON missing {field}")]
    MissingJsonField { field: String },

    /// Scoring judged the run as disqualified, unsound, or wrong.
    ///
    /// `cmd_score` surfaces these so calling tooling can distinguish a
    /// successful-but-failing score from a run-level infrastructure error.
    #[error("scoring failed: {reason}")]
    ScoringFailed { reason: String },

    /// Invalid arguments to a `cmd_*` entry point (e.g. no eval IDs and
    /// no `--all`/`--domain`, competition timeout mismatch, etc).
    #[error("invalid arguments: {reason}")]
    InvalidArgs { reason: String },

    /// I/O failure (file read, dir create, subprocess spawn, etc).
    #[error(transparent)]
    Io(#[from] std::io::Error),

    /// JSON (de)serialization failure.
    #[error(transparent)]
    Json(#[from] serde_json::Error),

    /// SQLite failure from the persistent results / baseline store.
    #[error(transparent)]
    Sqlite(#[from] rusqlite::Error),

    /// Thread-pool construction failure (rayon).
    #[error("failed to build thread pool: {0}")]
    ThreadPool(String),

    /// Contextual message that does not fit the structured variants above.
    ///
    /// Used for messages previously produced via
    /// `anyhow::Context::with_context`. Callers that need to distinguish the
    /// underlying cause should prefer matching on the typed variants.
    #[error("{0}")]
    Message(String),
}

impl BenchError {
    /// Construct a [`BenchError::Message`] from anything printable.
    ///
    /// Shorthand for `BenchError::Message(format!(...))`. Prefer a
    /// structured variant when one fits.
    #[must_use]
    pub fn msg(message: impl Into<String>) -> Self {
        Self::Message(message.into())
    }
}

/// Library-wide `Result` alias.
pub type Result<T, E = BenchError> = std::result::Result<T, E>;

/// Helper trait to add ad-hoc string context to a result while keeping the
/// error type as [`BenchError`].
///
/// Mirrors `anyhow::Context::with_context` / `.context(...)` semantics but
/// stays inside the crate's typed error hierarchy. The original error
/// message is appended as `": {source}"` so human-facing output remains
/// consistent with the pre-migration `anyhow` behaviour.
pub trait WithContext<T> {
    /// Wrap the error with a contextual message (lazy variant).
    fn with_bench_context<C, F>(self, f: F) -> Result<T>
    where
        C: std::fmt::Display,
        F: FnOnce() -> C;

    /// Wrap the error with a contextual message (eager variant).
    fn bench_context<C>(self, context: C) -> Result<T>
    where
        C: std::fmt::Display;
}

impl<T, E> WithContext<T> for std::result::Result<T, E>
where
    E: std::fmt::Display,
{
    fn with_bench_context<C, F>(self, f: F) -> Result<T>
    where
        C: std::fmt::Display,
        F: FnOnce() -> C,
    {
        self.map_err(|e| BenchError::Message(format!("{}: {e}", f())))
    }

    fn bench_context<C>(self, context: C) -> Result<T>
    where
        C: std::fmt::Display,
    {
        self.map_err(|e| BenchError::Message(format!("{context}: {e}")))
    }
}
