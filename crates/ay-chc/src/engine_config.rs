// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Common configuration for CHC engines.
//!
//! This module provides a base configuration struct that all CHC engines
//! can embed to avoid duplication of common fields like `verbose` and
//! `cancellation_token`.
//!
//! ## Usage
//!
//! Engines can embed `ChcEngineConfig` and delegate to its accessors:
//!
//! ```text
//! pub struct MyEngineConfig {
//!     pub base: ChcEngineConfig,
//!     pub engine_specific_field: usize,
//! }
//!
//! impl MyEngineConfig {
//!     pub fn verbose(&self) -> bool { self.base.verbose }
//!     pub fn is_cancelled(&self) -> bool { self.base.is_cancelled() }
//! }
//! ```
//!
//! See issue #2289 for consolidation tracking.

use crate::cancellation::CancellationToken;
use ay_core::TermStore;

/// Base configuration for CHC engines.
///
/// Contains fields common to all engine configs:
/// - `verbose`: Enable verbose logging
/// - `cancellation_token`: Cooperative cancellation for portfolio solving
///
/// Engines that use this base can delegate to its accessors to avoid
/// duplicating the cancellation check logic.
#[derive(Debug, Clone, Default)]
pub struct ChcEngineConfig {
    /// Enable verbose logging.
    pub verbose: bool,
    /// Cancellation token for cooperative stopping (portfolio solving).
    pub cancellation_token: Option<CancellationToken>,
}

impl ChcEngineConfig {
    /// Create a new config with default settings (verbose=false, no cancellation).
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new config with the specified verbosity.
    pub fn with_verbose(verbose: bool) -> Self {
        Self {
            verbose,
            cancellation_token: None,
        }
    }

    /// Check if the engine should stop.
    ///
    /// Returns true if either:
    /// - The cancellation token has been triggered (another engine found a result)
    /// - Global TermStore memory exceeds the budget (#2769)
    ///
    /// All engines already call `is_cancelled()` in their main loops (40+ sites),
    /// so adding the memory check here provides OOM defense everywhere for free.
    #[inline]
    pub fn is_cancelled(&self) -> bool {
        self.cancellation_token
            .as_ref()
            .is_some_and(CancellationToken::is_cancelled)
            || TermStore::global_memory_exceeded()
    }

    /// Builder: set verbose logging.
    #[must_use]
    pub fn verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Builder: set cancellation token.
    #[must_use]
    pub fn with_cancellation_token(mut self, token: Option<CancellationToken>) -> Self {
        self.cancellation_token = token;
        self
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "engine_config_tests.rs"]
mod tests;
