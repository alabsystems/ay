// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counterexample output style selection.
//!
//! The executor stores this preference and may use it when formatting models.

/// Style of counterexample to generate
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub enum CounterexampleStyle {
    /// Fast, current behavior - return any satisfying value
    Any,
    /// Prefer minimal values: 0, ±1, powers of 2, MIN, MAX
    #[default]
    Minimal,
    /// Prefer human-readable values: round numbers, simple fractions
    Readable,
}

#[cfg(test)]
#[path = "minimize_tests.rs"]
mod tests;
