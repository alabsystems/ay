// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DPLL(T) error types.

/// Errors that can occur during DPLL(T) solving.
///
/// These replace panic paths (#5843) so downstream consumers (verification-consumer, deductive-checks)
/// can handle theory-SAT integration failures without `catch_unwind`.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum DpllError {
    /// Theory-SAT mapping produced too many partial clauses.
    /// Indicates a systematic theory integration bug (#4666).
    #[error("theory-SAT mapping failure: {0} partial clause events (limit 100)")]
    TheoryMappingOverflow(usize),

    /// Unexpected theory result variant during solve loop.
    #[error("unexpected theory result in solve loop")]
    UnexpectedTheoryResult,
}
