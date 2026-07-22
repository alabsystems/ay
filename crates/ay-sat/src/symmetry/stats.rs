// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Minimal symmetry-preprocessing statistics.

/// Reason the symmetry pass did not emit any symmetry-breaking clauses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SymmetrySkipReason {
    Disabled,
    Incremental,
    ProofMode,
    TooLarge,
    NoActiveClauses,
    NoPairs,
}

/// Root symmetry-preprocessing telemetry.
#[derive(Debug, Clone, Default)]
pub(crate) struct SymmetryStats {
    pub(crate) runs: u64,
    pub(crate) candidate_pairs: u64,
    pub(crate) pairs_detected: u64,
    pub(crate) sb_clauses_added: u64,
    pub(crate) last_skipped_reason: Option<SymmetrySkipReason>,
}

impl SymmetryStats {
    pub(crate) fn begin_run(&mut self) {
        self.runs = self.runs.saturating_add(1);
        self.last_skipped_reason = None;
    }

    pub(crate) fn skip(&mut self, reason: SymmetrySkipReason) {
        self.last_skipped_reason = Some(reason);
    }
}
