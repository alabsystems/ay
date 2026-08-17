// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query-local accounting for parsed-source proof work.

use ay_frontend::command::Term as FrontendTerm;

use super::limits::{surface_pass_work, MAX_AGGREGATE_SOURCE_WORK};

/// The proof pipeline pass about to traverse, clone, or format source terms.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::executor) enum ProofSourcePass {
    UnsatProofBuild,
    /// Audit, deep clone, and re-elaboration.
    OriginalAssertionRebuild,
    /// FOUR source-scale traversals, not two: the deep clone, the raw re-intern,
    /// and the override-aware render plus full re-parse inside
    /// `rebuilt_root_prints_as_authored` — and the loop runs them over EVERY
    /// parsed root, not one. Charged as 2 it cost +5.6s at 400 roots that the
    /// envelope never authorized (measured; the ceiling itself still held, so
    /// this was a calibration miss, not an escape).
    AuthoredConjunctEvalRebuild,
    InputSyntaxRewrite,
    InputSyntaxOverridePairs,
    InternalCertificateScope,
}

impl ProofSourcePass {
    fn passes(self) -> usize {
        match self {
            Self::OriginalAssertionRebuild => 3,
            Self::AuthoredConjunctEvalRebuild => 4,
            _ => 1,
        }
    }
}

/// Aggregate source-work envelope for one query's proof pipeline.
#[derive(Debug)]
pub(in crate::executor) struct ProofSourceWorkEnvelope {
    remaining: std::cell::Cell<usize>,
}

impl Default for ProofSourceWorkEnvelope {
    fn default() -> Self {
        Self {
            remaining: std::cell::Cell::new(MAX_AGGREGATE_SOURCE_WORK),
        }
    }
}

impl ProofSourceWorkEnvelope {
    pub(in crate::executor) fn reset(&mut self) {
        self.remaining.set(MAX_AGGREGATE_SOURCE_WORK);
    }

    #[cfg(test)]
    pub(in crate::executor) fn remaining_for_test(&self) -> usize {
        self.remaining.get()
    }

    #[cfg(test)]
    pub(in crate::executor) fn set_remaining_for_test(&self, remaining: usize) {
        self.remaining.set(remaining);
    }

    /// Debit only work that is actually about to run. Any unbounded or
    /// unaffordable pass declines without mutating the envelope.
    pub(in crate::executor) fn spend<'a>(
        &self,
        pass: ProofSourcePass,
        roots: impl IntoIterator<Item = &'a FrontendTerm>,
    ) -> bool {
        let Some(single_pass) = surface_pass_work(roots) else {
            return false;
        };
        let charge = single_pass
            .checked_mul(pass.passes())
            .filter(|&charge| charge <= MAX_AGGREGATE_SOURCE_WORK);
        let Some(remaining) = charge.and_then(|charge| self.remaining.get().checked_sub(charge))
        else {
            return false;
        };
        self.remaining.set(remaining);
        true
    }
}
