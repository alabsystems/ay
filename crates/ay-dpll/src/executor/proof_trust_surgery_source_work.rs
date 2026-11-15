// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query-local accounting for parsed-source proof work.

use ay_frontend::command::Term as FrontendTerm;

use super::limits::{surface_pass_work_as, SurfaceWorkModel, MAX_AGGREGATE_SOURCE_WORK};

/// The proof pipeline pass about to traverse, clone, or format source terms.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::executor) enum ProofSourcePass {
    /// The assembly gate's admission of generic proof reconstruction. Its
    /// own source work is ONE traversal — the stack clones and the node-by-
    /// node raw rebuilds the reconstruction lanes run — so it is priced as a
    /// [`SurfaceWorkModel::Traversal`]. Every per-subtree renderer that runs
    /// inside it (the override collectors, `raw_intern_surface`, the
    /// authored-assume restoration, each metered pass below) checks and
    /// charges its own per-subtree bound at its own site, so a root this pass
    /// admits is not thereby admitted to any of them.
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
    /// The fold-identity promoter's first stage, charged PER CANDIDATE ROOT:
    /// the root's clone, its `let` expansion and the scan of its conjuncts
    /// for a normalization identity or a complementary pair
    /// (`authored_fold_identity`). One traversal.
    AuthoredFoldIdentityScan,
    /// Its second stage, charged only once an argument exists: the raw
    /// re-intern, the override-aware render plus re-parse, and the render
    /// gate. Three traversals — with the scan, the same four the sibling
    /// `AuthoredConjunctEvalRebuild` charges, but never spent on a root the
    /// pass cannot act on.
    AuthoredFoldIdentityRebuild,
    InputSyntaxRewrite,
    InputSyntaxOverridePairs,
    InternalCertificateScope,
}

impl ProofSourcePass {
    /// What this pass does with each root.
    const fn model(self) -> SurfaceWorkModel {
        match self {
            Self::UnsatProofBuild => SurfaceWorkModel::Traversal,
            _ => SurfaceWorkModel::PerSubtree,
        }
    }

    fn passes(self) -> usize {
        match self {
            Self::OriginalAssertionRebuild => 3,
            Self::AuthoredConjunctEvalRebuild => 4,
            Self::AuthoredFoldIdentityRebuild => 3,
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
    /// Charge canonical DAG/name visits to the SAME query-local source-work
    /// envelope; callers precharge before walking. This is cooperative logical
    /// accounting, not a new allowance or a hard wall/RSS limit. Refusal never
    /// renews, resets or refunds work already consumed by the proof pipeline.
    pub(in crate::executor) fn spend_canonical_scan_work(&self, work: usize) -> bool {
        let Some(remaining) = self.remaining.get().checked_sub(work) else {
            return false;
        };
        self.remaining.set(remaining);
        true
    }
    pub(in crate::executor) fn reset(&mut self) {
        self.remaining.set(MAX_AGGREGATE_SOURCE_WORK);
    }

    #[cfg(test)]
    pub(in crate::executor) fn remaining_for_test(&self) -> usize {
        self.remaining.get()
    }

    /// What is left of the envelope. Diagnostic: the unbounded census records
    /// it beside a refused spend so a reader can see the charge against it.
    pub(in crate::executor) fn remaining(&self) -> usize {
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
        let Some(single_pass) = surface_pass_work_as(roots, pass.model()) else {
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
