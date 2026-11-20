// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked Boolean projections of one immutable native query.

use ay_core::term::TermStoreSnapshotStamp;
use ay_frontend::SourceContextStamp;

use crate::api::{SolverCacheToken, UnsatProofArtifact};
use crate::UnknownReason;

use super::Term;

/// Why a projected enumeration ended. A value of this enum alone is not proof
/// authority; only AY constructs a [`BoolEnumerationReport`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum BoolEnumerationOutcome {
    /// One independent strict source refutation proved that no projection
    /// remains after the returned, independently checked rows were blocked.
    Exhaustive,
    /// Another candidate exists, but the requested number of rows was reached.
    Capped,
    /// Search, original-model validation or strict source certification stopped
    /// or declined. The returned rows remain checked witnesses; completeness
    /// has not been established.
    Incomplete(UnknownReason),
}

/// Candidate SAT search work. These counters exclude compilation, independent
/// original-model evaluation and the final source proof. They are diagnostic
/// work counts, not a complete CPU or allocation meter.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct BoolEnumerationSearchWork {
    /// SAT conflicts.
    pub conflicts: u64,
    /// SAT decisions.
    pub decisions: u64,
    /// SAT propagations.
    pub propagations: u64,
}

/// One projection, independently evaluated in a complete original Bool-leaf
/// witness. The order is the report's [`projection`](BoolEnumerationReport::projection).
#[derive(Debug, Clone)]
pub struct BoolEnumerationRow {
    pub(crate) values: Vec<bool>,
    pub(crate) witness: Vec<(Term, bool)>,
    pub(crate) search: BoolEnumerationSearchWork,
    pub(crate) validation_work: u64,
    pub(crate) materialization_work: u64,
}

impl BoolEnumerationRow {
    /// Values in the caller's requested projection order.
    #[must_use]
    pub fn values(&self) -> &[bool] {
        &self.values
    }

    /// Complete Bool-leaf assignment used to confirm the original assertions.
    /// These handles belong to the report's immutable source query.
    #[must_use]
    pub fn witness(&self) -> &[(Term, bool)] {
        &self.witness
    }

    /// Work of the candidate solve that produced this row.
    #[must_use]
    pub fn search_work(&self) -> BoolEnumerationSearchWork {
        self.search
    }

    /// Logical work admitted while constructing this witness and independently
    /// evaluating original roots and projections. Historical blockers are absent.
    /// This is not a complete arbitrary-precision arithmetic/CPU meter.
    #[must_use]
    pub fn original_validation_work(&self) -> u64 {
        self.validation_work
    }

    /// Logical work admitted to materialize this untrusted SAT assignment.
    /// The candidate producer performs no growing-CNF model-verdict scan.
    #[must_use]
    pub fn candidate_materialization_work(&self) -> u64 {
        self.materialization_work
    }
}

/// Work split at the persistent circuit/source proof boundary.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct BoolEnumerationStatistics {
    /// Exact finite-integer compilation work-unit schema.
    pub compilation_work_version: u32,
    /// Exact common signed width selected for finite integer compilation.
    pub signed_integer_width: u32,
    /// Logical preparation/evaluation/copy debits. This is not a fully counted
    /// native SMT endpoint and these are not a whole-operation work metric.
    pub admitted_work: u64,
    /// Cumulative logical storage debits, not live RSS.
    pub admitted_storage: usize,
    /// Number of persistent candidate SAT calls (including a terminal probe).
    pub candidate_solve_calls: u64,
    /// Total persistent candidate search work.
    pub candidate_search: BoolEnumerationSearchWork,
    /// Logical assignment materialization work of the candidate DATA producer.
    pub candidate_materialization_work: u64,
    /// Logical work admitted by witness construction and original-model/projection
    /// evaluations, including the extra candidate used to distinguish a reached
    /// cap from exhaustion.
    pub original_validation_work: u64,
    /// Logical work debited while copying the original-sort source query and
    /// adding its projection blockers. This partial meter excludes search.
    pub source_construction_work: u64,
    /// Time spent constructing that separate source query and its blockers.
    pub source_construction_micros: u64,
    /// Explicit final original-query check-sat calls: zero or one. The checked
    /// native proof funnel may perform its own internal certification probes.
    pub final_source_solve_calls: u64,
    /// Native source executor's reported work, internal solves included.
    pub final_source_work: u64,
    /// Time spent in the terminal original-query solve and strict proof export.
    pub final_source_micros: u64,
}

/// Checked projections of one frozen query. The caller's assertions, scopes,
/// declarations, last decision, model and proof are preserved.
///
/// An exhaustive report's proof concerns the composite query consisting of
/// the original assertions and one source projection blocker per returned row.
/// It never asserts that the caller's original query was UNSAT. The candidate
/// circuit's UNSAT result carries no completeness authority.
#[derive(Debug)]
#[must_use]
pub struct BoolEnumerationReport {
    pub(crate) common: EnumerationCommon,
    pub(crate) rows: Vec<BoolEnumerationRow>,
}

#[derive(Debug)]
pub(crate) struct EnumerationCommon {
    pub(crate) outcome: BoolEnumerationOutcome,
    pub(crate) projection: Vec<Term>,
    pub(crate) statistics: BoolEnumerationStatistics,
    pub(crate) completeness_proof: Option<UnsatProofArtifact>,
    pub(crate) diagnostic: Option<String>,
    pub(crate) solver: SolverCacheToken,
    pub(crate) source_context: SourceContextStamp,
    pub(crate) terms: TermStoreSnapshotStamp,
    pub(crate) assertions: Vec<Term>,
}

impl BoolEnumerationReport {
    /// Terminal outcome. Only `Exhaustive` establishes completeness.
    #[must_use]
    pub fn outcome(&self) -> BoolEnumerationOutcome {
        self.common.outcome
    }

    /// Authenticated source handles in the requested order.
    #[must_use]
    pub fn projection(&self) -> &[Term] {
        &self.common.projection
    }

    /// Distinct, independently checked projection rows.
    #[must_use]
    pub fn rows(&self) -> &[BoolEnumerationRow] {
        &self.rows
    }

    /// Compilation/search/terminal-proof work split.
    #[must_use]
    pub fn statistics(&self) -> BoolEnumerationStatistics {
        self.common.statistics
    }

    /// Strictly accepted native proof IR of the composite original query and blockers,
    /// present only for `Exhaustive`. This is a separate query from the caller's
    /// last decision. External Alethe limitations remain disclosed by the
    /// artifact; this getter implies no portable-checker acceptance.
    #[must_use]
    pub fn completeness_proof(&self) -> Option<&UnsatProofArtifact> {
        self.common.completeness_proof.as_ref()
    }

    /// Detail for a declined model/source proof or internal translation check.
    #[must_use]
    pub fn diagnostic(&self) -> Option<&str> {
        self.common.diagnostic.as_deref()
    }
}
