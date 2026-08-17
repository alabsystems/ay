// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact, query-cumulative closure for recursively finite arrays.

use super::super::super::super::Executor;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, TermId};
use std::collections::VecDeque;

const FINITE_ARRAY_SCAN_RESOURCE_POLL_INTERVAL: usize = 1024;

mod discovery;
mod equality;
mod select;
mod telemetry;

#[cfg(test)]
mod tests;

/// Finite index domain of an array equality, over which exact
/// extensionality is expanded (`add_finite_index_array_closure`).
#[derive(Clone)]
enum FiniteArrayIndexDomain {
    /// BitVec index of the given width: the `2^width` concrete bit-vectors.
    BitVec(u32),
    /// Bool index: the two values `false` / `true`.
    Bool,
    /// All-nullary (enum) datatype index: the constructor constants, built
    /// with the given index sort. The inhabitants of an all-nullary datatype
    /// are exactly its constructor constants, so this enumerates the full
    /// (finite) index domain.
    EnumDatatype(Vec<String>, Sort),
}

impl FiniteArrayIndexDomain {
    fn cardinality(&self) -> usize {
        match self {
            Self::BitVec(width) => 1usize << width,
            Self::Bool => 2,
            Self::EnumDatatype(constructors, _) => constructors.len(),
        }
    }
}

type FiniteArrayCandidate = (TermId, TermId, TermId, FiniteArrayIndexDomain);

#[derive(Default)]
struct FiniteArrayCandidates {
    equalities: Vec<FiniteArrayCandidate>,
    selects: Vec<FiniteArrayCandidate>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FiniteArrayScanStatus {
    Complete,
    Truncated,
}

#[derive(Clone, Copy)]
enum FiniteArrayCandidateKind {
    Equality,
    Select,
}

/// Work performed by one exact finite-index array-extensionality scan.
///
/// Every emitted equality is complete over its whole index domain. A budget
/// may defer complete equality atoms, but it never emits a partial
/// biconditional: callers can therefore keep an UNSAT result from the sound
/// emitted prefix and must fail closed only if the relaxed solve reports SAT.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
#[must_use]
pub(in crate::executor) struct FiniteArrayExtensionalityReport {
    pub(in crate::executor) candidate_equalities: usize,
    pub(in crate::executor) candidate_index_points: usize,
    pub(in crate::executor) candidate_value_cells: usize,
    pub(in crate::executor) candidate_selects: usize,
    pub(in crate::executor) candidate_select_index_points: usize,
    pub(in crate::executor) candidate_select_value_cells: usize,
    pub(in crate::executor) emitted_equalities: usize,
    pub(in crate::executor) emitted_index_points: usize,
    pub(in crate::executor) emitted_value_cells: usize,
    pub(in crate::executor) emitted_selects: usize,
    pub(in crate::executor) emitted_select_index_points: usize,
    pub(in crate::executor) emitted_select_value_cells: usize,
    pub(in crate::executor) already_covered_equalities: usize,
    pub(in crate::executor) already_covered_selects: usize,
    pub(in crate::executor) budget_deferred_equalities: usize,
    pub(in crate::executor) budget_deferred_index_points: usize,
    pub(in crate::executor) budget_deferred_value_cells: usize,
    pub(in crate::executor) budget_deferred_selects: usize,
    pub(in crate::executor) budget_deferred_select_index_points: usize,
    pub(in crate::executor) budget_deferred_select_value_cells: usize,
    pub(in crate::executor) candidate_scan_truncated: usize,
}

impl FiniteArrayExtensionalityReport {
    #[cfg(test)]
    pub(in crate::executor) const fn is_complete(self) -> bool {
        self.budget_deferred_equalities == 0
            && self.budget_deferred_selects == 0
            && self.candidate_scan_truncated == 0
    }
}

impl Executor {
    /// Maximum candidates retained by either initial closure scan. The work
    /// allowance can admit at most this many candidates because every
    /// supported finite carrier has at least one point. One additional sentinel
    /// is collected to make truncation exact rather than heuristic.
    #[cfg(test)]
    pub(in crate::executor) const FINITE_ARRAY_CANDIDATE_SCAN_CAP: usize =
        crate::executor::FiniteArrayExpansionLedger::MAX_CANDIDATES;
    /// Maximum BitVec index width for which finite-domain array extensionality
    /// is expanded eagerly. Width `w` enumerates `2^w` indices; `w <= 8` keeps
    /// this at <= 256 select pairs per array equality, which the bit-blaster
    /// handles cheaply while making such equalities EXACTLY decided.
    const FINITE_BV_ARRAY_EXT_MAX_INDEX_WIDTH: u32 = 8;

    /// Eager, sound + COMPLETE finite-domain closure for array equalities and
    /// symbolic finite-index selects.
    ///
    /// For an array sort `(Array (_ BitVec w) E)` with `w` small, the index
    /// domain is finite (`2^w` values), so two arrays are equal iff they agree
    /// at every index. The lazy single-Skolem extensionality axiom used
    /// elsewhere can only *witness* a difference; it cannot *refute* an
    /// equality that secretly fails (or holds) at a specific concrete index,
    /// which left QF_ABV array equalities involving `(as const ...)` /
    /// store-chains under-constrained and produced wrong-SAT.
    ///
    /// This pass first emits whole-domain symbolic-select expansions, then
    /// asserts the exact biconditional for each such equality atom
    /// `(= a b)` reachable from the assertions:
    ///   `(= a b)  <=>  AND_{i in domain} (= (select a i) (select b i))`
    /// which the underlying solver then decides completely. Fires for BitVec
    /// index widths `<= FINITE_BV_ARRAY_EXT_MAX_INDEX_WIDTH` and for Bool
    /// indices (2 values, `false`/`true`); larger / infinite index domains are
    /// left to the lazy machinery (no soundness impact — it just stays as-is).
    /// Generated array-valued cell equalities are queued recursively, so nested
    /// finite arrays reach a true fixed point rather than relying on a second
    /// route pass. Every reservation comes from the query-cumulative ledger;
    /// internal retries cannot replenish it, and already-installed axioms cost
    /// nothing on later incremental checks.
    ///
    /// (Soundness fix: finite-index / as-const array (dis)equality wrong-SAT.)
    pub(in crate::executor) fn add_finite_index_array_closure(
        &mut self,
    ) -> FiniteArrayExtensionalityReport {
        self.add_finite_index_array_closure_with_roots(&[])
    }

    pub(in crate::executor) fn add_finite_index_array_closure_with_roots(
        &mut self,
        extra_roots: &[TermId],
    ) -> FiniteArrayExtensionalityReport {
        let mut report = FiniteArrayExtensionalityReport::default();
        let root_cap = crate::executor::FiniteArrayExpansionLedger::MAX_SCAN_NODES;
        let root_count = self.ctx.assertions.len().saturating_add(extra_roots.len());
        let roots: Vec<_> = self
            .ctx
            .assertions
            .iter()
            .chain(extra_roots)
            .take(root_cap)
            .copied()
            .collect();
        let mut candidates = FiniteArrayCandidates::default();
        let scan_status = self.collect_finite_array_candidates_bounded(&roots, &mut candidates, 0);
        if root_count > root_cap || scan_status == FiniteArrayScanStatus::Truncated {
            self.mark_finite_array_scan_truncated(&mut report);
        }
        let mut active_assertions: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut equality_candidates: VecDeque<_> = candidates.equalities.into();
        let mut processed_selects = HashSet::default();
        self.add_finite_index_select_expansion_bounded(
            candidates.selects,
            &mut equality_candidates,
            &mut processed_selects,
            &mut active_assertions,
            &mut report,
        );
        self.add_finite_index_array_extensionality_fixed_point(
            equality_candidates,
            &mut processed_selects,
            &mut active_assertions,
            &mut report,
        );
        self.record_finite_array_extensionality_report(report);
        report
    }

    #[cfg(test)]
    pub(in crate::executor) fn add_finite_index_array_extensionality_with_budget(
        &mut self,
        max_index_points: usize,
    ) -> FiniteArrayExtensionalityReport {
        self.finite_array_expansion.begin_external_query();
        self.finite_array_expansion.remaining_index_points = max_index_points;
        self.finite_array_expansion.remaining_value_cells = usize::MAX;
        self.add_finite_index_array_closure()
    }
}
