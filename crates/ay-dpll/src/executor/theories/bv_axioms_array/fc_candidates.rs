// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded storage for the existing eager functional-consistency priority order.
//!
//! Relevant candidates arrive in source pair order within each category after
//! the caller excludes authenticated, distinct literal-index pairs. Only a prefix
//! of each category can survive the per-array and remaining global allowances,
//! so retaining later entries cannot affect the emitted prefix. Full counts are
//! kept separately for the existing diagnostics. This does not bound the scan's
//! CPU work: a caller enumerating all pairs still performs quadratic work.

/// Finite-domain symbolic/constant pairs precede the two ordinary categories.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Category {
    Finite,
    SameBase,
    CrossBase,
}

/// Counts before either the category or global allowance is applied.
///
/// Wide counters preserve diagnostic totals even when the pair count exceeds
/// `usize` on a narrow target; candidate storage is still bounded by `usize`
/// allowances. AY's source pairs are drawn from `u32` term identifiers.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Counts {
    pub(crate) finite: u128,
    pub(crate) same_base: u128,
    pub(crate) cross_base: u128,
}

/// Retain at most `global + min(same, global) + min(cross, global)` entries.
///
/// The bound describes retained elements, not an exact allocator byte charge.
/// Vectors grow only as candidates arrive; a large configured allowance does
/// not itself allocate its capacity. No vector or set holds discarded pairs.
pub(crate) struct CandidatePrefixes<T> {
    finite: Vec<T>,
    same_base: Vec<T>,
    cross_base: Vec<T>,
    counts: Counts,
    same_allowance: usize,
    cross_allowance: usize,
    global_allowance: usize,
}

impl<T> CandidatePrefixes<T> {
    pub(crate) fn new(same: usize, cross: usize, global: usize) -> Self {
        Self {
            finite: Vec::new(),
            same_base: Vec::new(),
            cross_base: Vec::new(),
            counts: Counts::default(),
            same_allowance: same,
            cross_allowance: cross,
            global_allowance: global,
        }
    }

    /// Observe each relevant candidate once, before post-budget pruning.
    pub(crate) fn observe(&mut self, category: Category, candidate: T) {
        let (prefix, count, allowance) = match category {
            Category::Finite => (
                &mut self.finite,
                &mut self.counts.finite,
                self.global_allowance,
            ),
            Category::SameBase => (
                &mut self.same_base,
                &mut self.counts.same_base,
                self.same_allowance.min(self.global_allowance),
            ),
            Category::CrossBase => (
                &mut self.cross_base,
                &mut self.counts.cross_base,
                self.cross_allowance.min(self.global_allowance),
            ),
        };
        *count += 1;
        if prefix.len() < allowance {
            prefix.push(candidate);
        }
    }

    pub(crate) fn counts(&self) -> Counts {
        self.counts
    }

    /// Number of same-base entries the old per-array slice would contain.
    pub(crate) fn same_base_limit(&self) -> u128 {
        self.counts.same_base.min(self.same_allowance as u128)
    }

    /// The exact finite → same-base → cross-base prefix of admitted candidates.
    ///
    /// This deliberately does not prune missing bits or encoded/normalized
    /// distinctness: those remaining candidates still consume global allowance
    /// before being rejected. Literal-only exclusion belongs to the caller.
    pub(crate) fn selected(&self) -> impl Iterator<Item = &T> {
        self.finite
            .iter()
            .chain(self.same_base.iter())
            .chain(self.cross_base.iter())
            .take(self.global_allowance)
    }

    /// Eligible candidates omitted by the global cap, not by category caps.
    pub(crate) fn global_skipped(&self) -> u128 {
        let eligible = self.counts.finite
            + self.same_base_limit()
            + self.counts.cross_base.min(self.cross_allowance as u128);
        eligible.saturating_sub(self.global_allowance as u128)
    }
}

#[cfg(test)]
mod tests;
