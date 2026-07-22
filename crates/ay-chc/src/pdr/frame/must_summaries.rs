// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Maximum number of must-summary entries per (level, predicate) before
/// oldest-first eviction.
///
/// MustSummaries grow with `level * predicates * reachable_states`. Without a
/// cap, long-running CHC solves on hard benchmarks accumulate unbounded
/// formula expressions. 1,000 per predicate is generous enough for normal
/// problems.
const MAX_MUST_SUMMARIES_PER_PREDICATE: usize = 1_000;

/// Global cap on total must-summary entries across all levels and predicates.
///
/// Even with per-predicate caps of 1,000, total can reach `levels * predicates * 1,000`.
/// For 50 levels and 10 predicates, that's 500K entries. This global cap prevents
/// pathological growth in multi-predicate problems with deep frame stacks.
const MAX_GLOBAL_MUST_SUMMARIES: usize = 50_000;

/// Entry in MustSummaries tracking provenance.
///
/// Backed entries have a `ReachFactId` proving reachability (complete witness chain).
/// Filter-only entries are heuristic seeds (e.g., loop-closure enrichment) that lack proof.
#[derive(Debug, Clone)]
pub(crate) struct MustSummaryEntry {
    pub(crate) formula: ChcExpr,
    /// Some = backed by a ReachFact (proven reachable); None = filter/seed only
    pub(crate) backing: Option<ReachFactId>,
}

/// Collection of must summaries per predicate per level.
///
/// Stores two categories of entries:
/// - **Backed**: proven reachable states with a corresponding `ReachFact` / witness chain
/// - **Unbacked**: heuristic seeds (e.g., loop-closure enrichment) without proof
///
/// Proof-critical consumers should use `get_backed()` or `get_all_levels_backed()`
/// to avoid relying on heuristic seeds.
#[derive(Debug, Clone, Default)]
pub(crate) struct MustSummaries {
    /// level -> predicate -> list of must-summary entries
    summaries: FxHashMap<usize, FxHashMap<PredicateId, Vec<MustSummaryEntry>>>,
}

impl MustSummaries {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Debug-only must-summary consistency check (#4757).
    ///
    /// Verifies:
    /// 1. No `Bool(false)` entries exist (filtered at add time)
    /// 2. If `Bool(true)` exists for a (level, pred), it is the sole entry
    /// 3. No duplicate formulas within any (level, pred) group
    fn debug_assert_must_summary_invariants(&self) {
        for (level, level_map) in &self.summaries {
            for (pred, entries) in level_map {
                // (1) No false entries
                debug_assert!(
                    entries.iter().all(|e| e.formula != ChcExpr::Bool(false)),
                    "BUG: MustSummaries has Bool(false) entry at level={level}, pred={pred:?}",
                );

                // (2) If true exists, it must be the sole entry
                let has_true = entries.iter().any(|e| e.formula == ChcExpr::Bool(true));
                if has_true {
                    let extra = entries.len() - 1;
                    debug_assert_eq!(
                        entries.len(),
                        1,
                        "BUG: MustSummaries has Bool(true) with {extra} other entries at level={level}, pred={pred:?}",
                    );
                }

                // (3) No duplicate formulas (O(n^2) but entries per (level, pred) are small)
                for i in 0..entries.len() {
                    for j in (i + 1)..entries.len() {
                        debug_assert!(
                            entries[i].formula != entries[j].formula,
                            "BUG: Duplicate formula in MustSummaries at level={level}, pred={pred:?}, indices {i} and {j}",
                        );
                    }
                }
            }
        }
    }

    /// Add a must summary with explicit backing.
    ///
    /// - `backing = Some(id)` -> backed entry with proof of reachability
    /// - `backing = None` -> filter-only / heuristic seed
    ///
    /// Deduplication:
    /// - If identical formula exists as unbacked and we add a backed entry, upgrade to backed.
    /// - If identical formula exists as backed, ignore unbacked re-adds.
    fn add_internal(
        &mut self,
        level: usize,
        pred: PredicateId,
        formula: ChcExpr,
        backing: Option<ReachFactId>,
    ) -> bool {
        // Skip trivially false formulas (they contribute nothing to the disjunction)
        if formula == ChcExpr::Bool(false) {
            return false;
        }

        let entries = self
            .summaries
            .entry(level)
            .or_default()
            .entry(pred)
            .or_default();

        // If new formula is true, it subsumes everything - replace with just true (backed)
        if formula == ChcExpr::Bool(true) {
            if entries.len() == 1 && entries[0].formula == ChcExpr::Bool(true) {
                // Upgrade backing if needed
                if backing.is_some() && entries[0].backing.is_none() {
                    entries[0].backing = backing;
                    return true;
                }
                return false;
            }
            entries.clear();
            entries.push(MustSummaryEntry { formula, backing });
            return true;
        }

        // If we already have true, the new formula is subsumed - skip it
        if entries.iter().any(|e| e.formula == ChcExpr::Bool(true)) {
            return false;
        }

        // Deduplicate: check if this exact formula already exists
        if let Some(existing) = entries.iter_mut().find(|e| e.formula == formula) {
            // Formula exists - check for backing upgrade
            if backing.is_some() && existing.backing.is_none() {
                existing.backing = backing;
                return true; // Upgraded to backed
            }
            return false; // Already exists (same or better backing)
        }

        // Evict oldest entries if at capacity to prevent unbounded memory growth.
        while entries.len() >= MAX_MUST_SUMMARIES_PER_PREDICATE {
            entries.remove(0);
        }

        entries.push(MustSummaryEntry { formula, backing });
        true
    }

    /// Add a backed must summary (proven reachable with witness chain).
    pub(crate) fn add_backed(
        &mut self,
        level: usize,
        pred: PredicateId,
        formula: ChcExpr,
        reach_fact_id: ReachFactId,
    ) -> bool {
        let result = self.add_internal(level, pred, formula, Some(reach_fact_id));
        self.debug_assert_must_summary_invariants();
        result
    }

    /// Add a filter-only must summary (heuristic seed, no proof).
    pub(crate) fn add_filter_only(
        &mut self,
        level: usize,
        pred: PredicateId,
        formula: ChcExpr,
    ) -> bool {
        let result = self.add_internal(level, pred, formula, None);
        self.debug_assert_must_summary_invariants();
        result
    }

    /// Add a must summary: predicate P is definitely reachable at level with given formula.
    /// Performs deduplication and basic simplification to prevent formula explosion.
    ///
    /// **Backwards-compatible** - adds as filter-only (unbacked).
    /// Prefer `add_backed()` or `add_filter_only()` for explicit provenance.
    ///
    /// Note: Only used in tests - production code uses `add_backed()` or `add_filter_only()`.
    #[cfg(any(test, kani))]
    pub(crate) fn add(&mut self, level: usize, pred: PredicateId, formula: ChcExpr) -> bool {
        self.add_filter_only(level, pred, formula)
    }

    /// Get disjunction of all must-reachable states for a predicate at a level.
    /// Includes both backed and unbacked entries.
    pub(crate) fn get(&self, level: usize, pred: PredicateId) -> Option<ChcExpr> {
        let level_map = self.summaries.get(&level)?;
        let entries = level_map.get(&pred)?;
        if entries.is_empty() {
            return None;
        }
        Some(
            entries
                .iter()
                .map(|e| e.formula.clone())
                .reduce(ChcExpr::or)
                .expect("non-empty after is_empty check"),
        )
    }

    /// Get disjunction of only **backed** must-reachable states for a predicate at a level.
    /// Use this for proof-critical consumers that need proven reachability.
    pub(crate) fn get_backed(&self, level: usize, pred: PredicateId) -> Option<ChcExpr> {
        let level_map = self.summaries.get(&level)?;
        let entries = level_map.get(&pred)?;
        let backed: Vec<_> = entries
            .iter()
            .filter(|e| e.backing.is_some())
            .map(|e| e.formula.clone())
            .collect();
        if backed.is_empty() {
            return None;
        }
        Some(
            backed
                .into_iter()
                .reduce(ChcExpr::or)
                .expect("non-empty after is_empty check"),
        )
    }

    /// Get the raw list of must-summary formulas for a predicate at a level.
    /// Returns formulas from both backed and unbacked entries.
    pub(crate) fn get_formulas(&self, level: usize, pred: PredicateId) -> Option<Vec<ChcExpr>> {
        let level_map = self.summaries.get(&level)?;
        let entries = level_map.get(&pred)?;
        Some(entries.iter().map(|e| e.formula.clone()).collect())
    }

    /// Get the raw list of must-summary entries for a predicate at a level.
    /// Allows callers to inspect backing status.
    ///
    /// Note: Only used in tests for verifying backing behavior.
    #[cfg(test)]
    pub(crate) fn get_entries(
        &self,
        level: usize,
        pred: PredicateId,
    ) -> Option<&[MustSummaryEntry]> {
        let level_map = self.summaries.get(&level)?;
        let entries = level_map.get(&pred)?;
        Some(entries.as_slice())
    }

    /// True if there exists any must-summary entry at `level`, across all predicates.
    pub(crate) fn has_any_at_level(&self, level: usize) -> bool {
        self.summaries
            .get(&level)
            .is_some_and(|level_map| level_map.values().any(|v| !v.is_empty()))
    }

    /// Total number of must-summary entries across all levels and predicates.
    pub(crate) fn entry_count(&self) -> usize {
        self.summaries
            .values()
            .map(|level_map| level_map.values().map(Vec::len).sum::<usize>())
            .sum()
    }

    /// Get disjunction of must-reachable states for a predicate across ALL levels.
    /// Includes both backed and unbacked entries.
    /// Used by hyperedge UNSAFE detection to check if any reachable states satisfy query.
    /// #1518: Check all levels, not just level 0, to capture propagated must-summaries.
    pub(crate) fn get_all_levels(&self, pred: PredicateId) -> Option<ChcExpr> {
        let mut seen = FxHashSet::default();
        let mut all_formulas = Vec::new();

        // Sort levels for deterministic disjunction ordering (#3060)
        let mut sorted_levels: Vec<_> = self.summaries.iter().collect();
        sorted_levels.sort_unstable_by_key(|(level, _)| **level);
        for (_, level_map) in &sorted_levels {
            if let Some(entries) = level_map.get(&pred) {
                for e in entries {
                    if seen.insert(e.formula.structural_hash()) {
                        all_formulas.push(e.formula.clone());
                    }
                }
            }
        }

        if all_formulas.is_empty() {
            return None;
        }

        Some(
            all_formulas
                .into_iter()
                .reduce(ChcExpr::or)
                .expect("non-empty after is_empty check"),
        )
    }

    /// Evict oldest entries across all (level, predicate) groups until the total
    /// entry count is at or below `MAX_GLOBAL_MUST_SUMMARIES`.
    ///
    /// Eviction strategy: build a sorted list of (level, pred, count), then
    /// drain from the largest groups first (batch eviction for efficiency).
    /// Returns the number of entries evicted.
    pub(crate) fn gc_if_over_global_budget(&mut self) -> usize {
        let initial_total = self.entry_count();
        if initial_total <= MAX_GLOBAL_MUST_SUMMARIES {
            return 0;
        }
        let mut evicted = 0usize;

        // Loop until the global budget is satisfied or eviction cannot make
        // more progress. A single proportional pass can under-evict when
        // `share.max(1)` rounds down for many equal-size groups, so we iterate
        // the sweep until the total fits. Each outer pass walks every non-empty
        // group, so this bounds total work at O(n_groups * n_passes) — in
        // practice <= 3 passes for the shapes we've measured. (#8599)
        loop {
            let total = self.entry_count();
            if total <= MAX_GLOBAL_MUST_SUMMARIES {
                break;
            }
            let mut to_evict = total - MAX_GLOBAL_MUST_SUMMARIES;

            // Build sorted list of (level, pred, count), largest first.
            let mut groups: Vec<(usize, PredicateId, usize)> = Vec::new();
            for (&level, level_map) in &self.summaries {
                for (&pred, entries) in level_map {
                    if !entries.is_empty() {
                        groups.push((level, pred, entries.len()));
                    }
                }
            }
            if groups.is_empty() {
                break;
            }
            groups.sort_unstable_by_key(|group| std::cmp::Reverse(group.2));

            let mut pass_evicted = 0usize;
            // Evict from the largest groups first. Each group gives up
            // a proportional share, but at least 1.
            for (level, pred, group_len) in &groups {
                if to_evict == 0 {
                    break;
                }
                let share = (to_evict * group_len / total.max(1))
                    .max(1)
                    .min(to_evict)
                    .min(*group_len);
                if let Some(entries) = self.summaries.get_mut(level).and_then(|m| m.get_mut(pred)) {
                    let drain_n = share.min(entries.len());
                    entries.drain(..drain_n);
                    // Release excess capacity after bulk eviction (#8601).
                    entries.shrink_to_fit();
                    evicted += drain_n;
                    pass_evicted += drain_n;
                    to_evict = to_evict.saturating_sub(drain_n);
                }
            }

            // Forward-progress guard: if we couldn't evict anything this pass
            // stop so we don't spin.
            if pass_evicted == 0 {
                break;
            }
        }

        evicted
    }

    /// Get disjunction of only **backed** must-reachable states across ALL levels.
    /// Use this for proof-critical consumers (e.g., hyperedge UNSAFE detection).
    pub(crate) fn get_all_levels_backed(&self, pred: PredicateId) -> Option<ChcExpr> {
        let mut seen = FxHashSet::default();
        let mut backed_formulas = Vec::new();

        // Sort levels for deterministic disjunction ordering (#3060)
        let mut sorted_levels: Vec<_> = self.summaries.iter().collect();
        sorted_levels.sort_unstable_by_key(|(level, _)| **level);
        for (_, level_map) in &sorted_levels {
            if let Some(entries) = level_map.get(&pred) {
                for e in entries.iter().filter(|e| e.backing.is_some()) {
                    if seen.insert(e.formula.structural_hash()) {
                        backed_formulas.push(e.formula.clone());
                    }
                }
            }
        }

        if backed_formulas.is_empty() {
            return None;
        }

        Some(
            backed_formulas
                .into_iter()
                .reduce(ChcExpr::or)
                .expect("non-empty after is_empty check"),
        )
    }
}
