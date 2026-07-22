// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CEGAR state preservation cache.
//!
//! Caches feasibility (SAT/UNSAT) results and implication check results
//! across CEGAR ARG restarts. Without this cache, every `restart_arg()` call
//! forces re-checking all expansion constraints from scratch — O(states × clauses)
//! redundant SMT queries per refinement iteration.
//!
//! ## Cache Invalidation
//!
//! - **Feasibility cache**: Keyed on the full expansion constraint (clause body
//!   constraint + predicate substitutions). Entries remain valid across ARG
//!   restarts because clause constraints don't change. When new predicates are
//!   added, the expansion constraints that include those predicates will have
//!   different keys, so stale entries are never hit.
//!
//! - **Implication cache**: Keyed on (assumptions, conclusion) pairs. Cleared
//!   when new predicates are added, because new predicates change the abstract
//!   state computation and may alter implication results for the same assumptions.
//!
//! ## Bounded Growth
//!
//! Both caches have a maximum entry cap to prevent unbounded memory growth on
//! hard problems with many refinement iterations. When the cap is hit, the cache
//! is cleared entirely (cheaper than LRU eviction for a hash map).

use crate::ChcExpr;
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Maximum number of entries per cache before eviction.
const MAX_CACHE_ENTRIES: usize = 10_000;

/// Cached satisfiability result for a constraint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CachedFeasibility {
    Sat,
    Unsat,
    Unknown,
}

/// Statistics for cache hit/miss tracking.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct CacheStats {
    pub(super) feasibility_hits: u64,
    pub(super) feasibility_misses: u64,
    pub(super) implication_hits: u64,
    pub(super) implication_misses: u64,
}

/// CEGAR state preservation cache.
///
/// Survives `restart_arg()` to avoid redundant SMT queries across
/// CEGAR refinement iterations.
pub(super) struct CegarCache {
    /// Feasibility (SAT/UNSAT) results keyed by constraint formula.
    feasibility: FxHashMap<ChcExpr, CachedFeasibility>,

    /// Implication check results keyed by (assumptions, conclusion).
    implication: FxHashMap<(ChcExpr, ChcExpr), bool>,

    /// Hit/miss statistics.
    stats: CacheStats,
}

impl CegarCache {
    /// Create a new empty cache.
    pub(super) fn new() -> Self {
        Self {
            feasibility: FxHashMap::default(),
            implication: FxHashMap::default(),
            stats: CacheStats::default(),
        }
    }

    /// Look up a feasibility result in the cache.
    pub(super) fn check_feasibility(&mut self, constraint: &ChcExpr) -> Option<CachedFeasibility> {
        match self.feasibility.get(constraint) {
            Some(&result) => {
                self.stats.feasibility_hits += 1;
                Some(result)
            }
            None => {
                self.stats.feasibility_misses += 1;
                None
            }
        }
    }

    /// Store a feasibility result in the cache.
    pub(super) fn store_feasibility(&mut self, constraint: ChcExpr, result: CachedFeasibility) {
        if self.feasibility.len() >= MAX_CACHE_ENTRIES {
            self.feasibility.clear();
        }
        self.feasibility.insert(constraint, result);
    }

    /// Look up an implication result in the cache.
    pub(super) fn check_implication(
        &mut self,
        assumptions: &ChcExpr,
        conclusion: &ChcExpr,
    ) -> Option<bool> {
        let key = (assumptions.clone(), conclusion.clone());
        match self.implication.get(&key) {
            Some(&result) => {
                self.stats.implication_hits += 1;
                Some(result)
            }
            None => {
                self.stats.implication_misses += 1;
                None
            }
        }
    }

    /// Store an implication result in the cache.
    pub(super) fn store_implication(
        &mut self,
        assumptions: ChcExpr,
        conclusion: ChcExpr,
        result: bool,
    ) {
        if self.implication.len() >= MAX_CACHE_ENTRIES {
            self.implication.clear();
        }
        self.implication.insert((assumptions, conclusion), result);
    }

    /// Invalidate the implication cache (called when predicates change).
    ///
    /// The feasibility cache is NOT cleared because expansion constraint
    /// formulas that include new predicates will have different keys.
    pub(super) fn invalidate_implications(&mut self) {
        self.implication.clear();
    }

    /// Return current cache statistics.
    pub(super) fn stats(&self) -> CacheStats {
        self.stats
    }

    /// Return the total number of cached entries.
    #[cfg(test)]
    #[allow(dead_code)]
    pub(super) fn total_entries(&self) -> usize {
        self.feasibility.len() + self.implication.len()
    }
}

impl Default for CegarCache {
    fn default() -> Self {
        Self::new()
    }
}
