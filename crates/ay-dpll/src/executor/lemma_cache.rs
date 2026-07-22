// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory lemma cache for incremental solving with persistence across push/pop.
//!
//! In binary path analysis, the same program is analyzed path-by-path. Each path
//! shares most constraints but differs in branch conditions. AY supports
//! incremental push/pop, but theory lemmas learned during one path are normally
//! discarded on pop. The `LemmaCache` stores theory lemmas independently of the
//! current scope level, enabling replay of persistent lemmas into the SAT solver
//! for subsequent paths.
//!
//! Each lemma is tagged with the assertion-scope level at which it was derived.
//! Lemmas derived from assertions at level <= L persist through pop to level >= L.
//! On push, persistent lemmas are replayed into the SAT solver for the new path.
//!
//! This feature is opt-in via `Solver::set_lemma_persistence(true)` and is off
//! by default to avoid overhead for non-incremental workloads.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{TheoryLemma, TheoryLit};

/// Maximum number of entries before the cache evicts older lemmas (#8623).
/// When exceeded, the older half is drained and the dedup set is rebuilt.
const MAX_ENTRIES: usize = 100_000;

/// Cache of theory lemmas that persist across push/pop scope transitions.
///
/// Lemmas are tagged with their derivation scope level. On pop to level L,
/// lemmas derived at scope > L are discarded. The remaining lemmas are
/// available for replay into a fresh SAT solver on the next check-sat.
///
/// The cache is bounded to [`MAX_ENTRIES`] to prevent unbounded memory growth
/// in long-running incremental solving sessions (#8623).
pub(crate) struct LemmaCache {
    /// Stored lemmas with their derivation scope level.
    lemmas: Vec<(TheoryLemma, usize)>,
    /// Deduplication set keyed on sorted clause literals.
    dedup: HashSet<Vec<TheoryLit>>,
}

impl LemmaCache {
    /// Create an empty lemma cache.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            lemmas: Vec::new(),
            dedup: HashSet::default(),
        }
    }

    /// Record a theory lemma at the given scope level.
    ///
    /// Duplicate lemmas (same clause literals regardless of order) are silently
    /// ignored. Returns `true` if the lemma was newly inserted.
    pub(crate) fn record_lemma(&mut self, lemma: TheoryLemma, scope_level: usize) -> bool {
        let mut key: Vec<TheoryLit> = lemma.clause.clone();
        key.sort();
        if !self.dedup.insert(key) {
            return false;
        }
        self.lemmas.push((lemma, scope_level));

        // Evict older half when the cache exceeds the size cap (#8623).
        if self.lemmas.len() > MAX_ENTRIES {
            let keep_from = self.lemmas.len() / 2;
            self.lemmas.drain(..keep_from);
            // Rebuild the dedup set from retained lemmas.
            self.dedup.clear();
            for (lemma, _) in &self.lemmas {
                let mut k: Vec<TheoryLit> = lemma.clause.clone();
                k.sort();
                self.dedup.insert(k);
            }
        }

        true
    }

    /// Remove all lemmas derived at scope levels strictly greater than `level`.
    ///
    /// This is called on pop to discard lemmas that depended on assertions
    /// from the popped scope. Lemmas at scope <= `level` are retained.
    pub(crate) fn pop_to_level(&mut self, level: usize) {
        self.lemmas.retain(|(_, scope)| *scope <= level);
        // Rebuild dedup set from retained lemmas.
        self.dedup.clear();
        for (lemma, _) in &self.lemmas {
            let mut key: Vec<TheoryLit> = lemma.clause.clone();
            key.sort();
            self.dedup.insert(key);
        }
    }

    /// Iterate over lemmas that are valid at the given scope level.
    ///
    /// A lemma is valid if its derivation scope is <= `current_level`.
    #[allow(dead_code)]
    pub(crate) fn persistent_lemmas(
        &self,
        current_level: usize,
    ) -> impl Iterator<Item = &TheoryLemma> {
        self.lemmas
            .iter()
            .filter(move |(_, scope)| *scope <= current_level)
            .map(|(lemma, _)| lemma)
    }

    /// Return all cached lemmas for replay into a SAT solver.
    pub(crate) fn replay_lemmas(&self) -> &[(TheoryLemma, usize)] {
        &self.lemmas
    }

    /// Number of cached lemmas.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.lemmas.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.lemmas.is_empty()
    }

    /// Clear all cached lemmas.
    pub(crate) fn clear(&mut self) {
        self.lemmas.clear();
        self.dedup.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{TermId, TheoryLemma, TheoryLit};

    fn make_lit(idx: u32, value: bool) -> TheoryLit {
        TheoryLit::new(TermId::new(idx), value)
    }

    fn make_lemma(lits: &[(u32, bool)]) -> TheoryLemma {
        TheoryLemma::new(lits.iter().map(|&(idx, val)| make_lit(idx, val)).collect())
    }

    #[test]
    fn test_lemma_cache_record_and_len() {
        let mut cache = LemmaCache::new();
        assert!(cache.is_empty());

        let lemma = make_lemma(&[(1, true), (2, false)]);
        assert!(cache.record_lemma(lemma, 0));
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_lemma_cache_dedup() {
        let mut cache = LemmaCache::new();
        let lemma1 = make_lemma(&[(1, true), (2, false)]);
        let lemma2 = make_lemma(&[(2, false), (1, true)]); // same clause, different order

        assert!(cache.record_lemma(lemma1, 0));
        assert!(!cache.record_lemma(lemma2, 0)); // should be deduplicated
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_lemma_cache_pop_to_level() {
        let mut cache = LemmaCache::new();

        // Global lemma at scope 0
        cache.record_lemma(make_lemma(&[(1, true)]), 0);
        // Scoped lemma at scope 1
        cache.record_lemma(make_lemma(&[(2, true)]), 1);
        // Scoped lemma at scope 2
        cache.record_lemma(make_lemma(&[(3, true)]), 2);

        assert_eq!(cache.len(), 3);

        // Pop to level 1: discard scope 2 lemma
        cache.pop_to_level(1);
        assert_eq!(cache.len(), 2);

        // Pop to level 0: discard scope 1 lemma
        cache.pop_to_level(0);
        assert_eq!(cache.len(), 1);

        // The global lemma survives
        let remaining: Vec<_> = cache.persistent_lemmas(0).collect();
        assert_eq!(remaining.len(), 1);
        assert_eq!(remaining[0].clause[0].term, TermId::new(1));
    }

    #[test]
    fn test_lemma_cache_persistent_lemmas_filter() {
        let mut cache = LemmaCache::new();
        cache.record_lemma(make_lemma(&[(1, true)]), 0);
        cache.record_lemma(make_lemma(&[(2, true)]), 1);
        cache.record_lemma(make_lemma(&[(3, true)]), 2);

        // At level 1, only scope 0 and scope 1 lemmas are valid
        let valid: Vec<_> = cache.persistent_lemmas(1).collect();
        assert_eq!(valid.len(), 2);
    }

    #[test]
    fn test_lemma_cache_replay_lemmas() {
        let mut cache = LemmaCache::new();
        cache.record_lemma(make_lemma(&[(1, true)]), 0);
        cache.record_lemma(make_lemma(&[(2, false)]), 1);

        let all = cache.replay_lemmas();
        assert_eq!(all.len(), 2);
        assert_eq!(all[0].1, 0); // scope 0
        assert_eq!(all[1].1, 1); // scope 1
    }

    #[test]
    fn test_lemma_cache_clear() {
        let mut cache = LemmaCache::new();
        cache.record_lemma(make_lemma(&[(1, true)]), 0);
        cache.record_lemma(make_lemma(&[(2, true)]), 1);

        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_lemma_cache_dedup_after_pop() {
        let mut cache = LemmaCache::new();
        let lemma = make_lemma(&[(5, true), (6, false)]);

        // Record at scope 1
        assert!(cache.record_lemma(lemma.clone(), 1));
        assert_eq!(cache.len(), 1);

        // Pop discards it
        cache.pop_to_level(0);
        assert!(cache.is_empty());

        // Re-record at scope 0 should succeed (dedup set was rebuilt)
        assert!(cache.record_lemma(lemma, 0));
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_lemma_cache_eviction_on_overflow() {
        let mut cache = LemmaCache::new();

        // Insert MAX_ENTRIES + 1 unique lemmas to trigger eviction.
        for i in 0..=(MAX_ENTRIES as u32) {
            let lemma = make_lemma(&[(i, true)]);
            cache.record_lemma(lemma, 0);
        }

        // After exceeding MAX_ENTRIES, the older half should be evicted.
        assert!(
            cache.len() <= MAX_ENTRIES,
            "cache should be bounded after eviction: got {}, max {}",
            cache.len(),
            MAX_ENTRIES,
        );
        // The newer half should survive.
        assert!(
            cache.len() > MAX_ENTRIES / 2,
            "cache should retain the newer half: got {}",
            cache.len(),
        );
    }

    #[test]
    fn test_lemma_cache_dedup_works_after_eviction() {
        let mut cache = LemmaCache::new();

        // Fill to trigger eviction.
        for i in 0..=(MAX_ENTRIES as u32) {
            cache.record_lemma(make_lemma(&[(i, true)]), 0);
        }

        let post_eviction_len = cache.len();

        // Try to insert a lemma that should still be in the cache
        // (high index = newer = survived eviction).
        let recent_lemma = make_lemma(&[(MAX_ENTRIES as u32, true)]);
        let inserted = cache.record_lemma(recent_lemma, 0);
        assert!(!inserted, "recent lemma should be deduplicated");
        assert_eq!(cache.len(), post_eviction_len);
    }
}
