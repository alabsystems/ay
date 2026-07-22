// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Cross-engine lemma cache for sequential portfolio runs (#7919).
//!
//! When the portfolio runs engines sequentially, a PDR engine that returns
//! Unknown may have learned useful lemmas. `LemmaCache` accumulates these
//! lemmas across engine runs so that subsequent PDR engines start with
//! prior knowledge instead of rediscovering the same facts.
//!
//! Unlike [`SharedBlackboard`](crate::blackboard::SharedBlackboard) which
//! enables real-time lemma exchange between *parallel* engines, `LemmaCache`
//! is designed for *sequential* handoff: one engine finishes, its lemmas are
//! captured, and the next engine receives them at startup.
//!
//! # Architecture
//!
//! ```text
//! Engine 0 (PDR) -> Unknown + writes to LemmaCache
//! Engine 1 (BMC) -> Unknown (ignores cache, not a PDR engine)
//! Engine 2 (PDR) -> reads LemmaCache -> seeds lemma_hints -> Safe
//! ```
//!
//! The cache is injected into `PdrConfig::lemma_cache` by the portfolio
//! scheduler. PDR writes to it via `export_to_cache()` when returning
//! Unknown. The portfolio reads accumulated lemmas from the cache and
//! injects them as `PdrConfig::lemma_hints` into subsequent PDR engines.

use crate::lemma_pool::LemmaPool;
use std::sync::{Arc, Mutex};

/// Maximum number of lemmas before the cache evicts older entries (#8623).
/// When exceeded after a merge, the older half is drained to bound memory
/// growth in long-running sequential portfolio sessions.
const MAX_LEMMAS: usize = 50_000;

/// Thread-safe accumulator for learned lemmas across sequential engine runs.
///
/// Wraps an `Arc<Mutex<LemmaPool>>` so it can be shared between the
/// portfolio scheduler and PDR engine configs. PDR writes to the cache
/// when it finishes with Unknown; the portfolio reads from it before
/// launching subsequent engines.
///
/// The `Arc<Mutex<_>>` overhead is minimal: writes happen once per engine
/// exit, reads happen once per engine launch.
#[derive(Debug, Clone)]
pub(crate) struct LemmaCache {
    pool: Arc<Mutex<LemmaPool>>,
}

impl LemmaCache {
    /// Create a new empty cache.
    pub(crate) fn new() -> Self {
        Self {
            pool: Arc::new(Mutex::new(LemmaPool::new())),
        }
    }

    /// Merge a `LemmaPool` into the cache.
    ///
    /// Called by PDR after returning Unknown. Deduplicates against
    /// existing entries by (predicate, formula) identity.
    ///
    /// After merging, if the cache exceeds [`MAX_LEMMAS`], the older half
    /// is drained to bound memory growth (#8623).
    pub(crate) fn merge(&self, incoming: &LemmaPool) {
        let mut guard = self.pool.lock().unwrap_or_else(|e| e.into_inner());
        for lemma in &incoming.lemmas {
            let already_exists = guard.lemmas.iter().any(|existing| {
                existing.predicate == lemma.predicate && existing.formula == lemma.formula
            });
            if !already_exists {
                guard.lemmas.push(lemma.clone());
            }
        }
        // Evict older half when the cache exceeds the size cap (#8623).
        if guard.lemmas.len() > MAX_LEMMAS {
            let keep_from = guard.lemmas.len() / 2;
            guard.lemmas.drain(..keep_from);
        }
    }

    /// Snapshot the accumulated lemmas as a `LemmaPool`.
    ///
    /// Returns a clone so the caller can inject it into `PdrConfig::lemma_hints`
    /// without holding the lock.
    pub(crate) fn snapshot(&self) -> LemmaPool {
        let guard = self.pool.lock().unwrap_or_else(|e| e.into_inner());
        guard.clone()
    }

    /// Number of accumulated lemmas.
    pub(crate) fn len(&self) -> usize {
        let guard = self.pool.lock().unwrap_or_else(|e| e.into_inner());
        guard.len()
    }

    /// Whether the cache is empty.
    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lemma_pool::SharedLemma;
    use crate::{ChcExpr, PredicateId};

    fn pred(id: u32) -> PredicateId {
        PredicateId(id)
    }

    #[test]
    fn test_empty_cache() {
        let cache = LemmaCache::new();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
        let snap = cache.snapshot();
        assert!(snap.is_empty());
    }

    #[test]
    fn test_merge_and_snapshot() {
        let cache = LemmaCache::new();

        let mut pool = LemmaPool::new();
        pool.lemmas.push(SharedLemma {
            formula: ChcExpr::Bool(false),
            predicate: pred(0),
            source_frame: 3,
        });
        pool.lemmas.push(SharedLemma {
            formula: ChcExpr::int(42),
            predicate: pred(1),
            source_frame: 5,
        });

        cache.merge(&pool);
        assert_eq!(cache.len(), 2);

        let snap = cache.snapshot();
        assert_eq!(snap.len(), 2);
        assert_eq!(snap.lemmas[0].predicate, pred(0));
        assert_eq!(snap.lemmas[1].predicate, pred(1));
    }

    #[test]
    fn test_merge_deduplicates() {
        let cache = LemmaCache::new();

        let mut pool1 = LemmaPool::new();
        pool1.lemmas.push(SharedLemma {
            formula: ChcExpr::int(99),
            predicate: pred(0),
            source_frame: 3,
        });

        let mut pool2 = LemmaPool::new();
        // Same predicate + formula, different frame
        pool2.lemmas.push(SharedLemma {
            formula: ChcExpr::int(99),
            predicate: pred(0),
            source_frame: 7,
        });
        // Different formula
        pool2.lemmas.push(SharedLemma {
            formula: ChcExpr::int(100),
            predicate: pred(0),
            source_frame: 4,
        });

        cache.merge(&pool1);
        cache.merge(&pool2);

        // Should have 2 unique lemmas, not 3
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_multiple_merges_accumulate() {
        let cache = LemmaCache::new();

        for i in 0..5 {
            let mut pool = LemmaPool::new();
            pool.lemmas.push(SharedLemma {
                formula: ChcExpr::int(i),
                predicate: pred(0),
                source_frame: i as usize,
            });
            cache.merge(&pool);
        }

        assert_eq!(cache.len(), 5);
    }

    #[test]
    fn test_clone_shares_state() {
        let cache1 = LemmaCache::new();
        let cache2 = cache1.clone();

        let mut pool = LemmaPool::new();
        pool.lemmas.push(SharedLemma {
            formula: ChcExpr::Bool(true),
            predicate: pred(0),
            source_frame: 1,
        });

        cache1.merge(&pool);

        // cache2 should see the same data (shared Arc)
        assert_eq!(cache2.len(), 1);
    }

    #[test]
    fn test_merge_evicts_when_exceeding_cap() {
        // Use a small test to verify the eviction logic works.
        // We can't easily test with MAX_LEMMAS entries (50k), so we
        // verify the eviction path indirectly by checking that after
        // enough merges the cache doesn't grow without bound.
        let cache = LemmaCache::new();

        // Merge enough distinct lemmas to trigger eviction.
        // MAX_LEMMAS is 50_000; we batch 1000 per merge to keep test fast.
        let batch_size = 1000;
        let total_batches = (MAX_LEMMAS / batch_size) + 2; // exceed cap
        for batch in 0..total_batches {
            let mut pool = LemmaPool::new();
            for i in 0..batch_size {
                pool.lemmas.push(SharedLemma {
                    formula: ChcExpr::int((batch * batch_size + i) as i64),
                    predicate: pred(0),
                    source_frame: 1,
                });
            }
            cache.merge(&pool);
        }

        // After exceeding MAX_LEMMAS, eviction should have trimmed.
        assert!(
            cache.len() <= MAX_LEMMAS,
            "cache should be bounded: got {} entries, max {}",
            cache.len(),
            MAX_LEMMAS,
        );
        // Should have roughly half of the total after eviction.
        assert!(!cache.is_empty(), "cache should not be empty after merges");
    }
}
