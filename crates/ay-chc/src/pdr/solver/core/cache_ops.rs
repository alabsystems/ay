// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded cache insertion methods for PdrSolver.
//!
//! Wraps `PdrCacheStore::bounded_insert` for each cache with type-safe keys.

use super::{
    caches, ChcExpr, PdrSolver, PredicateId, ReachFact, ReachFactId, ReachFactStore,
    ReachabilityState,
};

impl PdrSolver {
    pub(in crate::pdr::solver) fn insert_push_cache_entry(
        &mut self,
        key: (usize, usize, u64),
        value: (ChcExpr, u64, bool),
    ) {
        caches::PdrCacheStore::bounded_insert(
            &mut self.caches.push_cache,
            key,
            value,
            caches::PdrCacheStore::push_cache_cap(),
        );
    }

    pub(in crate::pdr::solver) fn insert_self_inductive_cache_entry(
        &mut self,
        key: (PredicateId, u64),
        value: (ChcExpr, u64, bool),
    ) {
        caches::PdrCacheStore::bounded_insert(
            &mut self.caches.self_inductive_cache,
            key,
            value,
            caches::PdrCacheStore::self_inductive_cache_cap(),
        );
    }

    pub(in crate::pdr::solver) fn insert_blocks_init_cache_entry(
        &mut self,
        key: (PredicateId, u64),
        value: (ChcExpr, bool),
    ) {
        caches::PdrCacheStore::bounded_insert(
            &mut self.caches.blocks_init_cache,
            key,
            value,
            caches::PdrCacheStore::blocks_init_cache_cap(),
        );
    }

    pub(in crate::pdr::solver) fn insert_inductive_blocking_cache_entry(
        &mut self,
        key: (PredicateId, usize, u64),
        value: (ChcExpr, u64, bool),
    ) {
        caches::PdrCacheStore::bounded_insert(
            &mut self.caches.inductive_blocking_cache,
            key,
            value,
            caches::PdrCacheStore::inductive_blocking_cache_cap(),
        );
    }

    pub(in crate::pdr::solver) fn insert_cumulative_constraint_cache_entry(
        &self,
        key: (usize, PredicateId),
        value: (u64, ChcExpr),
    ) {
        let mut cache = self.caches.cumulative_constraint_cache.borrow_mut();
        caches::PdrCacheStore::bounded_insert(
            &mut cache,
            key,
            value,
            caches::PdrCacheStore::cumulative_constraint_cache_cap(),
        );
    }

    pub(in crate::pdr::solver) fn bump_spurious_cex_weakness(
        &mut self,
        key: (PredicateId, u64),
    ) -> u8 {
        let cap = caches::PdrCacheStore::spurious_cex_weakness_cap();
        if self.caches.spurious_cex_weakness.len() >= cap
            && !self.caches.spurious_cex_weakness.contains_key(&key)
        {
            self.caches.spurious_cex_weakness.clear();
        }
        let weakness = self.caches.spurious_cex_weakness.entry(key).or_insert(0);
        *weakness = weakness.saturating_add(1);
        *weakness
    }

    pub(in crate::pdr::solver) fn upsert_clause_guarded_lemma(
        &mut self,
        key: (PredicateId, usize),
        formula: ChcExpr,
        target_level: usize,
        per_key_cap: usize,
    ) -> (bool, bool) {
        let cap = caches::PdrCacheStore::clause_guarded_keys_cap();
        if self.caches.clause_guarded_lemmas.len() >= cap
            && !self.caches.clause_guarded_lemmas.contains_key(&key)
        {
            self.caches.clause_guarded_lemmas.clear();
        }

        let guarded = self.caches.clause_guarded_lemmas.entry(key).or_default();
        if let Some(existing) = guarded.iter_mut().find(|(f, _)| f == &formula) {
            if target_level > existing.1 {
                existing.1 = target_level;
                return (false, true);
            }
            return (false, false);
        }
        if guarded.len() >= per_key_cap {
            return (false, false);
        }
        guarded.push((formula, target_level));
        (true, false)
    }

    pub(in crate::pdr::solver) fn clear_restart_caches(&mut self) {
        self.caches.clear_on_restart();
    }

    /// Insert a reach fact while enforcing store saturation behavior.
    pub(in crate::pdr::solver) fn insert_reach_fact_bounded(
        reachability: &mut ReachabilityState,
        verbose: bool,
        fact: ReachFact,
    ) -> Option<ReachFactId> {
        let id = reachability.reach_facts.try_add(fact);
        if id.is_none() {
            reachability.reach_facts_saturated = true;
            tracing::warn!(
                facts = reachability.reach_facts.len(),
                cap = ReachFactStore::max_facts(),
                "PDR reach-fact cap hit; marking solver cancelled to avoid truncated reachability evidence"
            );
            if verbose {
                safe_eprintln!(
                    "PDR: reach-fact cap hit ({}/{}); returning Unknown to preserve soundness",
                    reachability.reach_facts.len(),
                    ReachFactStore::max_facts(),
                );
            }
        }
        id
    }
}
