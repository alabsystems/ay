// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV persistent cache state management.
//!
//! Extracted from check_sat.rs — these methods save and restore BV solver
//! state across incremental check_sat calls, avoiding redundant bit-blasting
//! when the query structure (signature) matches.

use super::context::SmtContext;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::kani_compat::{DetHashMap as HbHashMap, DetHashSet as HbHashSet};
use ay_core::TermId;
#[cfg(test)]
use std::sync::atomic::{AtomicUsize, Ordering};

// Test-only instrumentation for the bitblast-bound repro/regression: the peak
// `PersistentBvCache::total_entries()` observed at capture time (BEFORE the cap
// enforcement clears it) and the number of times the cap-clear actually fired.
// These are the ground-truth signals for "did the bit-blast explode the cache
// past its cap and thrash?" (see tests_check_sat.rs).
#[cfg(test)]
static BV_CACHE_PEAK_ENTRIES: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
static BV_CACHE_CAP_CLEAR_COUNT: AtomicUsize = AtomicUsize::new(0);

#[cfg(test)]
pub(super) fn reset_bv_cache_peak_for_tests() {
    BV_CACHE_PEAK_ENTRIES.store(0, Ordering::Relaxed);
    BV_CACHE_CAP_CLEAR_COUNT.store(0, Ordering::Relaxed);
}

#[cfg(test)]
pub(super) fn bv_cache_peak_entries_for_tests() -> usize {
    BV_CACHE_PEAK_ENTRIES.load(Ordering::Relaxed)
}

#[cfg(test)]
pub(super) fn bv_cache_cap_clear_count_for_tests() -> usize {
    BV_CACHE_CAP_CLEAR_COUNT.load(Ordering::Relaxed)
}

impl SmtContext {
    pub(super) fn restore_cached_bv_state(
        &self,
        cache: &super::context::PersistentBvCache,
        bv_solver: &mut ay_bv::BvSolver<'_>,
        current_terms: impl IntoIterator<Item = TermId>,
    ) -> FxHashMap<TermId, Option<String>> {
        let mut key_memo = FxHashMap::default();
        let mut predicate_to_var = HbHashMap::default();
        let mut bool_to_var = HbHashMap::default();
        let mut ite_conditions = HbHashSet::default();
        let mut key_to_term = FxHashMap::default();

        for term in current_terms {
            if let Some(key) = self.bv_cache_key(term, &mut key_memo) {
                key_to_term.entry(key.clone()).or_insert(term);
                if let Some(bits) = cache.term_to_bits.get(&key) {
                    bv_solver.set_term_bits(term, bits.clone());
                }
                if let Some(&lit) = cache.predicate_to_var.get(&key) {
                    predicate_to_var.insert(term, lit);
                }
                if let Some(&lit) = cache.bool_to_var.get(&key) {
                    bool_to_var.insert(term, lit);
                }
                if cache.ite_conditions.contains(&key) {
                    ite_conditions.insert(term);
                }
            }
        }

        bv_solver.set_next_var(cache.next_var.max(1));
        bv_solver.set_predicate_to_var(predicate_to_var);
        bv_solver.set_bool_to_var(bool_to_var);
        bv_solver.set_bv_ite_conditions(ite_conditions);
        bv_solver.set_gate_caches(
            cache.and_cache.clone(),
            cache.or_cache.clone(),
            cache.xor_cache.clone(),
        );
        bv_solver.set_and_children(cache.and_children.clone());
        bv_solver.set_mux_cache(cache.mux_cache.clone());

        let mut unsigned_div_cache = HbHashMap::default();
        for ((lhs_key, rhs_key), cached) in &cache.unsigned_div_cache {
            if let (Some(&lhs), Some(&rhs)) = (key_to_term.get(lhs_key), key_to_term.get(rhs_key)) {
                unsigned_div_cache.insert((lhs, rhs), cached.clone());
            }
        }

        let mut signed_div_cache = HbHashMap::default();
        for ((lhs_key, rhs_key), cached) in &cache.signed_div_cache {
            if let (Some(&lhs), Some(&rhs)) = (key_to_term.get(lhs_key), key_to_term.get(rhs_key)) {
                signed_div_cache.insert((lhs, rhs), cached.clone());
            }
        }
        bv_solver.set_div_caches(unsigned_div_cache, signed_div_cache);

        key_memo
    }

    pub(super) fn capture_cached_bv_state(
        &self,
        cache: &mut super::context::PersistentBvCache,
        bv_solver: &ay_bv::BvSolver<'_>,
        signature: Vec<String>,
        key_memo: &mut FxHashMap<TermId, Option<String>>,
        new_clauses: Vec<ay_core::CnfClause>,
    ) {
        let (unsigned_div_cache, signed_div_cache) = bv_solver.div_caches();
        let cached_term_bits: Vec<(String, Vec<i32>)> = bv_solver
            .term_to_bits()
            .iter()
            .filter_map(|(&term, bits)| Some((self.bv_cache_key(term, key_memo)?, bits.clone())))
            .collect();
        let cached_predicates: Vec<(String, i32)> = bv_solver
            .predicate_to_var()
            .iter()
            .filter_map(|(&term, &lit)| Some((self.bv_cache_key(term, key_memo)?, lit)))
            .collect();
        let cached_bools: Vec<(String, i32)> = bv_solver
            .bool_to_var()
            .iter()
            .filter_map(|(&term, &lit)| Some((self.bv_cache_key(term, key_memo)?, lit)))
            .collect();
        let cached_ite_conditions: Vec<String> = bv_solver
            .bv_ite_conditions()
            .iter()
            .filter_map(|&term| self.bv_cache_key(term, key_memo))
            .collect();
        let cached_unsigned_div: HbHashMap<_, _> = unsigned_div_cache
            .iter()
            .filter_map(|(&(lhs, rhs), cached)| {
                Some((
                    (
                        self.bv_cache_key(lhs, key_memo)?,
                        self.bv_cache_key(rhs, key_memo)?,
                    ),
                    cached.clone(),
                ))
            })
            .collect();
        let cached_signed_div: HbHashMap<_, _> = signed_div_cache
            .iter()
            .filter_map(|(&(lhs, rhs), cached)| {
                Some((
                    (
                        self.bv_cache_key(lhs, key_memo)?,
                        self.bv_cache_key(rhs, key_memo)?,
                    ),
                    cached.clone(),
                ))
            })
            .collect();
        let (and_cache, or_cache, xor_cache) = bv_solver.gate_caches();

        cache.signature = signature;
        cache.next_var = bv_solver.num_vars() + 1;
        cache.clauses = new_clauses;
        cache.term_to_bits = cached_term_bits.into_iter().collect();
        cache.predicate_to_var = cached_predicates.into_iter().collect();
        cache.bool_to_var = cached_bools.into_iter().collect();
        cache.ite_conditions = cached_ite_conditions.into_iter().collect();
        cache.and_cache = and_cache.clone();
        cache.and_children = bv_solver.and_children().clone();
        cache.or_cache = or_cache.clone();
        cache.xor_cache = xor_cache.clone();
        cache.mux_cache = bv_solver.mux_cache().clone();
        cache.unsigned_div_cache = cached_unsigned_div;
        cache.signed_div_cache = cached_signed_div;

        // Bounded capacity check (#8571): prevent unbounded growth on
        // long-running BV-heavy CHC solves. The cache is a pure optimization;
        // clearing it only causes re-bitblasting on the next query.
        #[cfg(test)]
        BV_CACHE_PEAK_ENTRIES.fetch_max(cache.total_entries(), Ordering::Relaxed);
        if let Some(total) = cache.enforce_capacity() {
            #[cfg(test)]
            BV_CACHE_CAP_CLEAR_COUNT.fetch_add(1, Ordering::Relaxed);
            tracing::warn!(
                entries = total,
                cap = super::context::MAX_PERSISTENT_CACHE_ENTRIES,
                "PersistentBvCache cap hit; cleared pure performance cache"
            );
            if self.verbose || crate::debug_chc_smt_enabled() {
                safe_eprintln!(
                    "[CHC-SMT] PersistentBvCache cap hit ({total} > {}); cleared pure performance cache",
                    super::context::MAX_PERSISTENT_CACHE_ENTRIES,
                );
            }
            // Bit-blast thrash bail (ny-cert grind): a FULL cache clear means the
            // bit-blast state exceeded the cap and was thrown away, forcing a
            // re-blast of the same oversized nested-serde structure. Re-blasting
            // it dozens/hundreds of times (observed ~470×) is a no-progress
            // pathology, so once the clears cross NO_PROGRESS_BV_CACHE_CLEAR_LIMIT
            // trip the no-progress breaker: `check_sat` / `is_cancelled` then bail
            // the whole solve to Unknown instead of grinding to the wall-clock
            // watchdog SIGKILL. SOUND: the cache is a pure optimization and this
            // only forces an earlier Unknown, never a Sat/Unsat/proof.
            if super::note_bv_cache_thrash_clear() {
                tracing::warn!(
                    clears = super::context::NO_PROGRESS_BV_CACHE_CLEAR_LIMIT,
                    "PersistentBvCache thrash: repeated full cap-clears with no reuse; \
                     tripping the no-progress breaker to short-circuit this solve to Unknown \
                     (fail-closed) rather than re-bitblasting until the watchdog SIGKILLs"
                );
            }
        }
    }
}
