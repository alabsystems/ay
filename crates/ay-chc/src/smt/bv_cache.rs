// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV persistent cache state management.
//!
//! Extracted from check_sat.rs — these methods save and restore BV solver
//! state across incremental check_sat calls, avoiding redundant bit-blasting
//! when the query structure (signature) matches.

mod key;

pub(super) use key::{BvCacheKey, BvCacheKeys, BvKeyMemo};

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
    /// Key the query's Tseitin `atoms` against `cache` and, when their
    /// signature matches the cached one, restore the cached state into
    /// `bv_solver`. Returns the signature, whether the cache was reused, and
    /// the key memo the capture must key with (it belongs to this `TermStore`
    /// state and to `cache.keys`).
    ///
    /// On a miss the cache is restarted (key table included) and the
    /// signature recomputed in the fresh table: the capture replaces every
    /// cached field anyway, keys of dead queries must not pile up, and a key
    /// never outlives the table that minted it. A key table past the entry
    /// cap restarts even on a match (on the reuse path it also holds the keys
    /// of earlier queries' terms).
    pub(super) fn open_bv_cache(
        &self,
        cache: &mut super::context::PersistentBvCache,
        bv_solver: &mut ay_bv::BvSolver<'_>,
        atoms: &[TermId],
    ) -> (Vec<BvCacheKey>, bool, BvKeyMemo) {
        let mut memo = BvKeyMemo::default();
        let keys_were_empty = cache.keys.is_empty();
        let signature = self.bv_cache_signature(&mut cache.keys, atoms.iter().copied(), &mut memo);
        if cache.signature == signature
            && cache.keys.len() <= super::context::MAX_PERSISTENT_CACHE_ENTRIES
        {
            // Restore over the TRANSITIVE BV SUB-TERM CLOSURE of the atoms,
            // not the atom terms alone. `cache.term_to_bits` holds the bit
            // vectors of every blasted sub-term (variables, adders, ...), but
            // the atoms themselves are Bool — restoring only atoms brings
            // back their memoized predicate vars while leaving every
            // variable's bits unknown to `bv_solver`. Any NEW atom over a
            // previously-blasted variable then mints a SECOND, disconnected
            // set of bit variables for the same term: the replayed circuit
            // constrains the old bits, the new atom constrains the new bits,
            // nothing links them, and model extraction (which reads
            // `term_to_bits`) reports values that violate the memoized atoms.
            // That is the "SAT model from DPLL(T) loop violates original
            // expression" WARN-flood that collapsed the native BV lane to
            // Unknown on model-checker-consumer PDR workloads (looping_id L0 failure):
            // every PDR frame query shares the atom signature but adds fresh
            // cube atoms over the same state variables.
            let restore_terms = self.bv_subterm_closure(atoms);
            self.restore_cached_bv_state(cache, bv_solver, restore_terms, &mut memo);
            return (signature, true, memo);
        }
        if !keys_were_empty {
            cache.clear();
            memo.clear();
            let signature =
                self.bv_cache_signature(&mut cache.keys, atoms.iter().copied(), &mut memo);
            return (signature, false, memo);
        }
        (signature, false, memo)
    }

    /// Restore the cached state of every current term whose structural key
    /// the cache holds. `key_memo` must belong to this `TermStore` state and
    /// to `cache.keys` (it keeps the keys minted here for the capture).
    pub(super) fn restore_cached_bv_state(
        &self,
        cache: &mut super::context::PersistentBvCache,
        bv_solver: &mut ay_bv::BvSolver<'_>,
        current_terms: impl IntoIterator<Item = TermId>,
        key_memo: &mut BvKeyMemo,
    ) {
        let mut predicate_to_var = HbHashMap::default();
        let mut bool_to_var = HbHashMap::default();
        let mut ite_conditions = HbHashSet::default();
        let mut key_to_term = FxHashMap::default();

        for term in current_terms {
            if let Some(key) = self.bv_cache_key(&mut cache.keys, term, key_memo) {
                key_to_term.entry(key).or_insert(term);
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
    }

    pub(super) fn capture_cached_bv_state(
        &self,
        cache: &mut super::context::PersistentBvCache,
        bv_solver: &ay_bv::BvSolver<'_>,
        signature: Vec<BvCacheKey>,
        key_memo: &mut BvKeyMemo,
        new_clauses: Vec<ay_core::CnfClause>,
    ) {
        self.capture_cached_bv_state_with_limit(
            cache,
            bv_solver,
            signature,
            key_memo,
            new_clauses,
            super::context::MAX_PERSISTENT_CACHE_ENTRIES,
        );
    }

    /// Retention is optional; the caller has already wired the complete
    /// circuit into its SAT state. A refused cache is never an incomplete CNF.
    pub(in crate::smt) fn capture_cached_bv_state_with_limit(
        &self,
        cache: &mut super::context::PersistentBvCache,
        bv_solver: &ay_bv::BvSolver<'_>,
        signature: Vec<BvCacheKey>,
        key_memo: &mut BvKeyMemo,
        new_clauses: Vec<ay_core::CnfClause>,
        limit: usize,
    ) {
        // take_clauses may have drained the solver, and reuse supplies the
        // full retained circuit plus a delta. Replace (do not add twice) its
        // live clause count with the supplied complete circuit's count.
        let entries = bv_solver
            .minted_entries_estimate()
            .checked_sub(bv_solver.clauses().len())
            .and_then(|maps| maps.checked_add(new_clauses.len()));
        if !bv_solver.encoding_complete()
            || entries.is_none_or(|entries| entries > limit)
            || cache.keys.len() > limit
        {
            // Drop capacity too; keeping oversized allocations defeats the
            // purpose of declining retention. This is ordinary eviction, not
            // a failed query and not evidence for the no-progress breaker.
            *cache = Default::default();
            return;
        }
        let (unsigned_div_cache, signed_div_cache) = bv_solver.div_caches();
        let mut key = |term| self.bv_cache_key(&mut cache.keys, term, key_memo);
        let cached_term_bits: Vec<(BvCacheKey, Vec<i32>)> = bv_solver
            .term_to_bits()
            .iter()
            .filter_map(|(&term, bits)| Some((key(term)?, bits.clone())))
            .collect();
        let cached_predicates: Vec<(BvCacheKey, i32)> = bv_solver
            .predicate_to_var()
            .iter()
            .filter_map(|(&term, &lit)| Some((key(term)?, lit)))
            .collect();
        let cached_bools: Vec<(BvCacheKey, i32)> = bv_solver
            .bool_to_var()
            .iter()
            .filter_map(|(&term, &lit)| Some((key(term)?, lit)))
            .collect();
        let cached_ite_conditions: Vec<BvCacheKey> = bv_solver
            .bv_ite_conditions()
            .iter()
            .filter_map(|&term| key(term))
            .collect();
        let cached_unsigned_div: HbHashMap<_, _> = unsigned_div_cache
            .iter()
            .filter_map(|(&(lhs, rhs), cached)| Some(((key(lhs)?, key(rhs)?), cached.clone())))
            .collect();
        let cached_signed_div: HbHashMap<_, _> = signed_div_cache
            .iter()
            .filter_map(|(&(lhs, rhs), cached)| Some(((key(lhs)?, key(rhs)?), cached.clone())))
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
        if cache.keys.len() > limit
            || cache.total_entries() > limit
            || !bv_solver.encoding_complete()
        {
            #[cfg(test)]
            BV_CACHE_CAP_CLEAR_COUNT.fetch_add(1, Ordering::Relaxed);
            *cache = Default::default();
        }
    }
}
