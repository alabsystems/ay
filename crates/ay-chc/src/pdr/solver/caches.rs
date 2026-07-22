// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Centralized cache subsystem for PdrSolver (#3590).
//!
//! All revision-sensitive and bounded caches live here.  `PdrCacheStore`
//! provides coordinated invalidation (`clear_on_restart`, per-field caps)
//! and keeps the parent `PdrSolver` struct focused on algorithmic state.

use std::cell::RefCell;
use std::collections::VecDeque;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use crate::{ChcExpr, ChcVar, PredicateId};

use super::super::implication_cache::ImplicationCache;
use super::super::lemma_cluster::ClusterStore;

// ── Capacity limits (memory defense, #2780) ────────────────────────────────

/// Maximum per-predicate persistent solvers (#6554).
/// Each entry is a full SAT solver; 64 predicates is generous.
pub(in crate::pdr) const MAX_PROP_SOLVERS: usize = 64;

/// Maximum array clause sessions (#6554).
/// Lighter weight than prop_solvers but still bounded.
pub(in crate::pdr) const MAX_ARRAY_SESSIONS: usize = 128;

const MAX_PUSH_CACHE_ENTRIES: usize = 50_000;
const MAX_SELF_INDUCTIVE_CACHE_ENTRIES: usize = 50_000;
const MAX_BLOCKS_INIT_CACHE_ENTRIES: usize = 25_000;
const MAX_INDUCTIVE_BLOCKING_CACHE_ENTRIES: usize = 50_000;
const MAX_CUMULATIVE_CONSTRAINT_CACHE_ENTRIES: usize = 10_000;
const MAX_SPURIOUS_CEX_WEAKNESS_ENTRIES: usize = 20_000;
const MAX_CLAUSE_GUARDED_KEYS: usize = 4_096;
const MAX_DISEQ_VALUES_ENTRIES: usize = 10_000;

// ── PdrCacheStore ──────────────────────────────────────────────────────────

/// Consolidated cache subsystem for `PdrSolver`.
///
/// Groups all revision-sensitive, bounded, and static caches into a single
/// struct with coordinated invalidation and capacity enforcement.
pub(in crate::pdr) struct PdrCacheStore {
    // ── Static lookups (computed once at init, never modified) ──────────
    /// Canonical variables for each predicate's arguments.
    pub predicate_vars: FxHashMap<PredicateId, Vec<ChcVar>>,
    /// For each predicate P, the body predicates P's transitions depend on.
    pub push_cache_deps: FxHashMap<PredicateId, Vec<PredicateId>>,
    /// Inverse of `push_cache_deps`: which predicates use P in their body.
    pub predicate_users: FxHashMap<PredicateId, Vec<PredicateId>>,
    /// Predicates that have fact clauses (init rules).
    pub predicates_with_facts: FxHashSet<PredicateId>,
    /// Predicates transitively reachable from init via transitions.
    pub reachable_predicates: FxHashSet<PredicateId>,

    // ── Dynamic caches (revision/frame-dependent, bounded) ─────────────
    /// Lemma push checks: `(level, pred_idx, formula_hash) -> (expr, sig, can_push)`.
    /// Collision safety (#2860): stores full `ChcExpr` for verification.
    pub push_cache: FxHashMap<(usize, usize, u64), (ChcExpr, u64, bool)>,
    /// Self-inductiveness checks: `(pred, hash) -> (expr, frame1_rev, is_self_inductive)`.
    pub self_inductive_cache: FxHashMap<(PredicateId, u64), (ChcExpr, u64, bool)>,
    /// P0 taint (model-checker-consumer wishlist 2026-07-17 item 2.3): blocking formulas
    /// whose self-inductiveness was accepted via the forward-SAMPLE fallback
    /// (SMT Unknown on nonlinear mul + >=5 satisfying simulation samples —
    /// unsound-by-construction evidence, self_inductive.rs). Keyed like
    /// `self_inductive_cache`: `(pred, blocking_formula.structural_hash())`.
    /// Tainted lemmas must NEVER grant `individually_inductive` (the #5877
    /// whole-model verification skip). Monotone and conservative: entries are
    /// never removed (a later genuine SMT pass for the same formula still
    /// leaves the taint — that only forces full verification, never a skip).
    /// Survives restart for the same reason. Expected tiny (sampling fires
    /// only on nonlinear-mul Unknown), so unbounded.
    pub sample_accepted_taint: FxHashSet<(PredicateId, u64)>,
    /// Lemma hints already rejected by the relative-induction (entry-CEGAR)
    /// fallthrough (model-checker-consumer wishlist item 6). The entry query is expensive;
    /// hint sets are re-applied at Startup and every Stuck stage, so without
    /// this memo each pass re-pays the full rejection cost. Conservative:
    /// entries are never removed — a once-rejected hint stays on the cheap
    /// rejection path (completeness-only; frames strengthen over time but a
    /// hint that mattered would have been admitted by the level scan first).
    /// Bounded in practice by the hint set size.
    pub entry_induction_rejected_hints: FxHashSet<(PredicateId, ChcExpr)>,
    /// Blocks-initial-states checks: `(pred, hash) -> (expr, blocks_all)`.
    /// Monotonic (facts don't change).
    pub blocks_init_cache: FxHashMap<(PredicateId, u64), (ChcExpr, bool)>,
    /// Inductive-blocking checks: `(pred, level, hash) -> (expr, frame_epoch, result)`.
    /// `false` entries are only valid while the recorded frame epoch matches
    /// (`PdrSolver::frames_lemma_epoch`); `true` entries are stable (#pdr-chain).
    pub inductive_blocking_cache: FxHashMap<(PredicateId, usize, u64), (ChcExpr, u64, bool)>,
    /// Init-only value checks: `(pred, var_name, value) -> (frame1_rev, is_init_only)`.
    pub init_only_value_cache: FxHashMap<(PredicateId, String, i128), (u64, bool)>,
    /// Cumulative frame constraint: `(level, pred) -> (revision_sum, formula)`.
    /// Uses `RefCell` because callers need `&self` access.
    pub cumulative_constraint_cache: RefCell<FxHashMap<(usize, PredicateId), (u64, ChcExpr)>>,
    /// Per-predicate Entry-CEGAR refinement budget.
    pub entry_cegar_budget: FxHashMap<PredicateId, usize>,
    /// Disequality values per `(pred, var, level)` for enumeration detection.
    pub diseq_values: FxHashMap<(PredicateId, String, usize), Vec<i128>>,
    /// Spurious CEX weakness per `(pred, root_state_hash)`.
    pub spurious_cex_weakness: FxHashMap<(PredicateId, u64), u8>,
    /// Blocked states for convex closure per predicate.
    pub blocked_states_for_convex: FxHashMap<PredicateId, VecDeque<FxHashMap<String, i64>>>,
    /// Clause-guarded propagated lemmas: `(target_pred, clause_idx) -> [(expr, max_level)]`.
    pub clause_guarded_lemmas: FxHashMap<(PredicateId, usize), Vec<(ChcExpr, usize)>>,
    /// LAWI-style model-guided implication cache.
    pub implication_cache: ImplicationCache,
    /// Lemma cluster store for global generalization.
    pub cluster_store: ClusterStore,
}

impl PdrCacheStore {
    /// Create a cache store with pre-computed static lookups.
    ///
    /// Static lookups are computed once during `PdrSolver::new()` from the
    /// CHC problem and never modified afterwards.  Dynamic caches start empty.
    pub(crate) fn new(
        predicate_vars: FxHashMap<PredicateId, Vec<ChcVar>>,
        push_cache_deps: FxHashMap<PredicateId, Vec<PredicateId>>,
        predicate_users: FxHashMap<PredicateId, Vec<PredicateId>>,
        predicates_with_facts: FxHashSet<PredicateId>,
        reachable_predicates: FxHashSet<PredicateId>,
    ) -> Self {
        Self {
            predicate_vars,
            push_cache_deps,
            predicate_users,
            predicates_with_facts,
            reachable_predicates,
            push_cache: FxHashMap::default(),
            self_inductive_cache: FxHashMap::default(),
            sample_accepted_taint: FxHashSet::default(),
            entry_induction_rejected_hints: FxHashSet::default(),
            blocks_init_cache: FxHashMap::default(),
            inductive_blocking_cache: FxHashMap::default(),
            init_only_value_cache: FxHashMap::default(),
            cumulative_constraint_cache: RefCell::new(FxHashMap::default()),
            entry_cegar_budget: FxHashMap::default(),
            diseq_values: FxHashMap::default(),
            spurious_cex_weakness: FxHashMap::default(),
            blocked_states_for_convex: FxHashMap::default(),
            clause_guarded_lemmas: FxHashMap::default(),
            implication_cache: ImplicationCache::new(),
            cluster_store: ClusterStore::new(),
        }
    }

    /// Clear all revision-dependent caches on solver restart (#1270).
    ///
    /// Caches that survive restart:
    /// - `blocks_init_cache` (facts never change)
    /// - `implication_cache` (countermodels remain valid)
    /// - `clause_guarded_lemmas` (propagated lemmas survive restarts)
    /// - `entry_cegar_budget` (budget depletion is permanent)
    /// - `sample_accepted_taint` (soundness taint is permanent-conservative)
    /// - All static lookups
    pub(crate) fn clear_on_restart(&mut self) {
        self.push_cache.clear();
        self.self_inductive_cache.clear();
        self.inductive_blocking_cache.clear();
        self.init_only_value_cache.clear();
        self.cumulative_constraint_cache.borrow_mut().clear();
        self.spurious_cex_weakness.clear();
        self.blocked_states_for_convex.clear();
        self.diseq_values.clear();
    }

    /// Bounded insert: if `cache` is at capacity and key is new, clear and re-insert.
    ///
    /// Simple "clear everything on overflow" strategy — avoids LRU complexity.
    #[inline]
    pub(crate) fn bounded_insert<K, V>(cache: &mut FxHashMap<K, V>, key: K, value: V, cap: usize)
    where
        K: std::hash::Hash + Eq,
    {
        if cache.len() >= cap && !cache.contains_key(&key) {
            cache.clear();
        }
        cache.insert(key, value);
    }

    // ── Per-cache cap accessors ────────────────────────────────────────

    pub(crate) const fn push_cache_cap() -> usize {
        MAX_PUSH_CACHE_ENTRIES
    }
    pub(crate) const fn self_inductive_cache_cap() -> usize {
        MAX_SELF_INDUCTIVE_CACHE_ENTRIES
    }
    pub(crate) const fn blocks_init_cache_cap() -> usize {
        MAX_BLOCKS_INIT_CACHE_ENTRIES
    }
    pub(crate) const fn inductive_blocking_cache_cap() -> usize {
        MAX_INDUCTIVE_BLOCKING_CACHE_ENTRIES
    }
    pub(crate) const fn cumulative_constraint_cache_cap() -> usize {
        MAX_CUMULATIVE_CONSTRAINT_CACHE_ENTRIES
    }
    pub(crate) const fn spurious_cex_weakness_cap() -> usize {
        MAX_SPURIOUS_CEX_WEAKNESS_ENTRIES
    }
    pub(crate) const fn clause_guarded_keys_cap() -> usize {
        MAX_CLAUSE_GUARDED_KEYS
    }
    pub(crate) const fn diseq_values_cap() -> usize {
        MAX_DISEQ_VALUES_ENTRIES
    }
}

// ── LruSolverMap ──────────────────────────────────────────────────────────

/// LRU-evicting map for heavyweight solver instances (#6554).
///
/// Wraps `FxHashMap<K, (V, u64)>` where the `u64` is a monotonic access counter.
/// When total entries reach `cap` and a new key is inserted, the entry with the
/// lowest access counter is evicted. Evicted solvers are recreated on demand
/// (they are caches, not essential state).
///
/// Used for `prop_solvers` (per-predicate SAT solvers) and `array_clause_sessions`
/// (per-clause persistent executor sessions).
pub(in crate::pdr) struct LruSolverMap<K, V> {
    map: FxHashMap<K, (V, u64)>,
    counter: u64,
    cap: usize,
}

// LruSolverMap exposes the full standard collection
// API (get/get_mut/contains_key/len/is_empty/values/iter/iter_mut/clear) for
// consistency. Only `get_or_insert_with` is on the hot path today.
#[allow(dead_code)]
impl<K, V> LruSolverMap<K, V>
where
    K: std::hash::Hash + Eq + Copy,
{
    /// Create an empty LRU map with the given capacity.
    pub(in crate::pdr) fn new(cap: usize) -> Self {
        Self {
            map: FxHashMap::default(),
            counter: 0,
            cap,
        }
    }

    /// Look up an entry and bump its access counter.
    pub(in crate::pdr) fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        self.counter += 1;
        let tick = self.counter;
        self.map.get_mut(key).map(|(v, ts)| {
            *ts = tick;
            v
        })
    }

    /// Get an existing entry or insert a new one. If at capacity, evict LRU first.
    pub(in crate::pdr) fn get_or_insert_with(&mut self, key: K, f: impl FnOnce() -> V) -> &mut V {
        self.counter += 1;
        let tick = self.counter;
        if self.map.contains_key(&key) {
            let entry = self.map.get_mut(&key).expect("key just checked");
            entry.1 = tick;
            return &mut entry.0;
        }
        // Need to insert -- evict if at capacity.
        if self.map.len() >= self.cap {
            self.evict_lru();
        }
        self.map.insert(key, (f(), tick));
        &mut self.map.get_mut(&key).expect("just inserted").0
    }

    /// Evict the entry with the lowest access counter.
    fn evict_lru(&mut self) {
        if let Some((&lru_key, _)) = self.map.iter().min_by_key(|(_, (_, ts))| *ts) {
            self.map.remove(&lru_key);
        }
    }

    /// Immutable lookup (does NOT bump access counter).
    /// Used by tests and read-only observation.
    pub(in crate::pdr) fn get(&self, key: &K) -> Option<&V> {
        self.map.get(key).map(|(v, _)| v)
    }

    /// Check if the key exists (does NOT bump access counter).
    pub(in crate::pdr) fn contains_key(&self, key: &K) -> bool {
        self.map.contains_key(key)
    }

    /// Number of entries in the map.
    pub(in crate::pdr) fn len(&self) -> usize {
        self.map.len()
    }

    /// Whether the map is empty.
    pub(in crate::pdr) fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Iterate over values.
    pub(in crate::pdr) fn values(&self) -> impl Iterator<Item = &V> {
        self.map.values().map(|(v, _)| v)
    }

    /// Iterate over key-value pairs (without access timestamps).
    pub(in crate::pdr) fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.map.iter().map(|(k, (v, _))| (k, v))
    }

    /// Mutable iterator over key-value pairs.
    pub(in crate::pdr) fn iter_mut(&mut self) -> impl Iterator<Item = (&K, &mut V)> {
        self.map.iter_mut().map(|(k, (v, _))| (k, v))
    }

    /// Clear all entries (used on solver restart).
    pub(in crate::pdr) fn clear(&mut self) {
        self.map.clear();
        // Do not reset counter -- monotonicity is about ordering, not about
        // absolute values. Keeping the counter prevents stale-timestamp confusion
        // if entries are re-created after clear.
    }
}

impl<K, V> Default for LruSolverMap<K, V>
where
    K: std::hash::Hash + Eq + Copy,
{
    fn default() -> Self {
        // Default with a generous cap; callers should prefer `new(cap)`.
        Self::new(1024)
    }
}

#[cfg(test)]
mod lru_solver_map_tests {
    use super::LruSolverMap;

    #[test]
    fn test_lru_solver_map_basic_insert_and_get() {
        let mut map: LruSolverMap<u32, String> = LruSolverMap::new(4);
        map.get_or_insert_with(1, || "one".to_string());
        map.get_or_insert_with(2, || "two".to_string());
        assert_eq!(map.len(), 2);
        assert!(map.contains_key(&1));
        assert!(map.contains_key(&2));
        assert!(!map.contains_key(&3));
    }

    #[test]
    fn test_lru_solver_map_eviction_at_capacity() {
        let mut map: LruSolverMap<u32, String> = LruSolverMap::new(3);
        map.get_or_insert_with(1, || "one".to_string());
        map.get_or_insert_with(2, || "two".to_string());
        map.get_or_insert_with(3, || "three".to_string());
        assert_eq!(map.len(), 3);
        // Inserting 4th should evict key 1 (LRU)
        map.get_or_insert_with(4, || "four".to_string());
        assert_eq!(map.len(), 3);
        assert!(!map.contains_key(&1), "key 1 should be evicted");
        assert!(map.contains_key(&2));
        assert!(map.contains_key(&3));
        assert!(map.contains_key(&4));
    }

    #[test]
    fn test_lru_solver_map_access_bumps_priority() {
        let mut map: LruSolverMap<u32, String> = LruSolverMap::new(3);
        map.get_or_insert_with(1, || "one".to_string());
        map.get_or_insert_with(2, || "two".to_string());
        map.get_or_insert_with(3, || "three".to_string());
        // Access key 1 to bump its priority
        let _ = map.get_mut(&1);
        // Insert 4 -- should evict key 2 (now LRU)
        map.get_or_insert_with(4, || "four".to_string());
        assert!(map.contains_key(&1), "key 1 was accessed, should survive");
        assert!(!map.contains_key(&2), "key 2 should be evicted (LRU)");
        assert!(map.contains_key(&3));
        assert!(map.contains_key(&4));
    }

    #[test]
    fn test_lru_solver_map_get_or_insert_existing_no_eviction() {
        let mut map: LruSolverMap<u32, String> = LruSolverMap::new(2);
        map.get_or_insert_with(1, || "one".to_string());
        map.get_or_insert_with(2, || "two".to_string());
        // Re-insert existing key -- should NOT evict
        let val = map.get_or_insert_with(1, || "should_not_be_used".to_string());
        assert_eq!(val, "one");
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn test_lru_solver_map_clear() {
        let mut map: LruSolverMap<u32, String> = LruSolverMap::new(4);
        map.get_or_insert_with(1, || "one".to_string());
        map.get_or_insert_with(2, || "two".to_string());
        map.clear();
        assert_eq!(map.len(), 0);
        assert!(!map.contains_key(&1));
    }
}
