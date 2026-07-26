// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! AY Arrays - Array theory solver
//!
//! Implements the theory of arrays using the standard axioms:
//! - Read-over-write (same index): select(store(a, i, v), i) = v
//! - Read-over-write (different index): i ≠ j → select(store(a, i, v), j) = select(a, j)
//! - Extensionality: (∀i. select(a, i) = select(b, i)) → a = b
//!
//! This solver works in conjunction with EUF for equality reasoning.

#![warn(missing_docs)]
#![warn(clippy::all)]

mod theory_check;
mod theory_impl;
mod theory_propagate;

mod axiom_checkers;
mod axiom_store_checks;
mod bridge;
mod equality;
mod equality_query;
mod final_check;
mod incremental;
mod model;
mod propagation;
mod store_chain;
mod union_find;
mod weak_equiv;
mod weak_lemmas;

pub(crate) use bridge::SelectResolution;
pub use bridge::UndecidedIndexPair;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

/// A store chain entry: (array_term, base_array, effective_stores as (index, value) pairs).
type StoreChainEntry = (TermId, TermId, Vec<(TermId, TermId)>);

/// Ordered work queue with O(1) membership dedup.
///
/// The event-driven pending queues (`pending_row1`, `pending_row2_upward`,
/// `pending_store_chain`, …) were plain `Vec`s deduplicated by
/// `Vec::contains` linear scans. `notify_equality()` pushes cross-products of
/// `stores × parent_selects` per cross-theory equality, so on select-heavy
/// AUFLIA instances (QF_ALIA cs_lazy.i_*: ~200k terms after Shannon lifting)
/// those scans were O(queue × pairs × notifications) and consumed >99% of the
/// solve (2026-07-11 sample profile: one `memcmp` loop inside
/// `notify_equality`). This queue keeps the exact same visible semantics
/// (insertion-ordered, no duplicates while queued) with a `HashSet` mirror
/// for constant-time membership.
#[derive(Debug, Clone)]
pub(crate) struct DedupQueue<T> {
    items: Vec<T>,
    seen: HashSet<T>,
}

impl<T> Default for DedupQueue<T> {
    fn default() -> Self {
        Self {
            items: Vec::new(),
            seen: HashSet::default(),
        }
    }
}

impl<T: Copy + Eq + std::hash::Hash> DedupQueue<T> {
    /// Append `item` unless it is already queued.
    pub(crate) fn push(&mut self, item: T) {
        if self.seen.insert(item) {
            self.items.push(item);
        }
    }

    /// Remove and return all queued items (queue becomes empty).
    pub(crate) fn take(&mut self) -> Vec<T> {
        self.seen.clear();
        std::mem::take(&mut self.items)
    }

    /// Replace the queue contents (used to put back retained work after a
    /// budgeted drain).
    pub(crate) fn replace(&mut self, items: Vec<T>) {
        self.seen.clear();
        self.seen.extend(items.iter().copied());
        self.items = items;
    }

    pub(crate) fn clear(&mut self) {
        self.items.clear();
        self.seen.clear();
    }

    /// Used by the Kani verification harness and tests.
    #[cfg_attr(not(any(test, kani)), allow(dead_code))]
    pub(crate) fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub(crate) fn iter(&self) -> std::slice::Iter<'_, T> {
        self.items.iter()
    }

    /// O(1) queued-membership test (test observability).
    #[cfg_attr(not(any(test, kani)), allow(dead_code))]
    pub(crate) fn contains(&self, item: &T) -> bool {
        self.seen.contains(item)
    }

    /// Queued items in insertion order (test observability).
    #[cfg(test)]
    pub(crate) fn items(&self) -> &[T] {
        &self.items
    }
}

use ay_core::{
    DiscoveredEquality, EqualityPropagationResult, ModelEqualityRequest, Sort, TheoryLemma,
    TheoryLit, TheoryPropagation, TheoryResult, TheorySolver,
};

/// Interpretation of a single array in the model
#[derive(Debug, Clone, Default)]
pub struct ArrayInterpretation {
    /// Default value for all indices (if this is a const-array or has a known default)
    pub default: Option<String>,
    /// Explicit index-value mappings, authoritative/newest first.
    ///
    /// Duplicate indices can arise from a syntactic store chain. Consumers
    /// doing direct lookup must take the first matching entry; consumers
    /// rebuilding an SMT `store` chain or an oldest-first value representation
    /// must iterate this vector in reverse.
    pub stores: Vec<(String, String)>,
    /// Index sort for formatting
    pub index_sort: Option<Sort>,
    /// Element sort for formatting
    pub element_sort: Option<Sort>,
}

/// Model for array theory - maps array terms to their interpretations
#[derive(Debug, Clone, Default)]
pub struct ArrayModel {
    /// Maps array term IDs to their interpretations
    pub array_values: HashMap<TermId, ArrayInterpretation>,
    /// Arrays whose extraction DROPPED a cell because two committed reads of
    /// one (base, index-value) cell disagreed
    /// (#select-read-conflict-fail-closed). Such an interpretation is
    /// deliberately PARTIAL at the dropped cell; model completion must NOT
    /// total it — a fabricated default at the conflicted cell is exactly the
    /// wrong value the validators and the independent model-check gate would
    /// then refute a genuine `Sat` against.
    pub read_conflicted: HashSet<TermId>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ArrayVarData {
    /// `store(a, i, v)` terms whose result array is this term.
    stores_as_result: Vec<TermId>,
    /// `select(a, j)` terms reading from this array term.
    parent_selects: Vec<TermId>,
    /// `store(a, i, v)` terms whose base array is this term.
    parent_stores: Vec<TermId>,
    /// Whether delayed upward ROW2 work may be needed for this array term.
    prop_upward: bool,
}

/// Invertible undo record for one `merge_array_var_data` call. Records the
/// merge target and the pre-merge lengths of its three append-only vecs plus
/// its `prop_upward` flag, so the merge can be reversed by truncation.
#[derive(Debug, Clone, Copy)]
struct ArrayVarMergeUndo {
    target: TermId,
    stores_len: u32,
    selects_len: u32,
    parent_stores_len: u32,
    prev_prop_upward: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PendingAxiom {
    /// Downward ROW2 work for one `(store, select)` pair.
    Row2Down { store: TermId, select: TermId },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ExactSelectModelEqKind {
    DownIndex,
    DownSelect,
    UpwardIndex,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ExactSelectModelEqObligation {
    kind: ExactSelectModelEqKind,
    request: (TermId, TermId),
    store: TermId,
    store_base: TermId,
    store_index: TermId,
    store_value: TermId,
    select: TermId,
    select_array: TermId,
    select_index: TermId,
    value: Option<TermId>,
    reasons: Vec<TheoryLit>,
}

/// Stable key for exact select model-equality obligations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExactSelectModelEqKey {
    kind: u8,
    request: (TermId, TermId),
    store: TermId,
    store_base: TermId,
    store_index: TermId,
    store_value: TermId,
    select: TermId,
    select_array: TermId,
    select_index: TermId,
    value: Option<TermId>,
}

/// Reason-carrying array equality propagated to another theory.
///
/// AUFLIA may recreate a fresh combined theory solver after a model-equality
/// refinement. Persisting these entries lets the fresh combiner replay
/// reason-validated array-derived equalities into EUF and seed the array
/// solver's local duplicate filter.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayPropagatedEqualityReplay {
    /// Left-hand side of the propagated equality.
    pub lhs: TermId,
    /// Right-hand side of the propagated equality.
    pub rhs: TermId,
    /// SAT-visible literals justifying this equality.
    pub reason: Vec<TheoryLit>,
}

impl ArrayPropagatedEqualityReplay {
    /// Create a canonical replay entry.
    #[must_use]
    pub fn new(lhs: TermId, rhs: TermId, mut reason: Vec<TheoryLit>) -> Self {
        reason.sort_by_key(|lit| (lit.term.0, lit.value));
        reason.dedup_by_key(|lit| (lit.term, lit.value));
        let (lhs, rhs) = if lhs.0 <= rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        Self { lhs, rhs, reason }
    }

    /// Canonical unordered pair key.
    pub fn key(&self) -> (TermId, TermId) {
        (self.lhs, self.rhs)
    }
}

impl ExactSelectModelEqObligation {
    fn stable_key(&self) -> ExactSelectModelEqKey {
        let kind = match self.kind {
            ExactSelectModelEqKind::DownIndex => 0,
            ExactSelectModelEqKind::DownSelect => 1,
            ExactSelectModelEqKind::UpwardIndex => 2,
        };
        let value = match self.kind {
            ExactSelectModelEqKind::UpwardIndex => None,
            _ => self.value,
        };
        ExactSelectModelEqKey {
            kind,
            request: self.request,
            store: self.store,
            store_base: self.store_base,
            store_index: self.store_index,
            store_value: self.store_value,
            select: self.select,
            select_array: self.select_array,
            select_index: self.select_index,
            value,
        }
    }
}

/// Thread-local, call-scoped memo for `equality_reason_paths_from`
/// (#no-cross-flood). It is a plain cache of a deterministic pure function of
/// the (momentarily immutable) equality graph + assignments, so a hit is
/// byte-identical to a recomputation. It is armed only by the RAII `Guard` that
/// `propagate_equalities_impl` raises around its read-only select scan, and the
/// guard restores the prior state (normally: disabled) on every exit path,
/// including panics and mid-loop `return`s — so it can never be read stale from
/// another context. A thread-local (not a solver field) keeps `&self` query
/// paths free of borrow conflicts with the `&mut self` scan loop.
pub(crate) mod eq_paths_cache {
    use super::SelectResolution;
    use ay_core::kani_compat::DetHashMap as HashMap;
    use ay_core::{TermId, TheoryLit};
    use std::cell::RefCell;
    use std::rc::Rc;

    type PathMap = HashMap<TermId, Vec<TheoryLit>>;
    /// Memoized payload of `resolve_select_base_for_propagation_with_reasons`:
    /// `(resolution, reasons)`.
    pub(crate) type ResolveBaseMemo = (SelectResolution, Vec<TheoryLit>);
    type PairReason = Option<Vec<TheoryLit>>;
    type AssertedPredecessors = HashMap<TermId, (TermId, TermId)>;
    type SharedAssertedPredecessors = Rc<AssertedPredecessors>;

    /// Memoized payload of `find_store_through_eq_with_mode`:
    /// `(base, index, value, eq_terms, reasons)`.
    pub(crate) type StoreThroughMemo = (TermId, TermId, TermId, Vec<TermId>, Vec<TheoryLit>);

    /// The three call-scoped memo tables. Each is a plain cache of a
    /// deterministic pure function of the (momentarily immutable) equality
    /// graph + assignments + external facts, so a hit is byte-identical to a
    /// recomputation. All are keyed by the exact (unordered-as-given) inputs so
    /// no orientation assumption is made.
    #[derive(Default)]
    struct Tables {
        paths: HashMap<TermId, Rc<PathMap>>,
        distinct: HashMap<(TermId, TermId), PairReason>,
        equal: HashMap<(TermId, TermId), PairReason>,
        /// Whole-output memo of `select_conflict_candidate_pairs()` (D1,
        /// SELECT-PAIRS blueprint): the generator is a pure function of
        /// `select_cache` / class connectivity / `diseq_set` / term constants,
        /// all frozen for the lifetime of the window, so a hit is
        /// byte-identical (ordering included: the generator sorts its output)
        /// to a recomputation.
        candidate_pairs: Option<Rc<[(TermId, TermId)]>>,
        /// Window memo of `select_cache` grouped by syntactic array term (D3):
        /// `select_cache` is frozen for the lifetime of the window.
        selects_by_array: Option<Rc<HashMap<TermId, Vec<TermId>>>>,
        /// Per-`(term, skip-sentinel-edges)` memo of
        /// `find_store_through_eq_with_mode` (#7956 store-chain eq-path wall):
        /// the walk is a deterministic pure function of `store_cache`,
        /// `eq_adj`, `external_eq_reasons`, `requested_interface_eqs` and term
        /// sorts — all frozen for the lifetime of the window — so a hit is
        /// byte-identical to a recomputation. This collapses the
        /// O(pairs × chain × class) re-walk that `store_chain_reaches_asserted`
        /// / `collect_complete_effective_stores` drove per candidate pair.
        store_through: HashMap<(TermId, bool), Option<Rc<StoreThroughMemo>>>,
        /// Per-`(array, index)` memo of
        /// `resolve_select_base_for_propagation_with_reasons` (store-chain
        /// resolution for N-O equality propagation). The resolution is a
        /// deterministic pure function of `store_cache`, `eq_adj`, external
        /// facts, `assigns`, `diseq_set` and the (immutable) affine structure —
        /// all frozen for the lifetime of the window — so a hit is
        /// byte-identical to a recomputation (its reasons are sorted+deduped
        /// before return). This collapses the redundant re-resolution of the
        /// same `(array, index)` across the many asserted-array-equality
        /// (`lhs`/`rhs`) pairs in the cross-chain O(eq_pairs × indices) loop and
        /// the main per-select scan within one propagation call.
        resolve_base: HashMap<(TermId, TermId), Rc<ResolveBaseMemo>>,
        /// Whole-output memo of `select_alias_diseq_candidate_pairs()`
        /// (#7956): pure function of `diseq_set` / `select_cache` / `eq_adj` /
        /// `assigns` / shadow union-find, all frozen in the window; the
        /// generator sorts + dedups its output, so a hit is byte-identical.
        alias_diseq_pairs: Option<Rc<[(TermId, TermId)]>>,
        /// Per-start asserted-edge BFS predecessor forest (#k1-explain-memo):
        /// `start -> (node -> (parent, via_eq_term))` over asserted (non-
        /// sentinel, assigned-true) equality edges. BFS discovery order is
        /// deterministic, and a prefix of the traversal is unaffected by when
        /// the search would have early-exited, so a path reconstructed from
        /// this forest is byte-identical to the legacy per-goal early-exit
        /// BFS (`asserted_equality_path_bfs`). Frozen-graph window only.
        asserted_prev: HashMap<TermId, SharedAssertedPredecessors>,
    }

    thread_local! {
        static CACHE: RefCell<Option<Tables>> = const { RefCell::new(None) };
    }

    pub(crate) fn get_paths(start: TermId) -> Option<Rc<PathMap>> {
        CACHE.with(|c| {
            c.borrow()
                .as_ref()
                .and_then(|t| t.paths.get(&start).cloned())
        })
    }
    pub(crate) fn put_paths(start: TermId, paths: &Rc<PathMap>) {
        CACHE.with(|c| {
            if let Some(t) = c.borrow_mut().as_mut() {
                t.paths.insert(start, paths.clone());
            }
        });
    }

    /// Cached `explain_distinct_if_provable(a, b)` result, if warm. The outer
    /// `Option` is cache presence; the inner `PairReason` is the memoized value.
    pub(crate) fn get_distinct(a: TermId, b: TermId) -> Option<PairReason> {
        CACHE.with(|c| {
            c.borrow()
                .as_ref()
                .and_then(|t| t.distinct.get(&(a, b)).cloned())
        })
    }
    pub(crate) fn put_distinct(a: TermId, b: TermId, reason: &PairReason) {
        CACHE.with(|c| {
            if let Some(t) = c.borrow_mut().as_mut() {
                t.distinct.insert((a, b), reason.clone());
            }
        });
    }

    pub(crate) fn get_equal(a: TermId, b: TermId) -> Option<PairReason> {
        CACHE.with(|c| {
            c.borrow()
                .as_ref()
                .and_then(|t| t.equal.get(&(a, b)).cloned())
        })
    }
    pub(crate) fn put_equal(a: TermId, b: TermId, reason: &PairReason) {
        CACHE.with(|c| {
            if let Some(t) = c.borrow_mut().as_mut() {
                t.equal.insert((a, b), reason.clone());
            }
        });
    }

    pub(crate) fn get_candidate_pairs() -> Option<Rc<[(TermId, TermId)]>> {
        CACHE.with(|c| c.borrow().as_ref().and_then(|t| t.candidate_pairs.clone()))
    }
    pub(crate) fn put_candidate_pairs(pairs: &Rc<[(TermId, TermId)]>) {
        CACHE.with(|c| {
            if let Some(t) = c.borrow_mut().as_mut() {
                t.candidate_pairs = Some(pairs.clone());
            }
        });
    }

    pub(crate) fn get_selects_by_array() -> Option<Rc<HashMap<TermId, Vec<TermId>>>> {
        CACHE.with(|c| c.borrow().as_ref().and_then(|t| t.selects_by_array.clone()))
    }

    /// `Some(Some(forest))` on a warm hit, `Some(None)` when the window is
    /// active but cold for `start`, `None` when no window is active.
    #[allow(clippy::option_option)]
    pub(crate) fn get_asserted_prev(start: TermId) -> Option<Option<SharedAssertedPredecessors>> {
        CACHE.with(|c| {
            c.borrow()
                .as_ref()
                .map(|t| t.asserted_prev.get(&start).cloned())
        })
    }
    pub(crate) fn put_asserted_prev(start: TermId, prev: &SharedAssertedPredecessors) {
        CACHE.with(|c| {
            if let Some(t) = c.borrow_mut().as_mut() {
                t.asserted_prev.insert(start, prev.clone());
            }
        });
    }
    pub(crate) fn put_selects_by_array(map: &Rc<HashMap<TermId, Vec<TermId>>>) {
        CACHE.with(|c| {
            if let Some(t) = c.borrow_mut().as_mut() {
                t.selects_by_array = Some(map.clone());
            }
        });
    }

    /// `Some(Some(payload))`/`Some(None)` on a warm hit (found / miss result),
    /// `None` when the window is inactive or cold for this key.
    #[allow(clippy::option_option)]
    pub(crate) fn get_store_through(
        term: TermId,
        skip_sentinels: bool,
    ) -> Option<Option<Rc<StoreThroughMemo>>> {
        CACHE.with(|c| {
            c.borrow()
                .as_ref()
                .and_then(|t| t.store_through.get(&(term, skip_sentinels)).cloned())
        })
    }
    pub(crate) fn put_store_through(
        term: TermId,
        skip_sentinels: bool,
        found: &Option<Rc<StoreThroughMemo>>,
    ) {
        CACHE.with(|c| {
            if let Some(t) = c.borrow_mut().as_mut() {
                t.store_through
                    .insert((term, skip_sentinels), found.clone());
            }
        });
    }

    /// Cached `resolve_select_base_for_propagation_with_reasons(array, index)`
    /// payload, if warm. `None` when the window is inactive or cold for the key.
    pub(crate) fn get_resolve_base(array: TermId, index: TermId) -> Option<Rc<ResolveBaseMemo>> {
        CACHE.with(|c| {
            c.borrow()
                .as_ref()
                .and_then(|t| t.resolve_base.get(&(array, index)).cloned())
        })
    }
    pub(crate) fn put_resolve_base(array: TermId, index: TermId, payload: &Rc<ResolveBaseMemo>) {
        CACHE.with(|c| {
            if let Some(t) = c.borrow_mut().as_mut() {
                t.resolve_base.insert((array, index), payload.clone());
            }
        });
    }

    pub(crate) fn get_alias_diseq_pairs() -> Option<Rc<[(TermId, TermId)]>> {
        CACHE.with(|c| {
            c.borrow()
                .as_ref()
                .and_then(|t| t.alias_diseq_pairs.clone())
        })
    }
    pub(crate) fn put_alias_diseq_pairs(pairs: &Rc<[(TermId, TermId)]>) {
        CACHE.with(|c| {
            if let Some(t) = c.borrow_mut().as_mut() {
                t.alias_diseq_pairs = Some(pairs.clone());
            }
        });
    }

    /// Arm caching for the guard's lifetime; the previous state is restored on
    /// drop (nesting-safe, exception-safe).
    #[must_use]
    pub(crate) fn activate() -> Guard {
        let prev = CACHE.with(|c| c.borrow_mut().replace(Tables::default()));
        Guard { prev }
    }

    /// Arm caching only when no window is currently active (#7956). Nested
    /// `activate()` is safe but discards the outer window's warm entries for
    /// the inner scope; call sites that may run inside an existing window use
    /// this variant so an already-armed window is reused as-is.
    #[must_use]
    pub(crate) fn activate_if_inactive() -> Option<Guard> {
        let already_active = CACHE.with(|c| c.borrow().is_some());
        if already_active {
            None
        } else {
            Some(activate())
        }
    }

    pub(crate) struct Guard {
        prev: Option<Tables>,
    }

    impl Drop for Guard {
        fn drop(&mut self) {
            let prev = self.prev.take();
            CACHE.with(|c| *c.borrow_mut() = prev);
        }
    }
}

/// `(version, class-by-member)` memo for `equiv_class_shared()`; see the
/// `lazy_equiv_classes` field.
type LazyEquivClassMemo = RefCell<(Option<u64>, HashMap<TermId, Rc<[TermId]>>)>;

/// Array theory solver
///
/// Implements McCarthy's theory of arrays with the following axioms:
/// 1. ROW1 (read-over-write same): select(store(a, i, v), i) = v
/// 2. ROW2 (read-over-write diff): i ≠ j → select(store(a, i, v), j) = select(a, j)
/// 3. Extensionality: a ≠ b → ∃i. select(a, i) ≠ select(b, i)
/// 4. Select-map: select(map[f](a1,...,an), i) = f(select(a1,i),...,select(an,i))
pub struct ArraySolver<'a> {
    /// Reference to the term store
    terms: &'a TermStore,
    /// Current assignments: term -> bool
    assigns: HashMap<TermId, bool>,
    /// Trail for backtracking: (term, previous_value)
    trail: Vec<(TermId, Option<bool>)>,
    /// Scope markers (trail positions)
    scopes: Vec<usize>,
    /// Cache of select terms: select_term -> (array, index)
    select_cache: HashMap<TermId, (TermId, TermId)>,
    /// Exact select lookup: `(array_term, index_term) -> select_term`.
    /// Used by hot ROW2/self-store paths to avoid rescanning `parent_selects`
    /// when they need the syntactic `select(array, index)` term.
    select_pair_index: HashMap<(TermId, TermId), TermId>,
    /// Cache of store terms: store_term -> (array, index, value)
    store_cache: HashMap<TermId, (TermId, TermId, TermId)>,
    /// Cache of const-array terms: const_array_term -> default_value
    const_array_cache: HashMap<TermId, TermId>,
    /// Cache of map terms: map_term -> (func_name, array_args)
    /// Tracks `map[f](a1, ..., an)` terms for select-map axiom generation.
    /// Z3 ref: theory_array_full.cpp:43 (`add_map`) and :458 (`instantiate_select_map_axiom`)
    map_cache: HashMap<TermId, (String, Vec<TermId>)>,
    /// Cache of as-array terms: as_array_term -> func_name
    /// Tracks `as-array[f]` terms for select-as-array axiom generation through
    /// equality aliases (#8598).
    /// Z3 ref: theory_array_full.cpp:637-666 (`instantiate_select_as_array_axiom`)
    as_array_cache: HashMap<TermId, String>,
    /// Cache of default terms: array_arg -> default_term
    /// Tracks `default(array)` terms for event-driven default-const axiom
    /// generation through equality aliases (#8598).
    /// When `default(a)` exists and `a =_E const-array(v)`, the axiom
    /// `default(a) = v` must fire.
    default_cache: HashMap<TermId, TermId>,
    /// Event-driven select-map axiom candidates: `(select_term, map_term)`.
    /// Populated when a select reads from a map term or when a map term
    /// gains a parent select via equality. Drained in `check_select_map()`.
    /// Cleared on `pop()` and `clear_term_caches()`.
    pending_select_map: DedupQueue<(TermId, TermId)>,
    /// Event-driven select-as-array axiom candidates: `(select_term, as_array_term)`.
    /// Populated when a select reads from an as-array term or when an as-array
    /// term gains a parent select via equality (#8598). Drained in
    /// `check_select_as_array()`. Cleared on `pop()` and `clear_term_caches()`.
    pending_select_as_array: DedupQueue<(TermId, TermId)>,
    /// Event-driven default-const axiom candidates: `(default_term, const_array_term)`.
    /// Populated when `default(a)` is registered and `a` is a const-array, or
    /// when a const-array becomes equal to an array that has a default term
    /// (#8598). Drained in `check_default_const()`.
    /// Cleared on `pop()` and `clear_term_caches()`.
    pending_default_const: DedupQueue<(TermId, TermId)>,
    /// Equality terms we track: eq_term -> (lhs, rhs)
    equality_cache: HashMap<TermId, (TermId, TermId)>,
    /// Reverse index: term -> equality terms involving that term.
    /// Maintained in sync with `equality_cache` for O(1) lookup in
    /// `register_store` (#6820).
    term_to_equalities: HashMap<TermId, Vec<TermId>>,
    /// Dirty flag for a full cache rebuild.
    ///
    /// Set only when the STRUCTURAL caches (`select_cache`, `store_cache`,
    /// `equality_cache`, `term_to_equalities`, `eq_pair_index`, …) must be
    /// wiped and rebuilt from scratch — i.e. `reset()` and (defensively) term
    /// growth. **Not** set by `pop()`: those caches are pure functions of the
    /// immutable, monotonic `TermStore` and are therefore pop-invariant. See
    /// `var_layer_dirty` for the assignment/merge-derived layer that a `pop`
    /// actually invalidates (M1 persistent-structural-registration campaign).
    dirty: bool,
    /// Dirty flag for the assignment/merge-derived array-var layer.
    ///
    /// `pop()` sets this instead of `dirty`: on backtrack, `array_vars` merges
    /// (`array_var_merge_log`) and the event-driven `pending_*` queues must be
    /// rebuilt from the persisted structural caches via `replay_var_layer()`,
    /// but the structural caches themselves are kept intact. Cleared once the
    /// replay runs in `populate_caches()`.
    var_layer_dirty: bool,
    /// Term ids whose registration produces array-var / event-queue effects
    /// (select, store, map, as-array, lambda-array, default, and equality
    /// terms). Append-only structural index built during term registration and
    /// replayed by `replay_var_layer()` to rebuild the assignment/merge layer
    /// after a `pop()` without re-scanning the whole term store. Cleared only
    /// by `clear_term_caches()` / `reset()`.
    var_layer_terms: Vec<TermId>,
    /// Number of terms already scanned into the term caches.
    populated_terms: usize,
    /// Optional reachable-term scope seeded from registered atoms.
    ///
    /// When enabled, cache population indexes only terms transitively reachable
    /// from atoms registered through `TheorySolver::register_atom()`. This lets
    /// combined incremental routes ignore dead terms that remain in the
    /// append-only `TermStore` after earlier `check-sat-assuming` calls.
    registered_term_scope: Option<HashSet<TermId>>,
    /// Per-array incremental tracking for ROW2 registration (#6282 packet 1).
    array_vars: HashMap<TermId, ArrayVarData>,
    /// Equality-driven `array_vars` merges performed by `notify_equality`.
    /// Replayed in debug invariant checks so `array_vars` can legitimately be
    /// richer than the raw structural term caches after cross-theory equality
    /// notifications (#6703).
    array_var_merge_log: Vec<(TermId, TermId)>,
    /// Invertible undo record parallel to `array_var_merge_log`: for each merge
    /// (`target`, prior lengths of `target`'s three append-only vecs, prior
    /// `prop_upward`). `merge_array_var_data` only ever appends to the end of
    /// those vecs, so a merge is undone by truncating each vec back to its
    /// recorded length and restoring `prop_upward` — O(1)-invertible, the same
    /// discipline as the union-find trail. Lets `array_vars` persist across
    /// `pop()` (structural base kept; only the popped scope's merges undone)
    /// instead of being wiped and rebuilt (M1 persistent-registration).
    array_var_merge_undo: Vec<ArrayVarMergeUndo>,
    /// Marks into `array_var_merge_log` at each `push()`, so `pop()` undoes
    /// exactly the merges recorded in the scope being left.
    array_var_merge_scopes: Vec<usize>,
    /// Deduplicates repeated ROW2 registrations by `(store_term, select_index)`.
    axiom_fingerprints: HashSet<(TermId, TermId)>,
    /// Exact ROW2 fingerprint indices recorded per store term.
    ///
    /// Unlike Z3's enode-root fingerprints, these remain exact `TermId`s so a
    /// fingerprint inserted under a branch-local equality does not suppress a
    /// distinct-index branch after backtracking. `queue_row2_down_axiom()`
    /// consults the current equality graph against this exact history to avoid
    /// re-queuing alias-equivalent ROW2 work.
    row2_fingerprint_indices: HashMap<TermId, Vec<TermId>>,
    /// Incrementally registered ROW2 work. Packet 2 consumes this queue.
    pending_axioms: Vec<PendingAxiom>,
    /// Axioms blocked on missing equality atoms. Moved back to `pending_axioms`
    /// only when new terms are created (`populated_terms` increases), since new
    /// equality atoms can only appear via term registration (#6820).
    blocked_axioms: Vec<PendingAxiom>,
    /// The `populated_terms` count when `blocked_axioms` were last examined.
    /// If `populated_terms == blocked_axiom_term_gen`, blocked axioms are
    /// still blocked and need not be re-examined.
    blocked_axiom_term_gen: usize,
    /// Event-driven const-array read candidates: `(select_term, const_array_term)`.
    /// Populated in `register_select()` and `notify_equality()`.
    /// Drained in `check_const_array_read()` instead of scanning `select_cache`.
    pending_const_reads: DedupQueue<(TermId, TermId)>,
    /// Event-driven ROW1 (read-hit) candidates: `(select_term, store_term)`.
    /// Populated at the same three points as ROW2 down axioms:
    /// - `register_select()`: select's syntactic array has `stores_as_result`
    /// - `register_store()`: store term has existing `parent_selects`
    /// - `notify_equality()`: cross-product of merged equivalence classes
    ///
    /// Drain semantics: on each `check_row1()`, drain the queue. Pairs where
    /// indices are equal but no conflict is detected yet (because the
    /// disequality on values hasn't been propagated) are RETAINED for future
    /// re-checking. Pairs with non-matching indices are discarded (handled by
    /// ROW2). Cleared on `pop()` and `clear_term_caches()`.
    pending_row1: DedupQueue<(TermId, TermId)>,
    /// Event-driven ROW2 upward (axiom 2b) candidates: `(select_term, store_term)`.
    /// Populated at the same three points as other event-driven queues:
    /// - `register_select()`: select's array has `parent_stores` (upward direction)
    /// - `register_store()`: store's base array has existing `parent_selects`
    /// - `notify_equality()`: cross parent_stores × parent_selects
    ///
    /// ROW2 upward propagates selects from base arrays "up" to store results:
    /// `select(A, j) = select(store(A,i,v), j)` when `i ≠ j`.
    /// Drained in `check_row2_upward_with_guidance()` instead of scanning
    /// `select_cache`. Cleared on `pop()` and `clear_term_caches()`.
    pending_row2_upward: DedupQueue<(TermId, TermId)>,
    /// Event-driven self-store candidates: `(eq_term, store_term)`.
    /// Populated when an equality involving a store term is assigned true
    /// (`record_assignment`) or when a new store/equality is registered.
    /// `check_self_store()` drains this queue instead of scanning
    /// `equality_cache`. Cleared on `pop()` and `clear_term_caches()`.
    pending_self_store: Vec<(TermId, TermId)>,
    /// Event-driven store chain resolution candidates: `(select_term)`.
    /// Populated when a select is registered on a store chain
    /// (`register_select`, `register_store`, `notify_equality`).
    /// `check_store_chain_resolution()` drains this queue instead of
    /// scanning `select_cache`. Cleared on `pop()` and `clear_term_caches()`.
    pending_store_chain: DedupQueue<TermId>,
    /// Event-driven conflicting store equality candidates: `(store1, store2)`.
    /// Populated when two stores become equal via `notify_equality` or
    /// `record_assignment`. `check_conflicting_store_equalities()` drains
    /// this queue instead of scanning `store_cache`. Cleared on `pop()` and
    /// `clear_term_caches()`.
    pending_conflicting_stores: DedupQueue<(TermId, TermId)>,
    /// Event-driven array equality check candidates: `(eq_term, lhs, rhs)`.
    /// Populated when an array equality is asserted true. `check_array_equality()`
    /// drains this queue instead of scanning `equality_cache`. Cleared on `pop()`
    /// and `clear_term_caches()`.
    pending_array_eqs: Vec<(TermId, TermId, TermId)>,
    /// Permanent theory lemmas already applied to the SAT solver.
    applied_theory_lemmas: HashSet<Vec<TheoryLit>>,
    /// When true, expensive O(n²) checks (ROW2 upward, ROW2 extended, nested
    /// select conflicts) are deferred from `check()` to `final_check()`. Set by
    /// combined solvers that call `final_check()` at fixpoint (#6282 Packet 2).
    defer_expensive_checks: bool,
    /// Deduplicates NeedModelEquality requests from `check_row2_upward_with_guidance`.
    /// Prevents the same undecided index pair from being requested repeatedly,
    /// which would cause an infinite loop in the N-O fixpoint (#6282 Phase A).
    /// Cleared on `soft_reset()`.
    requested_model_eqs: HashSet<(TermId, TermId)>,
    /// Deduplicates interface equality requests from `check_interface_equalities`.
    /// Prevents the same array pair from being requested repeatedly across
    /// final_check calls. Uses equivalence class roots as keys so that pairs
    /// already in the same class are never re-requested.
    /// Persists across both `pop()` and `reset()` (#8594: reset() deliberately
    /// keeps this convergence dedup set so import/export persistence survives
    /// the split loop's reset; see theory_impl.rs). Soft-capped in
    /// `theory_check.rs` to bound growth on long incremental sessions.
    /// Reference: Z3 `mk_interface_eqs` in `theory_array_base.cpp:554-582`.
    requested_interface_eqs: HashSet<(TermId, TermId)>,
    /// Exact ROW2/model-equality obligations already emitted.
    ///
    /// This is narrower than `requested_model_eqs`: it records the structural
    /// store/select witness plus reasons that produced the request. It prevents
    /// repeated exact-select witness exploration from re-requesting the same
    /// obligation across model-equality/backtracking rounds (#8785).
    exact_select_model_eq_obligations: HashSet<ExactSelectModelEqObligation>,
    /// Stable exact-select obligation keys persisted across fresh solvers.
    exact_select_model_eq_keys: HashSet<ExactSelectModelEqKey>,
    /// Reason-carrying equality propagations already sent to EUF.
    sent_equality_replays: HashSet<ArrayPropagatedEqualityReplay>,
    /// Append-only discovery-order log of `sent_equality_replays`
    /// (#no-replay-quadratic): lets the combined solver export exact deltas
    /// via a cursor instead of cloning/rescanning the whole reason-carrying
    /// set every Nelson-Oppen iteration. Cleared together with the set.
    sent_equality_replay_log: Vec<ArrayPropagatedEqualityReplay>,

    // === Indexed data structures (rebuilt from equality_cache + assigns) ===
    /// `equality_cache` entries whose sides can possibly carry a select view,
    /// as a sorted `(eq_term, lhs, rhs)` vector. Rebuilt only when
    /// `populate_caches()` mutates the caches (dirty rebuild or newly
    /// registered terms). `propagate_impl()` runs once per BCP round and
    /// previously collected + sorted the whole map EVERY call — measured as
    /// a top self-time block on the QF_AX swap family (43k rounds × ~600
    /// entries).
    ///
    /// Filter soundness: a side yields a `SelectView` only when the side
    /// itself or an `eq_adj` neighbor is in `select_cache`; equality edges
    /// (both real eq atoms and cross-theory sentinel edges) only connect
    /// same-sorted terms, so an eq atom whose side sort has NO select-term
    /// with that sort provably produces zero views — the ROW2 loop body is a
    /// no-op for it (index-index and array-array equalities on flat-array
    /// problems). Iteration order for the survivors is identical to the old
    /// per-call sort (ascending eq term id), so propagation order — and
    /// thus determinism (#3060) — is unchanged.
    eq_select_entries_sorted: Vec<(TermId, TermId, TermId)>,
    /// Monotonic version of every input `propagate_impl()` reads: bumped on
    /// assignment changes, eq-graph changes, external (dis)equality
    /// injection, and cache rebuilds. See `bump_propagate_state_version`.
    propagate_state_version: u64,
    /// `propagate_state_version` at the last COMPLETED (uninterrupted)
    /// `propagate_impl()` scan. When the version is unchanged, the rescan
    /// would recompute exactly the propagations already recorded in
    /// `sent_propagations` and return the empty set — so it is skipped.
    last_full_scan_version: Option<u64>,
    /// Map from unordered term pair to equality term: {min(a,b), max(a,b)} -> eq_term
    eq_pair_index: HashMap<(TermId, TermId), TermId>,
    /// Set of unordered term pairs asserted distinct: {min(a,b), max(a,b)}
    diseq_set: HashSet<(TermId, TermId)>,
    /// Adjacency list for true equalities: term -> [(other_term, eq_term)]
    eq_adj: HashMap<TermId, Vec<(TermId, TermId)>>,
    /// Whether the assignment-derived indices need a full rebuild.
    assign_dirty: bool,
    /// Debug-only tripwire: set whenever the assignment/equality layer
    /// (`eq_adj` / `shadow_uf` / `diseq_set`) is mutated incrementally outside a
    /// full `rebuild_assign_indices()`. Drives the mandatory
    /// `debug_assignment_layer_matches_full_rebuild()` oracle in
    /// `populate_caches()` so the incremental warm path is verified byte-for-
    /// byte against a from-scratch recompute on every call that changed it.
    #[cfg(debug_assertions)]
    eq_layer_touched_since_populate: bool,
    /// Equality atoms assigned before `register_term()` sees them while the
    /// caches are otherwise warm. Drained after the next incremental term scan
    /// so `eq_adj` / `diseq_set` can be updated without a full rebuild.
    pending_registered_equalities: Vec<TermId>,
    /// Monotonic version for equality-graph connectivity updates.
    /// Bumped only when `eq_adj`'s connected components can change.
    eq_adj_version: u64,
    /// External disequalities injected by the combined solver (e.g., from LIA).
    /// These survive `rebuild_assign_indices()` and are merged into `diseq_set` (#4665).
    external_diseqs: HashSet<(TermId, TermId)>,
    /// Reason-carrying external disequalities from arithmetic tight bounds (#6546).
    /// When present, `explain_distinct_if_provable()` can justify ROW2 store-chain
    /// skips for these pairs. Only non-empty, deduplicated reason vectors are stored.
    external_diseq_reasons: HashMap<(TermId, TermId), Vec<TheoryLit>>,
    /// External equalities injected by the combined solver (e.g., from LIA).
    /// These survive `rebuild_assign_indices()` and are merged into `eq_adj` (#4665).
    external_eqs: Vec<(TermId, TermId)>,
    /// SAT-visible reasons for reason-carrying external equalities.
    ///
    /// Store-chain walkers may traverse sentinel `external_eqs` edges only when
    /// they can add these guards to any conflict lemma that depends on the edge.
    external_eq_reasons: HashMap<(TermId, TermId), Vec<TheoryLit>>,
    /// Equalities already reported via `propagate_equalities()`.
    /// Prevents the N-O fixpoint loop from re-discovering the same equality
    /// every iteration (#5121). Cleared on `pop()`.
    sent_equalities: HashSet<(TermId, TermId)>,
    /// Propagations already emitted in the current scope.
    /// Prevents the eager theory extension from re-processing the exact same
    /// implication clause on every call when the justification has not changed.
    sent_propagations: HashSet<(TheoryLit, Vec<TheoryLit>)>,
    // Per-theory runtime statistics (#4706)
    check_count: u64,
    conflict_count: u64,
    propagation_count: u64,
    /// ROW2 scan diagnostics: scans executed (version fast-path missed).
    scan_count: u64,
    /// ROW2 scan diagnostics: entries re-derived across all scans.
    scan_entry_visits: u64,
    /// ROW2 scan diagnostics: inner view-triple iterations across all scans.
    scan_view_iters: u64,
    /// ROW2 dirty-entry scanning (see `theory_propagate.rs` module docs):
    /// true = every entry must be re-derived on the next scan. Starts true.
    row2_all_dirty: bool,
    /// Entry indices woken since the last scan (deduped via the flag vector).
    row2_dirty_entries: Vec<u32>,
    /// Parallel dedup flags; kept sized to `eq_select_entries_sorted`.
    row2_entry_is_dirty: Vec<bool>,
    /// Reverse dependency index: watched term/atom -> watching entries with
    /// their wake masks (see `theory_propagate::wake_mask`). May hold stale
    /// registrations (spurious wakes are harmless); rebuilt from scratch by
    /// every full scan and on structural invalidation.
    row2_watch: HashMap<TermId, Vec<(u32, u8)>>,
    /// Per-entry dependency sequence from its last derivation, exactly as
    /// recorded (unsorted, may repeat). Registration is skipped when a
    /// rescan reproduces the identical sequence — the dominant case.
    row2_entry_watches: Vec<Vec<(TermId, u8)>>,
    /// Total registrations in `row2_watch` (growth cap trigger).
    row2_watch_registrations: usize,
    /// Count of dead fingerprint entries removed by `gc_dead_fingerprints()`.
    fingerprint_gc_removed: u64,
    /// M0 (SELECT-PAIRS blueprint): `select_conflict_candidate_pairs()` call
    /// count. `Cell` because the generator runs on `&self` query paths.
    candidate_pairs_calls: Cell<u64>,
    /// M0: total candidate pairs produced by fresh (non-memoized) generations.
    candidate_pairs_generated: Cell<u64>,
    /// M0: calls served from the window memo (D1).
    candidate_pairs_memo_hits: Cell<u64>,
    /// Cached equivalence class map for the current `eq_adj_version`.
    /// Reused across repeated `check()` / `final_check()` calls until the
    /// equality graph connectivity changes.
    equiv_class_map: HashMap<TermId, usize>,
    /// Cached equivalence class members for the current `eq_adj_version`.
    equiv_classes: Vec<Vec<TermId>>,
    /// `eq_adj_version` that last populated `equiv_class_map` / `equiv_classes`.
    equiv_class_cache_version: Option<u64>,
    /// Lazy per-class equivalence cache for `equiv_class_shared()`.
    ///
    /// `(version, class-by-member)` memo filled on demand by BFS: one BFS per
    /// QUERIED class per `eq_adj_version`, shared across all class members via
    /// `Rc`. Unlike the full `build_equiv_class_cache()` rebuild (O(graph) per
    /// version bump — too hot for `notify_equality`, which runs once per
    /// cross-theory equality assertion), the cost here is proportional to the
    /// classes actually queried. Interior mutability keeps the read-only
    /// query surface (`row2_fingerprint_seen` & co.) on `&self`.
    lazy_equiv_classes: LazyEquivClassMemo,
    /// Scratch memo for `pair_is_decided(a, b)` — whether an index pair is
    /// same-class OR known-distinct OR affine-distinct. Pure function of the
    /// current theory state, which is CONSTANT within a single `final_check()`
    /// pass (equiv classes / diseq set are only mutated between passes). The
    /// store-chain interface-equality guards evaluate this predicate millions
    /// of times over only ~thousands of distinct index pairs (storecomm SAT
    /// benchmarks), so memoizing collapses the redundant recompute. Cleared at
    /// the top of every `final_check()` so no entry can outlive the state it
    /// was computed under.
    pairwise_decided_cache: RefCell<HashMap<(TermId, TermId), bool>>,
    /// Scratch memo for `store_chain_indices_are_decided`, keyed by the
    /// sorted+deduped merged index set. Store-commutativity SAT benchmarks call
    /// this predicate thousands of times over the SAME handful of index sets
    /// (commuted store chains share their index universe), so caching by set
    /// collapses the O(sets²·k²) work to O(distinct-sets·k²). Same lifetime
    /// invariant as `pairwise_decided_cache`: cleared at each `final_check`.
    store_chain_decided_cache: RefCell<HashMap<Vec<TermId>, bool>>,
    #[cfg(test)]
    /// Regression-only counter used to assert that repeated `check()` calls do
    /// not rebuild the equivalence cache when the equality graph is unchanged.
    equiv_class_cache_builds: u64,
    #[cfg(test)]
    /// Regression-only counter used to assert that warm-cache equality updates
    /// do not force full `eq_adj` / `diseq_set` reconstruction.
    assign_index_rebuilds: u64,
    /// Snapshot of `(eq_adj_version, select_cache.len(), store_cache.len(),
    /// external_diseqs.len(), external_eqs.len(), diseq_set.len())` at the last
    /// `propagate_equalities()` call. When the snapshot matches the current
    /// state, the method short-circuits to an empty result because no new
    /// equalities can be discovered (#6546).
    prop_eq_snapshot: Option<(u64, usize, usize, usize, usize, usize)>,
    /// Snapshot of `(eq_adj_version, diseq_set.len(), select_cache.len(),
    /// store_cache.len(), requested_model_eqs.len(), requested_interface_eqs.len())`
    /// at the last `final_check()` call that returned `Sat` (all sub-checks passed).
    /// When the snapshot matches the current state, `final_check` short-circuits
    /// because no new conflicts, lemmas, or model equality requests can be
    /// discovered (#6546).
    final_check_snapshot: Option<(u64, usize, usize, usize, usize, usize)>,
    final_check_call_count: u64,
    /// Memoized affine Int normal forms + canonical interning, keyed by the
    /// immutable term DAG.
    ///
    /// The parse result depends only on `terms`, not on solver assignments, so
    /// it is safe to retain across scopes, repeated `propagate()` calls, AND
    /// across the fresh-`ArraySolver`-per-refinement-round recreation. The
    /// cache is shared (`Rc`) so the check_sat outer loop can hand the same
    /// instance to each freshly built solver (see `adopt_affine_cache`). It
    /// carries no solver-assignment or lemma-reason content — purely the
    /// structural affine form of each `TermId` — so cross-round persistence is
    /// byte-identical to recompute.
    affine_cache: Rc<AffineCache>,
    /// Shadow weak-equivalence graph (Christ/Hoenicke), version-keyed cache.
    ///
    /// M1 of the weak-equivalence campaign: validation-only structure backing
    /// debug asserts and unit tests; no effect on solving behavior. Rebuilt
    /// when `eq_adj_version` bumps or store/external-edge caches grow
    /// (see weak_equiv.rs).
    weak_equiv_cache: RefCell<Option<weak_equiv::WeakEquivCacheEntry>>,
    /// Shadow backtrackable union-find over the equality graph (M1 of the
    /// union-find arrays campaign, see union_find.rs). Fed from the same
    /// three writer sites as `eq_adj`; `eq_adj` remains the source of truth.
    /// Validated against the BFS equivalence classes by
    /// `#[cfg(debug_assertions)]` invariants; no effect on solving behavior.
    shadow_uf: union_find::ArrayUnionFind,
    /// Whether `shadow_uf` no longer mirrors `eq_adj` and must be rebuilt
    /// before consistency checks. Set on the out-of-order equality-retraction
    /// path (edge removal/replacement cannot be expressed as a union) and
    /// cleared by `rebuild_shadow_uf()`. The `assign_dirty` full-rebuild path
    /// (pop/reset/cold assignments) also leaves the shadow stale until
    /// `rebuild_assign_indices()` reconstructs both in lockstep.
    shadow_uf_stale: bool,
    /// External interrupt flag for cooperative cancellation (#8615).
    ///
    /// When set, the array solver periodically checks this flag during
    /// long-running propagation loops (propagate_equalities, propagate,
    /// check) and returns early if interrupted. This allows `set_timeout()`
    /// and `interrupt()` to take effect during array theory solving, rather
    /// than only between theory solver calls.
    interrupt: Option<Arc<AtomicBool>>,
    /// Hard wall-clock deadline pushed down from the caller
    /// (#array-deadline-forward, mirroring `LiaSolver::set_deadline` #8749).
    ///
    /// The Nelson-Oppen driver only polls its own deadline BETWEEN theory
    /// checks, so a single dense `final_check` (the O(pairs x graph)
    /// `check_row2_extended` explain loop) could overshoot the caller's wall
    /// budget by tens of seconds (measured: a QF_AX storecomm subset re-solve
    /// under an ~8.7s slice ran 40+s inside one final_check until an external
    /// watchdog killed the already-answered run). `interrupted_or_deadline`
    /// polls this at sub-check boundaries and amortized inside the pair
    /// loops, so the check exits `Unknown` at the boundary — fail-closed,
    /// verdict-neutral by construction.
    deadline: Option<ay_core::time::Instant>,
}

pub(crate) type AffineIntExpr = (HashMap<TermId, BigInt>, BigInt);

/// Shared, pop-invariant memo for affine Int normal forms.
///
/// Every field is a pure function of the immutable `TermStore` term DAG and
/// carries no solver assignments or lemma-reason content, so it is safe to
/// share across the fresh-`ArraySolver`-per-round recreation and to retain
/// across structural rebuilds (`clear_term_caches`) and push/pop. This is the
/// key distinction from equality-reason-path memos: affine forms are not reason
/// paths, so no staleness key is required.
///
/// `interner` assigns each *canonical* affine variable-map (sorted exact
/// `(TermId, coeff)` vector, zero coeffs already dropped) a dense `u32` id. Two
/// variable-maps receive the same id **iff** their canonical vectors compare
/// equal — the `HashMap` key equality is exact (not a hash digest), so the
/// interning is collision-free and byte-identical to a structural `HashMap`
/// compare. Equality of two affine forms then collapses to `id == id` on the
/// variable part plus a `BigInt` constant compare, replacing the pairwise
/// `HashMap<TermId, BigInt>` structural walk in `known_equal` /
/// `equal_by_affine_form` / `distinct_by_affine_offset`.
#[derive(Default)]
pub struct AffineCache {
    /// `TermId` -> parsed affine normal form (`None` = not an affine Int term).
    parse: RefCell<HashMap<TermId, Option<Rc<AffineIntExpr>>>>,
    /// `TermId` -> interned id of its affine variable-map (`None` mirrors a
    /// `None` parse). Memoizes the canonical-vector build + interner lookup so
    /// a term is interned at most once.
    varmap_ids: RefCell<HashMap<TermId, Option<u32>>>,
    /// Canonical affine variable-map (sorted `(TermId, coeff)`) -> dense `u32` id.
    interner: RefCell<HashMap<Vec<(TermId, BigInt)>, u32>>,
    /// Ordered `(t1, t2)` -> `distinct_by_affine_offset` result. Like every
    /// other field here it is a pure function of the immutable term DAG; the
    /// ROW2 probe loop hits the same pairs millions of times per solve
    /// (measured ~5% of a QF_AX swap solve in parse/canonical hash traffic).
    distinct_offset_pairs: RefCell<HashMap<(TermId, TermId), bool>>,
    /// `TermId` -> OPAQUE-LEAF affine form (`None` = nonlinear / non-Int).
    /// Unlike `parse` (which fails on UF-application leaves), every non-affine
    /// Int subterm is kept as an opaque leaf keyed by its `TermId`, so
    /// `(+ (seq_offset a) 1)` parses to `{leaf: seq_offset(a) -> 1}, +1`.
    /// Purely structural (term DAG only), so cross-round retention is sound
    /// exactly like `parse` (#7956 index-congruence).
    opaque_parse: RefCell<HashMap<TermId, Option<Rc<OpaqueAffineExpr>>>>,
}

/// Affine form over OPAQUE Int leaves: `(leaf -> coefficient, constant)`.
/// Leaves are arbitrary Int-sorted terms (UF applications, selects, vars)
/// keyed by `TermId` (the term store is hash-consed, so syntactic identity is
/// `TermId` identity).
pub(crate) type OpaqueAffineExpr = (HashMap<TermId, BigInt>, BigInt);

impl<'a> ArraySolver<'a> {
    /// Create a new array solver
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        ArraySolver {
            terms,
            assigns: HashMap::default(),
            trail: Vec::new(),
            scopes: Vec::new(),
            select_cache: HashMap::default(),
            select_pair_index: HashMap::default(),
            store_cache: HashMap::default(),
            const_array_cache: HashMap::default(),
            map_cache: HashMap::default(),
            as_array_cache: HashMap::default(),
            default_cache: HashMap::default(),
            pending_select_map: DedupQueue::default(),
            pending_select_as_array: DedupQueue::default(),
            pending_default_const: DedupQueue::default(),
            equality_cache: HashMap::default(),
            term_to_equalities: HashMap::default(),
            dirty: true,
            var_layer_dirty: false,
            var_layer_terms: Vec::new(),
            populated_terms: 0,
            registered_term_scope: None,
            array_vars: HashMap::default(),
            array_var_merge_log: Vec::new(),
            array_var_merge_undo: Vec::new(),
            array_var_merge_scopes: Vec::new(),
            axiom_fingerprints: HashSet::default(),
            row2_fingerprint_indices: HashMap::default(),
            pending_axioms: Vec::new(),
            blocked_axioms: Vec::new(),
            blocked_axiom_term_gen: 0,
            pending_const_reads: DedupQueue::default(),
            pending_row1: DedupQueue::default(),
            pending_row2_upward: DedupQueue::default(),
            pending_self_store: Vec::new(),
            pending_store_chain: DedupQueue::default(),
            pending_conflicting_stores: DedupQueue::default(),
            pending_array_eqs: Vec::new(),
            applied_theory_lemmas: HashSet::default(),
            defer_expensive_checks: false,
            requested_model_eqs: HashSet::default(),
            requested_interface_eqs: HashSet::default(),
            exact_select_model_eq_obligations: HashSet::default(),
            exact_select_model_eq_keys: HashSet::default(),
            sent_equality_replays: HashSet::default(),
            sent_equality_replay_log: Vec::new(),
            eq_select_entries_sorted: Vec::new(),
            propagate_state_version: 0,
            last_full_scan_version: None,
            eq_pair_index: HashMap::default(),
            diseq_set: HashSet::default(),
            eq_adj: HashMap::default(),
            assign_dirty: true,
            #[cfg(debug_assertions)]
            eq_layer_touched_since_populate: false,
            pending_registered_equalities: Vec::new(),
            eq_adj_version: 0,
            external_diseqs: HashSet::default(),
            external_diseq_reasons: HashMap::default(),
            external_eqs: Vec::new(),
            external_eq_reasons: HashMap::default(),
            sent_equalities: HashSet::default(),
            sent_propagations: HashSet::default(),
            check_count: 0,
            scan_count: 0,
            scan_entry_visits: 0,
            scan_view_iters: 0,
            row2_all_dirty: true,
            row2_dirty_entries: Vec::new(),
            row2_entry_is_dirty: Vec::new(),
            row2_watch: HashMap::default(),
            row2_entry_watches: Vec::new(),
            row2_watch_registrations: 0,
            conflict_count: 0,
            propagation_count: 0,
            fingerprint_gc_removed: 0,
            candidate_pairs_calls: Cell::new(0),
            candidate_pairs_generated: Cell::new(0),
            candidate_pairs_memo_hits: Cell::new(0),
            equiv_class_map: HashMap::default(),
            equiv_classes: Vec::new(),
            equiv_class_cache_version: None,
            lazy_equiv_classes: RefCell::new((None, HashMap::default())),
            pairwise_decided_cache: RefCell::new(HashMap::default()),
            store_chain_decided_cache: RefCell::new(HashMap::default()),
            #[cfg(test)]
            equiv_class_cache_builds: 0,
            #[cfg(test)]
            assign_index_rebuilds: 0,
            prop_eq_snapshot: None,
            final_check_snapshot: None,
            final_check_call_count: 0,
            affine_cache: Rc::new(AffineCache::default()),
            weak_equiv_cache: RefCell::new(None),
            shadow_uf: union_find::ArrayUnionFind::default(),
            shadow_uf_stale: true,
            interrupt: None,
            deadline: None,
        }
    }

    /// Share the affine normal-form / interning memo so a caller can persist it
    /// across fresh-`ArraySolver`-per-round recreation (see
    /// `adopt_affine_cache`). The memo is a pure function of the immutable
    /// `TermStore`, so the returned handle stays byte-identical-correct for the
    /// lifetime of that same `TermStore`.
    #[must_use]
    pub fn share_affine_cache(&self) -> Rc<AffineCache> {
        self.affine_cache.clone()
    }

    /// Adopt a shared affine memo built by an earlier round over the *same*
    /// `TermStore`. Because the memo carries no assignment/reason content and
    /// `TermId`s are stable and append-only within a solve, reusing it is
    /// byte-identical to recomputing every parse/intern from scratch — it only
    /// skips the redundant re-`parse_affine_int_expr` and re-interning.
    pub fn adopt_affine_cache(&mut self, cache: Rc<AffineCache>) {
        self.affine_cache = cache;
    }

    /// Set an external interrupt flag for cooperative cancellation (#8615).
    ///
    /// When set, the array solver checks this flag periodically during
    /// long-running propagation loops and returns early if the flag is
    /// set to `true`. This allows `set_timeout()` and `interrupt()` to
    /// take effect during array theory solving.
    pub fn set_interrupt(&mut self, flag: Arc<AtomicBool>) {
        self.interrupt = Some(flag);
    }

    /// Check whether the external interrupt flag has been set (#8615).
    ///
    /// Returns `true` if the interrupt flag exists and is set to `true`.
    /// Used for cooperative cancellation in hot loops.
    pub fn is_interrupted(&self) -> bool {
        self.interrupt
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
    }

    /// Install a hard wall-clock deadline (#array-deadline-forward; see the
    /// `deadline` field docs). Mirrors `LiaSolver::set_deadline` (#8749): the
    /// combiner forwards its own deadline here so a single dense
    /// `final_check` cannot overshoot the caller's wall budget.
    pub fn set_deadline(&mut self, deadline: ay_core::time::Instant) {
        self.deadline = Some(deadline);
    }

    /// Interrupt flag OR deadline poll for the expensive final-check /
    /// propagation loops (#array-deadline-forward).
    ///
    /// FAIL-CLOSED: every caller maps `true` to `TheoryResult::Unknown` (or
    /// returns the partial-but-sound lemma batch found so far) — a stop can
    /// only degrade completeness for THIS check round, never flip a verdict.
    /// The outer DPLL(T)/executor loops observe the same expired deadline at
    /// their own polls and abort with `Unknown(Timeout)`.
    pub fn interrupted_or_deadline(&self) -> bool {
        if self.is_interrupted() {
            return true;
        }
        self.deadline
            .is_some_and(|deadline| ay_core::time::Instant::now() >= deadline)
    }
}

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;
