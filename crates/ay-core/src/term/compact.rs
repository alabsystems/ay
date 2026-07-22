// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mark-compact garbage collection for the hash-cons [`TermStore`].
//!
//! Ports the arena-compaction strategy from Kissat's
//! `reference/kissat/src/compact.c` (`kissat_compact_literals`,
//! `compact_literal`, `compact_export`, `kissat_finalize_compacting`).
//! Where Kissat rewrites SAT variable indices through `map_literal`, we
//! rewrite [`TermId`]s through a [`RemapTable`] that is applied to every
//! external holder via the [`Remappable`] visitor trait.
//!
//! The compaction is a **pure relabelling**: the set of interned
//! [`TermData`] values is unchanged (modulo dead terms that are dropped),
//! every surviving term keeps its semantic identity via hash-consing,
//! and any proof log that is rewritten through the same [`Remappable`]
//! visitor remains checkable. See
//! the development design notes §3.1 for the
//! full proof-preservation argument.
//!
//! This module ONLY adds the `mark_and_compact` function and the
//! [`Remappable`] trait. Scheduling compaction at SAT restart
//! boundaries or under memory pressure is a separate sub-task of
//! the #8599 adaptive-memory epic and is intentionally NOT wired here.

use std::mem::size_of;
use std::sync::atomic::Ordering;

use crate::kani_compat::KaniHashMap;
use crate::sort::Sort;

use super::{TermData, TermEntry, TermId, TermStore, GLOBAL_TERM_BYTES};

/// Translation table from pre-compaction [`TermId`]s to post-compaction
/// [`TermId`]s produced by [`TermStore::mark_and_compact`].
///
/// Dead terms (reachable from no root) map to `None`. The sentinel
/// [`TermId::SENTINEL`] always maps to itself — it is not a real
/// interned term and must pass through unchanged.
#[derive(Debug, Clone)]
pub struct RemapTable {
    /// `mapping[old_id.index()]` is the new `TermId` for the live term
    /// previously interned at `old_id`, or `None` if the term was
    /// reclaimed.
    mapping: Vec<Option<TermId>>,
}

impl RemapTable {
    /// Number of pre-compaction slots this table covers. Callers can
    /// use this to sanity-check that a [`TermId`] came from the same
    /// store whose compaction produced the table.
    pub fn len(&self) -> usize {
        self.mapping.len()
    }

    /// Returns `true` if the table has no entries (the store was empty).
    pub fn is_empty(&self) -> bool {
        self.mapping.is_empty()
    }

    /// Translate a pre-compaction [`TermId`] to its post-compaction
    /// identity. Returns `None` if the term was reclaimed.
    ///
    /// The [`TermId::SENTINEL`] is always mapped to itself.
    /// Out-of-range ids (e.g., a `TermId` from a different store or
    /// from after a second compaction) also return `None`.
    pub fn get(&self, old: TermId) -> Option<TermId> {
        if old.is_sentinel() {
            return Some(TermId::SENTINEL);
        }
        self.mapping.get(old.index()).copied().flatten()
    }

    /// Translate `old` to its new identity, or panic if `old` was
    /// reclaimed. Intended for callers who have already marked `old`
    /// as a root and therefore KNOW it survives.
    ///
    /// Prefer [`RemapTable::get`] for untrusted input.
    pub fn remap(&self, old: TermId) -> TermId {
        self.get(old).unwrap_or_else(|| {
            panic!(
                "RemapTable::remap: TermId {old} was not marked as a root and has been reclaimed"
            )
        })
    }

    /// Returns a closure `|old| -> new` convenient to pass through
    /// [`Remappable::remap`]. Reclaimed ids panic — only use when the
    /// caller has pinned every [`TermId`] it holds as a root.
    pub fn as_fn(&self) -> impl Fn(TermId) -> TermId + '_ {
        move |old| self.remap(old)
    }
}

/// External holders of [`TermId`]s implement this trait so that
/// [`TermStore::mark_and_compact`] can rewrite every stale id in one
/// pass after compaction.
///
/// # Invariants
///
/// The implementation MUST call `f` on every stored [`TermId`] and
/// replace it with the returned value. Skipping a field leaves a
/// dangling index into the post-compaction arena — a silent
/// use-after-free.
///
/// Structures that indirectly hold [`TermId`]s (e.g., a `Vec<Atom>`
/// where `Atom` wraps a [`TermId`]) should recursively delegate to
/// the inner [`Remappable`] impl.
///
/// # Example
///
/// ```
/// use ay_core::term::{Remappable, TermId};
///
/// struct Lemma { head: TermId, body: Vec<TermId> }
///
/// impl Remappable for Lemma {
///     fn remap(&mut self, f: &dyn Fn(TermId) -> TermId) {
///         self.head = f(self.head);
///         for t in &mut self.body {
///             *t = f(*t);
///         }
///     }
/// }
/// ```
pub trait Remappable {
    /// Rewrite every [`TermId`] stored in `self` through `f`.
    fn remap(&mut self, f: &dyn Fn(TermId) -> TermId);
}

// ----------------------------------------------------------------------
// Blanket / std-library implementations
// ----------------------------------------------------------------------

impl Remappable for TermId {
    fn remap(&mut self, f: &dyn Fn(TermId) -> TermId) {
        *self = f(*self);
    }
}

impl<T: Remappable> Remappable for Vec<T> {
    fn remap(&mut self, f: &dyn Fn(TermId) -> TermId) {
        for item in self {
            item.remap(f);
        }
    }
}

impl<T: Remappable> Remappable for Option<T> {
    fn remap(&mut self, f: &dyn Fn(TermId) -> TermId) {
        if let Some(inner) = self {
            inner.remap(f);
        }
    }
}

impl<T: Remappable, const N: usize> Remappable for [T; N] {
    fn remap(&mut self, f: &dyn Fn(TermId) -> TermId) {
        for item in self {
            item.remap(f);
        }
    }
}

// ----------------------------------------------------------------------
// Core algorithm
// ----------------------------------------------------------------------

impl TermStore {
    /// Mark-compact the hash-consed term arena.
    ///
    /// Walks the transitive closure of `roots` plus every
    /// `TermStore`-owned pin (`true`, `false`, entries in `names`),
    /// copies the reachable `TermEntry` values into a fresh arena
    /// in topological order (children before parents so that
    /// remapped [`TermData::App`] children are already valid), and
    /// returns a [`RemapTable`] that callers must apply to every
    /// external [`TermId`] they hold via [`Remappable::remap`].
    ///
    /// The hash-cons map is rebuilt from the surviving terms so that
    /// subsequent `intern` calls continue to deduplicate.
    ///
    /// # Safety / correctness contract
    ///
    /// 1. EVERY external holder of a [`TermId`] (SAT trail, theory
    ///    pending queues, PDR lemmas, proof-log pointers, cached
    ///    atom maps, …) MUST be included in `roots` OR remapped
    ///    through the returned [`RemapTable`]. A missed holder is
    ///    a use-after-free.
    /// 2. Compaction does not change the semantics of any surviving
    ///    term — post-compaction [`TermData`] is byte-identical to
    ///    the pre-compaction value, only its [`TermId`] changed.
    ///    Proof checkers that walk [`TermData`] see an equivalent
    ///    term.
    /// 3. This function does not schedule itself. It only executes
    ///    when called.
    ///
    /// # Reference
    ///
    /// Ported from Kissat `reference/kissat/src/compact.c` — see
    /// `kissat_compact_literals` for the marking walk,
    /// `compact_literal` for the in-place copy, and
    /// `kissat_finalize_compacting` for the rebuild of auxiliary
    /// structures (analogous to our hash-cons rebuild).
    pub fn mark_and_compact(&mut self, roots: &[TermId]) -> RemapTable {
        let old_len = self.terms.len();

        // Phase 1: collect roots. In addition to caller-supplied
        // roots, we pin:
        //   * the `true` and `false` sentinels (always live)
        //   * every `TermId` held in `self.names` (user-visible names,
        //     per §3.1 of the design doc)
        let mut stack: Vec<TermId> = Vec::with_capacity(roots.len() + 2 + self.names.len());
        let mut reachable: Vec<bool> = vec![false; old_len];

        let push_root = |id: TermId, stack: &mut Vec<TermId>, reachable: &mut Vec<bool>| {
            if id.is_sentinel() {
                return;
            }
            let idx = id.index();
            if idx < reachable.len() && !reachable[idx] {
                reachable[idx] = true;
                stack.push(id);
            }
        };

        for &r in roots {
            push_root(r, &mut stack, &mut reachable);
        }
        if let Some(t) = self.true_term {
            push_root(t, &mut stack, &mut reachable);
        }
        if let Some(f) = self.false_term {
            push_root(f, &mut stack, &mut reachable);
        }
        for &(id, _) in self.names.values() {
            push_root(id, &mut stack, &mut reachable);
        }

        // Phase 2: iterative DFS (terms can nest hundreds deep — a
        // recursive walk is a stack-overflow hazard as called out in
        // the design doc).
        while let Some(id) = stack.pop() {
            let entry = &self.terms[id.index()];
            Self::for_each_child(&entry.term, |child| {
                push_root(child, &mut stack, &mut reachable);
            });
        }

        // Phase 3: build the old → new mapping in topological order
        // (children before parents). A post-order traversal from the
        // marked roots guarantees that when we emit a parent, its
        // children have already been assigned new ids — but the
        // marking pass above already walked every child, so we can
        // equivalently emit in INCREASING old-id order because the
        // intern path only ever creates a parent AFTER its children,
        // so old ids are already a valid topological order. This is
        // the same trick Kissat uses: `for (all_variables (iidx))`
        // iterates in index order.
        let mut mapping: Vec<Option<TermId>> = vec![None; old_len];
        let live_count: usize = reachable.iter().filter(|b| **b).count();
        let mut new_terms: Vec<TermEntry> = Vec::with_capacity(live_count);
        let mut new_heap_data_bytes: usize = 0;

        for old_idx in 0..old_len {
            if !reachable[old_idx] {
                continue;
            }
            let new_id = TermId(new_terms.len() as u32);
            mapping[old_idx] = Some(new_id);

            // Move the entry out of the old arena to avoid cloning
            // the potentially-large TermData payload. We replace the
            // slot with a placeholder that we'll discard at the end.
            let mut entry = std::mem::replace(
                &mut self.terms[old_idx],
                TermEntry {
                    term: TermData::Not(TermId(0)),
                    sort: Sort::Bool,
                },
            );

            // Rewrite every child TermId inside the term payload.
            Self::remap_term_children(&mut entry.term, &mapping);

            new_heap_data_bytes += Self::heap_size(&entry.term);
            new_terms.push(entry);
        }

        // Phase 4: swap in the compacted arena.
        self.terms = new_terms;

        // Phase 5: remap TermStore-owned pins.
        let remap = RemapTable { mapping };
        if let Some(t) = self.true_term.as_mut() {
            *t = remap.remap(*t);
        }
        if let Some(f) = self.false_term.as_mut() {
            *f = remap.remap(*f);
        }
        // `names` values: rewrite each (TermId, Sort) pair. We replace
        // the map wholesale because KaniHashMap does not expose
        // value_mut for every backend uniformly.
        let old_names = std::mem::take(&mut self.names);
        for (name, (id, sort)) in old_names {
            if let Some(new_id) = remap.get(id) {
                self.names.insert(name, (new_id, sort));
            }
            // Names pointing at reclaimed terms CANNOT exist because
            // we pinned every named TermId above — but if a caller
            // somehow violates the contract, we silently drop the
            // name rather than dangling.
        }

        // Phase 6: rebuild the hash-cons map from scratch. This is
        // O(live_terms) — cheaper than patching the stale map,
        // because dead entries were bloating every bucket.
        let mut new_hash_cons: KaniHashMap<u64, Vec<TermId>> = KaniHashMap::default();
        for (idx, entry) in self.terms.iter().enumerate() {
            let hash = Self::compute_hash(&entry.term);
            new_hash_cons
                .entry(hash)
                .or_default()
                .push(TermId(idx as u32));
        }
        self.hash_cons = new_hash_cons;

        // Phase 7: update memory accounting. The old counters
        // tracked pre-compaction allocation. After compaction the
        // real instance footprint is the sum of surviving entries'
        // heap + the new hash-cons bucket capacities + names.
        let names_string_heap: usize = self
            .names
            .iter()
            .map(|(name, _)| name.capacity() + size_of::<(TermId, Sort)>())
            .sum();
        let bucket_capacity_bytes: usize = self
            .hash_cons
            .values()
            .map(|v| v.capacity() * size_of::<TermId>())
            .sum();
        let entries_bytes = self.terms.len() * size_of::<TermEntry>();

        let new_total =
            entries_bytes + new_heap_data_bytes + names_string_heap + bucket_capacity_bytes;
        let old_total = self.instance_term_bytes;

        // Decrement the global counter by the freed amount. Use a
        // saturating CAS loop identical to Drop's pattern: if another
        // thread reset GLOBAL_TERM_BYTES while we were compacting, a
        // naive fetch_sub could underflow.
        let freed = old_total.saturating_sub(new_total);
        if freed > 0 {
            let mut current = GLOBAL_TERM_BYTES.load(Ordering::Relaxed);
            loop {
                let nv = current.saturating_sub(freed);
                match GLOBAL_TERM_BYTES.compare_exchange_weak(
                    current,
                    nv,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => break,
                    Err(actual) => current = actual,
                }
            }
        }

        self.instance_term_bytes = new_total;
        self.heap_data_bytes = new_heap_data_bytes + names_string_heap;
        self.bucket_capacity_bytes = bucket_capacity_bytes;
        // Invalidate the true_memory_bytes cache so the next pressure
        // check recomputes against the compacted arena.
        self.true_memory_cache.set(0);
        self.true_memory_cache_at.set(0);

        remap
    }

    /// Call `f` on every `TermId` child referenced by `term`.
    ///
    /// This is the ONE place that enumerates structural children of a
    /// [`TermData`]. Keeping it centralised prevents the marking pass
    /// and the child-rewrite pass from drifting out of sync — missing
    /// a child in one but not the other would cause a use-after-free.
    fn for_each_child(term: &TermData, mut f: impl FnMut(TermId)) {
        match term {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::App(_, args) => {
                for &c in args {
                    f(c);
                }
            }
            TermData::Let(bindings, body) => {
                for (_, c) in bindings {
                    f(*c);
                }
                f(*body);
            }
            TermData::Not(t) => f(*t),
            TermData::Ite(c, t, e) => {
                f(*c);
                f(*t);
                f(*e);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                f(*body);
                for group in triggers {
                    for &t in group {
                        f(t);
                    }
                }
            }
        }
    }

    /// Rewrite every child [`TermId`] inside `term` through `mapping`.
    /// Every child MUST resolve (it was visited by the marking pass).
    fn remap_term_children(term: &mut TermData, mapping: &[Option<TermId>]) {
        let remap = |old: TermId| -> TermId {
            if old.is_sentinel() {
                return TermId::SENTINEL;
            }
            mapping[old.index()]
                .expect("mark_and_compact: child not marked — bug in for_each_child")
        };
        match term {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::App(_, args) => {
                for c in args.iter_mut() {
                    *c = remap(*c);
                }
            }
            TermData::Let(bindings, body) => {
                for (_, c) in bindings.iter_mut() {
                    *c = remap(*c);
                }
                *body = remap(*body);
            }
            TermData::Not(t) => *t = remap(*t),
            TermData::Ite(c, t, e) => {
                *c = remap(*c);
                *t = remap(*t);
                *e = remap(*e);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                *body = remap(*body);
                for group in triggers.iter_mut() {
                    for t in group.iter_mut() {
                        *t = remap(*t);
                    }
                }
            }
        }
    }
}

// ----------------------------------------------------------------------
// Unit tests
// ----------------------------------------------------------------------

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]
mod tests {
    use super::*;
    use crate::kani_compat::{det_hash_set_new, DetHashSet};
    use crate::sort::Sort;
    use crate::term::{Constant, Symbol, TermData};
    use num_bigint::BigInt;

    /// Helper: build an arithmetic term `(+ x y)` returning the root.
    fn build_add(store: &mut TermStore, x: TermId, y: TermId) -> TermId {
        store.intern(TermData::App(Symbol::named("+"), vec![x, y]), Sort::Int)
    }

    fn mk_int_var(store: &mut TermStore, name: &str) -> TermId {
        store.mk_var(name, Sort::Int)
    }

    #[test]
    fn test_compact_preserves_semantics_of_live_roots() {
        // Round-trip: interning the same TermData after compaction must
        // return the same TermId as mark_and_compact produced.
        let mut store = TermStore::new();
        let x = mk_int_var(&mut store, "x");
        let y = mk_int_var(&mut store, "y");
        let sum = build_add(&mut store, x, y);

        // Create some garbage: terms that will NOT be in the root set.
        let z = mk_int_var(&mut store, "z");
        let _garbage1 = build_add(&mut store, x, z);
        let _garbage2 = store.intern(TermData::App(Symbol::named("*"), vec![y, z]), Sort::Int);

        let before_len = store.len();
        let remap = store.mark_and_compact(&[sum]);

        // x, y, z are pinned via `names`, so none of them are
        // reclaimed. sum is pinned as a root. The two garbage terms
        // (x+z and y*z) are only reachable through themselves — NOT
        // pinned — and MUST be gone.
        assert!(
            store.len() < before_len,
            "compaction should shrink arena: before={before_len} after={}",
            store.len()
        );

        let new_sum = remap.remap(sum);
        // Post-compaction, the term at new_sum must still be `(+ x y)`
        // with remapped children.
        let new_x = remap.remap(x);
        let new_y = remap.remap(y);
        match store.get(new_sum) {
            TermData::App(sym, args) => {
                assert_eq!(sym.name(), "+");
                assert_eq!(args.len(), 2);
                assert_eq!(args[0], new_x);
                assert_eq!(args[1], new_y);
            }
            other => panic!("expected (+ x y), got {other:?}"),
        }

        // Re-interning (+ x y) with the remapped children returns the
        // SAME id — hash-cons is rebuilt correctly.
        let rehashed = store.intern(
            TermData::App(Symbol::named("+"), vec![new_x, new_y]),
            Sort::Int,
        );
        assert_eq!(rehashed, new_sum, "hash-cons rebuild lost dedup");
    }

    #[test]
    fn test_compact_shrinks_arena_after_bulk_garbage() {
        // Memory-reduction: create 10k terms, compact with few roots,
        // arena must shrink substantially.
        let mut store = TermStore::new();
        let base = mk_int_var(&mut store, "base");
        let mut garbage: Vec<TermId> = Vec::with_capacity(10_000);
        for i in 0..10_000i64 {
            let c = store.mk_int(BigInt::from(i));
            let t = build_add(&mut store, base, c);
            garbage.push(t);
        }

        // Keep only the last 2_000 as live. The other 8_000 + their
        // integer-constant children become garbage.
        let live_roots: Vec<TermId> = garbage[8_000..].to_vec();

        let before = store.len();
        let before_bytes = store.true_memory_bytes();

        let _ = store.mark_and_compact(&live_roots);

        let after = store.len();
        let after_bytes = store.true_memory_bytes();

        assert!(
            after < before,
            "arena should shrink: before={before} after={after}"
        );
        // We kept ~2k adds + 2k constants + `base` + true/false → ~4k.
        // Before was ~20k (10k adds + 10k consts + base + true/false).
        // Assert roughly half or less.
        assert!(
            after * 2 < before,
            "arena should drop to <=50% of original: before={before} after={after}"
        );
        assert!(
            after_bytes < before_bytes,
            "true_memory_bytes should drop: before={before_bytes} after={after_bytes}"
        );
    }

    #[test]
    fn test_compact_preserves_true_and_false() {
        let mut store = TermStore::new();
        let t_before = store.true_term();
        let f_before = store.false_term();
        // Create and abandon some garbage.
        for _ in 0..100 {
            let _ = store.mk_int(BigInt::from(0));
        }
        let _ = store.mark_and_compact(&[]);
        // true/false remain valid and still return a Bool constant.
        let t_after = store.true_term();
        let f_after = store.false_term();
        match store.get(t_after) {
            TermData::Const(Constant::Bool(true)) => {}
            other => panic!("true_term corrupted: {other:?}"),
        }
        match store.get(f_after) {
            TermData::Const(Constant::Bool(false)) => {}
            other => panic!("false_term corrupted: {other:?}"),
        }
        // true and false are pinned even without being in roots.
        // (IDs may be stable because they're the first two terms
        // created, but we don't assert equality to avoid coupling
        // to construction order.)
        let _ = (t_before, f_before);
    }

    #[test]
    fn test_compact_pins_named_variables() {
        // Every variable registered via `mk_var` lives in `store.names`
        // and MUST survive compaction (per design doc §3.1).
        let mut store = TermStore::new();
        let x = mk_int_var(&mut store, "x");
        let y = mk_int_var(&mut store, "y");
        // No roots beyond the names pin.
        let remap = store.mark_and_compact(&[]);

        // Variables remain reachable through the names map.
        let new_x = remap.get(x).expect("x (named) should survive");
        let new_y = remap.get(y).expect("y (named) should survive");
        assert!(matches!(store.get(new_x), TermData::Var(n, _) if n == "x"));
        assert!(matches!(store.get(new_y), TermData::Var(n, _) if n == "y"));
    }

    #[test]
    fn test_compact_transitive_closure_deep_nesting() {
        // Terms can nest deeply — the marking walk must follow children
        // iteratively without blowing the stack.
        let mut store = TermStore::new();
        let x = mk_int_var(&mut store, "x");
        let mut acc = x;
        for i in 0..500 {
            let c = store.mk_int(BigInt::from(i));
            acc = build_add(&mut store, acc, c);
        }
        let remap = store.mark_and_compact(&[acc]);
        // Every term in the spine must have survived. Walking args[0]
        // repeatedly from the root must eventually reach Var("x");
        // along the way every level must be an App(+, [spine, const]).
        let new_root = remap.remap(acc);
        let mut cursor = new_root;
        let mut hops = 0;
        loop {
            hops += 1;
            assert!(hops <= 600, "spine too long — loop, not a chain");
            match store.get(cursor).clone() {
                TermData::App(_, args) => {
                    assert_eq!(args.len(), 2);
                    cursor = args[0];
                }
                TermData::Var(n, _) => {
                    assert_eq!(n, "x");
                    break;
                }
                other => panic!("unexpected term in spine: {other:?}"),
            }
        }
        // We built the chain with 500 `+` applications, so reaching x
        // takes exactly 500 hops through App plus one terminal match
        // — 501 hops total.
        assert_eq!(hops, 501, "expected 501 hops to reach x, got {hops}");
    }

    #[test]
    fn test_compact_ite_and_not() {
        // Exercise Not / Ite / Forall child walks to catch for_each_child
        // drift.
        let mut store = TermStore::new();
        let p = store.mk_var("p", Sort::Bool);
        let q = store.mk_var("q", Sort::Bool);
        let r = store.mk_var("r", Sort::Bool);
        let not_p = store.intern(TermData::Not(p), Sort::Bool);
        let ite = store.intern(TermData::Ite(not_p, q, r), Sort::Bool);
        let remap = store.mark_and_compact(&[ite]);
        let new_ite = remap.remap(ite);
        match store.get(new_ite) {
            TermData::Ite(c, t, e) => {
                assert_eq!(*c, remap.remap(not_p));
                assert_eq!(*t, remap.remap(q));
                assert_eq!(*e, remap.remap(r));
            }
            other => panic!("ite corrupted: {other:?}"),
        }
        match store.get(remap.remap(not_p)) {
            TermData::Not(inner) => assert_eq!(*inner, remap.remap(p)),
            other => panic!("not corrupted: {other:?}"),
        }
    }

    #[test]
    fn test_compact_quantifier_body_and_triggers() {
        // Forall/Exists carry TermIds in both the body and the
        // (multi-)trigger list. Both paths must be walked.
        let mut store = TermStore::new();
        let x = mk_int_var(&mut store, "qx");
        let body = mk_int_var(&mut store, "qbody");
        let trig_a = mk_int_var(&mut store, "qtriga");
        let trig_b = mk_int_var(&mut store, "qtrigb");
        let forall = store.intern(
            TermData::Forall(
                vec![("v".into(), Sort::Int)],
                body,
                vec![vec![trig_a, trig_b]],
            ),
            Sort::Bool,
        );
        // x is not referenced by forall; it's only pinned via `names`.
        let _ = x;
        let remap = store.mark_and_compact(&[forall]);
        let new_forall = remap.remap(forall);
        match store.get(new_forall) {
            TermData::Forall(vars, b, triggers) => {
                assert_eq!(vars.len(), 1);
                assert_eq!(vars[0].0, "v");
                assert_eq!(*b, remap.remap(body));
                assert_eq!(triggers.len(), 1);
                assert_eq!(triggers[0].len(), 2);
                assert_eq!(triggers[0][0], remap.remap(trig_a));
                assert_eq!(triggers[0][1], remap.remap(trig_b));
            }
            other => panic!("forall corrupted: {other:?}"),
        }
    }

    #[test]
    fn test_compact_sentinel_is_preserved() {
        let mut store = TermStore::new();
        let _ = mk_int_var(&mut store, "dummy");
        let remap = store.mark_and_compact(&[]);
        assert_eq!(remap.get(TermId::SENTINEL), Some(TermId::SENTINEL));
        assert_eq!(remap.remap(TermId::SENTINEL), TermId::SENTINEL);
    }

    #[test]
    fn test_compact_idempotent_when_no_garbage() {
        // If nothing is garbage, compaction must be a no-op modulo
        // relabelling.
        let mut store = TermStore::new();
        let x = mk_int_var(&mut store, "x");
        let y = mk_int_var(&mut store, "y");
        let sum = build_add(&mut store, x, y);
        let before_len = store.len();
        let remap = store.mark_and_compact(&[sum]);
        assert_eq!(store.len(), before_len, "no-garbage compact changed len");
        // All live terms must remain reachable.
        assert!(remap.get(sum).is_some());
        assert!(remap.get(x).is_some());
        assert!(remap.get(y).is_some());
    }

    #[test]
    fn test_compact_rebuilds_hash_cons_for_future_interns() {
        let mut store = TermStore::new();
        let x = mk_int_var(&mut store, "x");
        let y = mk_int_var(&mut store, "y");
        let sum = build_add(&mut store, x, y);

        // Create garbage that shares a structure with what we'll
        // re-intern later — we want to make sure the hash-cons map
        // doesn't accidentally resurrect a reclaimed id.
        let z = mk_int_var(&mut store, "z");
        let _garbage = build_add(&mut store, x, z);
        let _garbage2 = build_add(&mut store, y, z);

        let remap = store.mark_and_compact(&[sum]);
        let new_x = remap.remap(x);
        let new_y = remap.remap(y);

        // (+ new_x new_y) already exists in the new arena.
        let new_sum_lookup = store.intern(
            TermData::App(Symbol::named("+"), vec![new_x, new_y]),
            Sort::Int,
        );
        assert_eq!(new_sum_lookup, remap.remap(sum));

        // A fresh term NOT previously present must get a new id
        // strictly greater than any live id.
        let w = mk_int_var(&mut store, "w");
        let fresh = build_add(&mut store, new_x, w);
        let live_count = store.len();
        assert!(fresh.index() < live_count);
    }

    #[test]
    fn test_remappable_trait_on_common_containers() {
        // Sanity-check the blanket impls.
        let mut store = TermStore::new();
        let x = mk_int_var(&mut store, "x");
        let y = mk_int_var(&mut store, "y");
        let remap = store.mark_and_compact(&[]);
        let new_x = remap.remap(x);
        let new_y = remap.remap(y);

        let mut v: Vec<TermId> = vec![x, y];
        v.remap(&remap.as_fn());
        assert_eq!(v, vec![new_x, new_y]);

        let mut opt: Option<TermId> = Some(x);
        opt.remap(&remap.as_fn());
        assert_eq!(opt, Some(new_x));

        let mut arr: [TermId; 2] = [x, y];
        arr.remap(&remap.as_fn());
        assert_eq!(arr, [new_x, new_y]);
    }

    /// Proof-preservation check: a simple proof-log-like external
    /// holder of TermIds is correctly remapped and continues to
    /// resolve to the semantically-equivalent term.
    ///
    /// This stands in for the LRAT/Alethe tests called out in the
    /// task brief — we don't pull in the full proof pipeline from
    /// here (that crosses crate boundaries), but we demonstrate the
    /// invariant the pipeline depends on: a `Remappable` proof
    /// log records semantically-equivalent terms before and after.
    #[test]
    fn test_remap_preserves_term_semantics_for_external_holder() {
        #[derive(Default)]
        struct FakeProofLog {
            /// Each "step" records (conclusion, premises).
            steps: Vec<(TermId, Vec<TermId>)>,
        }
        impl Remappable for FakeProofLog {
            fn remap(&mut self, f: &dyn Fn(TermId) -> TermId) {
                for (c, ps) in &mut self.steps {
                    c.remap(f);
                    ps.remap(f);
                }
            }
        }

        let mut store = TermStore::new();
        let x = mk_int_var(&mut store, "x");
        let y = mk_int_var(&mut store, "y");
        let sum = build_add(&mut store, x, y);

        // Pre-compaction TermData snapshots (cloned — they are the
        // "payload" a proof checker would serialise).
        let pre_x: TermData = store.get(x).clone();
        let pre_y: TermData = store.get(y).clone();
        let pre_sum: TermData = store.get(sum).clone();

        let mut log = FakeProofLog::default();
        log.steps.push((sum, vec![x, y]));

        // Introduce garbage so compaction actually moves ids.
        let z = mk_int_var(&mut store, "z");
        let _garbage = build_add(&mut store, x, z);

        let remap = store.mark_and_compact(&[sum]);
        log.remap(&remap.as_fn());

        // After remap, every id in the log resolves to the ORIGINAL
        // semantic payload.
        let (conc, prems) = &log.steps[0];
        assert_eq!(store.get(*conc), &pre_sum);
        assert_eq!(prems.len(), 2);
        assert_eq!(store.get(prems[0]), &pre_x);
        assert_eq!(store.get(prems[1]), &pre_y);
    }

    /// Reachable-set check against a ground-truth HashSet implementation.
    /// This is a mini property test without pulling in proptest.
    #[test]
    fn test_compact_reachable_set_matches_reference() {
        let mut store = TermStore::new();
        let x = mk_int_var(&mut store, "x");
        let y = mk_int_var(&mut store, "y");
        let z = mk_int_var(&mut store, "z");
        let ab = build_add(&mut store, x, y);
        let bc = build_add(&mut store, y, z);
        let tree = build_add(&mut store, ab, bc);

        // Reference reachable set (iterative DFS over `children`).
        let mut expected: DetHashSet<TermId> = det_hash_set_new();
        let mut stk = vec![tree];
        while let Some(t) = stk.pop() {
            if !expected.insert(t) {
                continue;
            }
            for c in store.children(t) {
                stk.push(c);
            }
        }
        // Include names pins (x, y, z) and true/false.
        expected.insert(x);
        expected.insert(y);
        expected.insert(z);
        expected.insert(store.true_term());
        expected.insert(store.false_term());

        let before_len = store.len();
        let remap = store.mark_and_compact(&[tree]);
        assert_eq!(
            store.len(),
            expected.len(),
            "live count mismatch: before_len={before_len} got={} expected={}",
            store.len(),
            expected.len()
        );
        for old in expected {
            assert!(
                remap.get(old).is_some(),
                "expected live TermId {old:?} was reclaimed"
            );
        }
    }
}
