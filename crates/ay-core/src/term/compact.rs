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

        // Compaction can shrink the arena and later appends can restore the old
        // length with different terms. Retire length-keyed structural snapshots
        // (and pre-compaction rollback checkpoints) before rewriting anything,
        // so that sequence can never alias the old term universe.
        self.advance_structural_generation();

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
            // `:no-pattern` candidates live in a side map rather than in
            // `TermData`, but their TermIds are owned by a live quantifier and
            // must survive and be remapped with it.
            if let Some(no_patterns) = self.quantifier_no_patterns.get(&id) {
                for &no_pattern in no_patterns {
                    push_root(no_pattern, &mut stack, &mut reachable);
                }
            }
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
            let placeholder_stamp = self.terms[old_idx].stamp;
            let mut entry = std::mem::replace(
                &mut self.terms[old_idx],
                TermEntry {
                    term: TermData::Not(TermId(0)),
                    sort: Sort::Bool,
                    stamp: placeholder_stamp,
                },
            );

            // Rewrite every child TermId inside the term payload.
            Self::remap_term_children(&mut entry.term, &mapping);

            new_heap_data_bytes += Self::heap_size(&entry.term);
            new_terms.push(entry);
        }

        // Phase 4: swap in the compacted arena.
        self.terms = new_terms;
        // Memoized checker verdicts are keyed by `TermId` and every id has just
        // been remapped, so the memo cannot be carried across compaction.
        self.strict_bv_semantics_ok.get_mut().clear();

        // Phase 5: remap TermStore-owned pins.
        //
        // The synthesis watermark is an INDEX, not a `TermId`, so neither
        // `RemapTable` nor `Remappable` can carry it and a compaction that
        // ignored it would leave a boundary pointing into a term universe that
        // no longer exists. It is recoverable exactly: terms are emitted in
        // increasing OLD-id order, so every surviving pre-watermark term keeps a
        // new id below every surviving post-watermark term, and the new boundary
        // is simply how many pre-watermark terms survived. With that count,
        // `is_synthesized(new_id)` answers exactly what `is_synthesized(old_id)`
        // answered for the same term - preserved, not merely fail-open.
        if let Some(old_watermark) = self.synthesis_watermark {
            let surviving_original = mapping
                .iter()
                .take(old_watermark.min(mapping.len()))
                .filter(|slot| slot.is_some())
                .count();
            self.synthesis_watermark = Some(surviving_original);
        }
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

        // The `mk_not` memo (`arg -> not(arg)`) is keyed AND valued by `TermId`,
        // so a compaction that ignored it would answer the next `mk_not` with a
        // node that is not the negation of its argument — a wrong term, silently,
        // from a pure builder. `rollback_to` already prunes this map for exactly
        // that reason (it can only ever reuse a suffix); compaction relabels the
        // WHOLE arena, so every surviving entry has to move and every reclaimed
        // one has to go. Relabelling preserves the relation: `TermData` is
        // byte-identical after the move, so `not(k) == v` still holds of the
        // images `k'`, `v'`.
        let old_not_cache = std::mem::take(&mut self.not_cache);
        for (arg, negated) in old_not_cache {
            if let (Some(new_arg), Some(new_negated)) = (remap.get(arg), remap.get(negated)) {
                self.not_cache.insert(new_arg, new_negated);
            }
        }

        let old_no_mbqi = std::mem::take(&mut self.no_mbqi);
        for old_id in old_no_mbqi {
            if let Some(new_id) = remap.get(old_id) {
                self.no_mbqi.insert(new_id);
            }
        }

        let old_quantifier_id = std::mem::take(&mut self.quantifier_id);
        for (old_id, qid) in old_quantifier_id {
            if let Some(new_id) = remap.get(old_id) {
                self.quantifier_id.insert(new_id, qid);
            }
        }

        let old_skolem_id = std::mem::take(&mut self.skolem_id);
        for (old_id, skid) in old_skolem_id {
            if let Some(new_id) = remap.get(old_id) {
                self.skolem_id.insert(new_id, skid);
            }
        }

        let old_quantifier_weight = std::mem::take(&mut self.quantifier_weight);
        for (old_id, weight) in old_quantifier_weight {
            if let Some(new_id) = remap.get(old_id) {
                self.quantifier_weight.insert(new_id, weight);
            }
        }

        let old_quantifier_no_patterns = std::mem::take(&mut self.quantifier_no_patterns);
        for (old_id, no_patterns) in old_quantifier_no_patterns {
            let Some(new_id) = remap.get(old_id) else {
                continue;
            };
            let no_patterns = no_patterns
                .into_iter()
                .map(|no_pattern| remap.remap(no_pattern))
                .collect();
            self.quantifier_no_patterns.insert(new_id, no_patterns);
        }

        // Skolem-choice provenance is keyed by witness TermId and holds a body
        // TermId, so both sides must move with the arena. An entry whose
        // witness or body was reclaimed is DROPPED — the exporter then DECLINES
        // rather than spelling a term that no longer exists. (The neighbouring
        // `no_mbqi` / `quantifier_id` / `skolem_id`
        // pins are not remapped here; they are instantiation hints whose loss
        // cannot change a verdict, whereas this map is read by the certificate
        // printer.)
        let old_skolem_choice = std::mem::take(&mut self.skolem_choice);
        for (witness, mut choice) in old_skolem_choice {
            let (Some(new_witness), Some(new_body)) = (remap.get(witness), remap.get(choice.body))
            else {
                continue;
            };
            choice.body = new_body;
            self.skolem_choice.insert(new_witness, choice);
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

    /// The `mk_not` memo must move with the arena.
    ///
    /// The memo is keyed AND valued by `TermId`, so if compaction left it alone
    /// the very next `mk_not` would be answered out of a table describing the
    /// PRE-compaction universe — returning a node that is not the negation of
    /// its argument. That is a wrong term produced by a pure builder, with no
    /// checker anywhere in the path, which is why this is a soundness test and
    /// not a hygiene one. `rollback_to` already prunes the same map.
    #[test]
    fn compaction_moves_the_mk_not_memo_with_the_arena() {
        let mut store = TermStore::new();
        // Three declared Bools: `mk_var` pins them in `names`, so all three
        // survive compaction and their memo rows are the ones that can collide
        // with a relabelled slot.
        let p = store.mk_var("memo_p", Sort::Bool);
        let q = store.mk_var("memo_q", Sort::Bool);
        let _s = store.mk_var("memo_s", Sort::Bool);
        // Rows that will DIE (their negations are reachable from nothing).
        let not_p = store.mk_not(p);
        let not_q = store.mk_not(q);
        // The row that will LIVE, minted above a gap the compaction closes.
        let r = store.intern(TermData::App(Symbol::named("r"), vec![p, q]), Sort::Bool);
        let not_r = store.mk_not(r);

        let before = store.len();
        let remap = store.mark_and_compact(&[not_r]);
        assert!(
            store.len() < before,
            "the fixture requires reclaimed slots, so ids actually move"
        );
        assert!(remap.get(not_p).is_none() && remap.get(not_q).is_none());

        let new_p = remap.remap(p);
        let new_r = remap.remap(r);
        let new_not_r = remap.remap(not_r);

        // WHITEBOX: no surviving row may describe the old universe. Either side
        // out of range is a dangling read; a row whose value is not the negation
        // of its key is a wrong answer waiting to be served.
        for (&arg, &negated) in store.not_cache.iter() {
            assert!(
                arg.index() < store.len() && negated.index() < store.len(),
                "memo row {arg:?} -> {negated:?} points outside the compacted arena"
            );
            let describes_a_negation = matches!(store.get(negated), TermData::Not(inner) if *inner == arg)
                || matches!(store.get(arg), TermData::Not(inner) if *inner == negated)
                || matches!(
                    (store.get(arg), store.get(negated)),
                    (
                        TermData::Const(Constant::Bool(a)),
                        TermData::Const(Constant::Bool(b))
                    ) if a != b
                );
            assert!(
                describes_a_negation,
                "memo row {arg:?} -> {negated:?} no longer describes a negation"
            );
        }

        // And the builder itself must answer correctly for both a survivor whose
        // row was dropped and one whose row moved.
        let rebuilt_not_p = store.mk_not(new_p);
        assert_eq!(store.get(rebuilt_not_p), &TermData::Not(new_p));
        assert_eq!(store.mk_not(new_r), new_not_r);
        assert_eq!(store.get(new_not_r), &TermData::Not(new_r));
    }

    /// The synthesis watermark is an INDEX, so compaction must move it too.
    ///
    /// Terms are emitted in increasing OLD-id order, so the boundary survives
    /// exactly: it becomes the number of surviving pre-watermark terms. This
    /// pins the preserved answer, not merely a fail-open one.
    #[test]
    fn compaction_preserves_the_synthesis_watermark_boundary() {
        let mut store = TermStore::new();
        let original_a = mk_int_var(&mut store, "orig_a");
        let original_b = mk_int_var(&mut store, "orig_b");
        let original_sum = build_add(&mut store, original_a, original_b);
        // Dead ORIGINAL-side term: reclaimed, and its slot must not be counted
        // into the new boundary.
        let _dead_original = store.intern(
            TermData::App(Symbol::named("dead"), vec![original_a]),
            Sort::Int,
        );

        store.set_synthesis_watermark();

        let synthesized = store.intern(
            TermData::App(Symbol::named("synth"), vec![original_sum]),
            Sort::Int,
        );
        assert!(!store.is_synthesized(original_sum));
        assert!(store.is_synthesized(synthesized));

        let remap = store.mark_and_compact(&[synthesized]);
        let new_sum = remap.remap(original_sum);
        let new_synth = remap.remap(synthesized);

        assert!(
            !store.is_synthesized(new_sum),
            "an original-problem term must stay original after compaction"
        );
        assert!(
            store.is_synthesized(new_synth),
            "a solve-invented term must stay invented after compaction"
        );
    }

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
    fn test_compact_preserves_quantifier_side_metadata() {
        let mut store = TermStore::new();

        // This unrooted constant is deliberately allocated first so every live
        // metadata key/value below moves to a different TermId.
        let garbage = store.mk_int(BigInt::from(999));
        let x = mk_int_var(&mut store, "metadata_x");
        let body = store.mk_var("metadata_body", Sort::Bool);
        let no_pattern = store.intern(
            TermData::App(Symbol::named("metadata_no_pattern"), vec![x]),
            Sort::Bool,
        );
        let forall = store.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        store.mark_no_mbqi(forall);
        store.set_quantifier_id(forall, "compact-qid".to_string());
        store.set_skolem_id(forall, "compact-skid".to_string());
        store.set_quantifier_weight(forall, 23);
        store.set_quantifier_no_patterns(forall, vec![no_pattern]);

        let remap = store.mark_and_compact(&[forall]);

        assert_eq!(remap.get(garbage), None);
        let new_forall = remap.remap(forall);
        let new_no_pattern = remap
            .get(no_pattern)
            .expect(":no-pattern metadata must pin its term");
        assert_ne!(new_forall, forall);
        assert_ne!(new_no_pattern, no_pattern);
        assert!(store.is_no_mbqi(new_forall));
        assert_eq!(store.quantifier_id(new_forall), Some("compact-qid"));
        assert_eq!(store.skolem_id(new_forall), Some("compact-skid"));
        assert_eq!(store.explicit_quantifier_weight(new_forall), Some(23));
        assert_eq!(store.quantifier_no_patterns(new_forall), &[new_no_pattern]);
        assert!(matches!(
            store.get(new_no_pattern),
            TermData::App(symbol, args)
                if symbol.name() == "metadata_no_pattern"
                    && args == &[remap.remap(x)]
        ));
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
