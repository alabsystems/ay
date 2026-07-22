// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF explanation and proof-forest traversal.
//!
//! Congruence closure rebuilding lives in sibling `closure.rs`.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermId;
use ay_core::{TheoryLit, TheoryResult};
use std::collections::VecDeque;

use crate::solver::EufSolver;
use crate::types::{EqualityReason, UndoRecord};

/// Batch-lifetime cache of `(a, b) → reason-literal set`, used to skip
/// re-traversing shared congruence sub-proofs. Two reuse scopes share the
/// SAME structure:
///   1. Within one top-level `explain` call, shared congruence sub-DAGs
///      appear many times across the proof DAG (the profiled QF_UF hot spot).
///   2. Across the whole `propagate_equalities` DRAIN BATCH: the batch calls
///      `explain(lhs, rhs)` for many pending congruence propagations that
///      share sub-proofs; threading ONE cache through the batch (via
///      `explain_using_memo`, no `clear()` between pairs) reuses them
///      cross-call (#i6-euf-explain-batch-memo).
///
/// SOUND BY CONSTRUCTION: throughout a batch NO merges occur — `explain` only
/// reads `pending_propagations` and the proof forest (`propagate_equalities`
/// drains, it never merges). So the forest is IMMUTABLE across the batch and
/// `explain_into(a, b)` is a pure function of `(a, b)` + forest: the reason set
/// on the a↔b path. A cache HIT re-appends exactly that set, byte-identical to
/// a fresh walk (the top-level `sort`+`dedup` normalizes ordering/duplicates).
///
/// EUF is STRICTLY SAFER than the array eq-path cache here: the proof forest is
/// a TREE, so the `a→lca→b` reason path is UNIQUE — there is no shortest-vs-any
/// ambiguity (the fuzz-2303-class model sensitivity the arrays cache must pin).
/// The cached set is THE set, not A set.
///
/// A cached entry is SELF-CONTAINED (the full expanded reason set for its pair),
/// so — unlike the former skip-set — a parent congruence frame that fails and
/// truncates its buffer needs NO cache rollback: a later HIT on a sub-pair
/// re-APPENDS its reasons (it does not merely "skip because already present").
///
/// Threaded by `&mut` (NOT stored on `self` across the recursion) so a
/// re-entrant BFS-fallback `self.explain()` takes its own cache and cannot
/// cross buffers.
#[derive(Default)]
pub(crate) struct ExplainMemo {
    cache: HashMap<(u32, u32), Vec<TheoryLit>>,
}

impl ExplainMemo {
    #[inline]
    pub(crate) fn clear(&mut self) {
        self.cache.clear();
    }
    #[inline]
    fn key(a: u32, b: u32) -> (u32, u32) {
        if a <= b {
            (a, b)
        } else {
            (b, a)
        }
    }
    #[inline]
    fn get(&self, a: u32, b: u32) -> Option<&Vec<TheoryLit>> {
        self.cache.get(&Self::key(a, b))
    }
    /// Store the reason set for `(a, b)` (idempotent: the forest is immutable
    /// within the cache lifetime, so a re-store would be identical).
    #[inline]
    fn insert(&mut self, a: u32, b: u32, reasons: &[TheoryLit]) {
        self.cache
            .entry(Self::key(a, b))
            .or_insert_with(|| reasons.to_vec());
    }
}

impl EufSolver<'_> {
    /// Find the root of a node's proof-forest tree.
    /// Follows proof_target pointers until None (tree root).
    pub(crate) fn find_proof_root(&self, x: u32) -> u32 {
        let mut curr = x;
        while let Some(target) = self.enodes.get(curr as usize).and_then(|e| e.proof_target) {
            curr = target;
        }
        curr
    }

    /// Reverse the singly-linked proof-forest path from `node` to its root,
    /// making `node` the new root of its proof subtree.
    /// Port of Z3's euf_enode.cpp:133-148 reverse_justification().
    pub(crate) fn reverse_justification(&mut self, node: u32) {
        let mut curr = node;
        let mut prev_target: Option<u32> = None;
        let mut prev_just: Option<EqualityReason> = None;
        while let Some(target) = self.enodes[curr as usize].proof_target {
            let curr_just = self.enodes[curr as usize].proof_justification.take();
            self.enodes[curr as usize].proof_target = prev_target;
            self.enodes[curr as usize].proof_justification = prev_just;
            prev_target = Some(curr);
            prev_just = curr_just;
            curr = target;
        }
        self.enodes[curr as usize].proof_target = prev_target;
        self.enodes[curr as usize].proof_justification = prev_just;
    }

    /// Set a proof-forest edge from a to b with the given reason.
    /// Records an UnmergeProofForest undo record for incremental pop().
    /// Port of Z3's merge_justification().
    pub(crate) fn merge_proof_forest(&mut self, a: u32, b: u32, reason: EqualityReason) {
        let old_root = self.find_proof_root(a);
        if old_root == self.find_proof_root(b) {
            return;
        }
        self.reverse_justification(a);
        self.enodes[a as usize].proof_target = Some(b);
        self.enodes[a as usize].proof_justification = Some(reason);
        self.undo_trail
            .push(UndoRecord::UnmergeProofForest { node: a, old_root });
    }

    /// Undo a proof-forest merge. Called during pop() for UnmergeProofForest records.
    /// Port of Z3's unmerge_justification().
    pub(crate) fn unmerge_proof_forest(&mut self, node: u32, old_root: u32) {
        if (node as usize) < self.enodes.len() {
            self.enodes[node as usize].proof_target = None;
            self.enodes[node as usize].proof_justification = None;
        }
        if (old_root as usize) < self.enodes.len() {
            self.reverse_justification(old_root);
        }
    }

    /// Find the lowest common ancestor (LCA) of two nodes in the proof forest.
    ///
    /// Two-pointer depth-balanced walk — ZERO allocation. The previous version
    /// allocated and populated a fresh `HashSet` of `a`'s ancestors on every
    /// call; since `explain` calls `find_lca` at very high volume (and
    /// recursively through congruence sub-pairs), that per-call hashing
    /// (`reserve_rehash`/`insert`/`fallible_with_capacity`) was the dominant
    /// EUF cost on dense QF_UF benchmarks. Both nodes are in the same proof tree
    /// (the caller checks `find_proof_root(a) == find_proof_root(b)`), so
    /// equalizing depths and then advancing both pointers in lockstep meets at
    /// the LCA. Result is identical to the set-based version for a tree.
    pub(crate) fn find_lca(&self, a: u32, b: u32) -> u32 {
        #[inline]
        fn parent(this: &EufSolver<'_>, x: u32) -> Option<u32> {
            this.enodes.get(x as usize).and_then(|e| e.proof_target)
        }
        // Measure each node's depth (distance to its proof-tree root).
        let mut da: u32 = 0;
        let mut x = a;
        while let Some(t) = parent(self, x) {
            da += 1;
            x = t;
        }
        let mut db: u32 = 0;
        let mut y = b;
        while let Some(t) = parent(self, y) {
            db += 1;
            y = t;
        }
        // Lift the deeper node until both are at equal depth.
        let mut ca = a;
        let mut cb = b;
        while da > db {
            match parent(self, ca) {
                Some(t) => ca = t,
                None => break,
            }
            da -= 1;
        }
        while db > da {
            match parent(self, cb) {
                Some(t) => cb = t,
                None => break,
            }
            db -= 1;
        }
        // Advance both in lockstep until they converge on the LCA.
        while ca != cb {
            match (parent(self, ca), parent(self, cb)) {
                (Some(ta), Some(tb)) => {
                    ca = ta;
                    cb = tb;
                }
                // Reached roots without meeting — only possible if the caller's
                // same-tree precondition was violated; return current best.
                _ => break,
            }
        }
        ca
    }

    /// Collect reason literals along the proof-forest path from `from` to `to` (LCA).
    /// Handles Direct, Congruence (recursive explain for arg pairs), and Shared reasons.
    /// Returns `true` on success, `false` if the proof forest is broken.
    pub(crate) fn collect_path_reasons_proof_forest(
        &mut self,
        from: u32,
        to: u32,
        reasons: &mut Vec<TheoryLit>,
        memo: &mut ExplainMemo,
    ) -> bool {
        let mut curr = from;
        while curr != to {
            let target = self.enodes[curr as usize].proof_target;
            // Avoid cloning the justification: it is read by reference for the
            // simple variants, and the `Congruence` arg pairs (the only heap
            // field) are read by index so the borrow is released before each
            // recursive (mut self) sub-explain. The previous `.clone()` copied a
            // fresh `arg_pairs` Vec on EVERY edge walked — a per-step heap alloc
            // that dominated the residual `explain` cost after the LCA fix.
            let is_congruence = matches!(
                self.enodes[curr as usize].proof_justification,
                Some(EqualityReason::Congruence { .. })
            );
            if is_congruence {
                let n = match &self.enodes[curr as usize].proof_justification {
                    Some(EqualityReason::Congruence { arg_pairs, .. }) => arg_pairs.len(),
                    _ => 0,
                };
                for i in 0..n {
                    // TermId is Copy, so the borrow ends at the end of this match
                    // — before the recursive explain mutably borrows self.
                    let (arg_a, arg_b) = match &self.enodes[curr as usize].proof_justification {
                        Some(EqualityReason::Congruence { arg_pairs, .. }) => arg_pairs[i],
                        _ => continue,
                    };
                    if arg_a == arg_b {
                        continue;
                    }
                    if self.explain_nosort_enabled {
                        // Recurse into the SAME buffer without an intermediate
                        // sort/dedup; the top-level `explain` sorts+dedups once.
                        // Fall back to the full (BFS-capable) `explain` only if the
                        // proof-forest fast path can't resolve this sub-pair.
                        if !self.explain_into(arg_a, arg_b, reasons, memo) {
                            let sub = self.explain(arg_a, arg_b);
                            reasons.extend(sub);
                        }
                    } else {
                        let sub = self.explain(arg_a, arg_b);
                        reasons.extend(sub);
                    }
                }
            } else {
                match &self.enodes[curr as usize].proof_justification {
                    None => {}
                    Some(EqualityReason::Direct(eq_term)) => {
                        reasons.push(TheoryLit::new(*eq_term, true));
                    }
                    Some(EqualityReason::Shared) => {
                        let target_node = target.unwrap_or(curr);
                        let key = Self::edge_key(curr, target_node);
                        if let Some(lits) = self.shared_equality_reasons.get(&key) {
                            reasons.extend(lits.iter().copied());
                        } else {
                            // Production soundness gate (#8454): proof-forest
                            // edge missing. Log and bail instead of silently
                            // continuing with incomplete reasons. Caller discards
                            // or truncates partial reasons on a `false` return.
                            safe_eprintln!(
                                "BUG: proof-forest Shared edge ({curr}, {target_node}) has no entry in shared_equality_reasons — scope-aware cleanup may be incomplete"
                            );
                            return false;
                        }
                    }
                    Some(EqualityReason::BoolValue { term, value }) => {
                        let (t, v) = (*term, *value);
                        // #bool-arg-congruence: unwrap `Not` so reason literals
                        // reference the SAT-owned atom (Not(inner)=v ⟺ inner=!v);
                        // constant endpoints contribute no literal (skip None).
                        if let Some(lit) = self.bool_value_reason_lit(t, v) {
                            reasons.push(lit);
                        }
                        let other = target.unwrap_or(curr);
                        if let Some(lit) = self.bool_value_reason_lit(TermId(other), v) {
                            reasons.push(lit);
                        }
                    }
                    Some(EqualityReason::Ite { condition, value }) => {
                        reasons.push(TheoryLit::new(*condition, *value));
                    }
                    // Routed to the `is_congruence` branch above.
                    Some(EqualityReason::Congruence { .. }) => unreachable!(),
                }
            }
            match target {
                Some(next) => curr = next,
                None => {
                    // Production soundness gate (#8454): proof-forest path
                    // broken. Log and bail instead of silently continuing.
                    safe_eprintln!(
                        "BUG: proof-forest path broken at node {curr} before reaching LCA {to}"
                    );
                    // See note above: caller discards/truncates on `false`.
                    return false;
                }
            }
        }
        true
    }

    pub(crate) fn all_true_equalities(&self) -> Vec<TheoryLit> {
        let mut keys: Vec<TermId> = self.assigns.keys().copied().collect();
        keys.sort_unstable(); // Deterministic iteration order (#3724)
        let mut out = Vec::new();
        for t in keys {
            if self.assigns[&t] && self.decode_eq(t).is_some() {
                out.push(TheoryLit::new(t, true));
            }
        }
        out
    }

    /// Proof-forest reason collection WITHOUT sorting — appends the LCA-path
    /// reasons for `a == b` (recursing into congruence sub-pairs) onto `reasons`.
    ///
    /// Returns `true` on success. On `false` (terms not in the same proof tree,
    /// or a broken/missing proof edge) the buffer is truncated back to its
    /// entry length so a shared parent frame's reasons are preserved, and the
    /// caller (top-level `explain`) falls back to BFS.
    ///
    /// This is the core of the `explain_nosort_enabled` optimization: the whole
    /// recursion shares one buffer and the top-level `explain` sorts+dedups it
    /// ONCE, instead of sorting+deduping at every recursive congruence level
    /// (O(depth) redundant sorts on deep chains). The final reason SET is
    /// identical to the legacy path, so learned-clause soundness is unchanged.
    pub(crate) fn explain_into(
        &mut self,
        a: TermId,
        b: TermId,
        reasons: &mut Vec<TheoryLit>,
        memo: &mut ExplainMemo,
    ) -> bool {
        if a == b {
            return true;
        }
        // Cache HIT: `(a, b)`'s complete reason set was computed earlier (this
        // call or an earlier pair in the same drain batch). Re-append it — the
        // forest is immutable within the cache lifetime, so this is byte
        // identical to a fresh walk (final `sort`+`dedup` normalizes). Unlike a
        // skip-set, we APPEND (the current buffer may not already hold it).
        if self.explain_memo_enabled {
            if let Some(cached) = memo.get(a.0, b.0) {
                #[cfg(debug_assertions)]
                let start = reasons.len();
                reasons.extend_from_slice(cached);
                // Debug oracle (#i6-euf-explain-batch-memo): recompute the
                // reasons uncached and assert the cached set matches.
                #[cfg(debug_assertions)]
                self.debug_assert_cached_explain(a, b, start, reasons);
                return true;
            }
        }
        if self.enodes_init
            && (a.0 as usize) < self.enodes.len()
            && (b.0 as usize) < self.enodes.len()
        {
            let root_a = self.find_proof_root(a.0);
            let root_b = self.find_proof_root(b.0);
            if root_a == root_b {
                let lca = self.find_lca(a.0, b.0);
                self.debug_assert_explain_lca(lca, root_a);
                let start = reasons.len();
                let ok_a = self.collect_path_reasons_proof_forest(a.0, lca, reasons, memo);
                let ok_b = ok_a && self.collect_path_reasons_proof_forest(b.0, lca, reasons, memo);
                if ok_a && ok_b {
                    // Cache only on FULL success: `true` guarantees the complete
                    // reason set for (a, b) is now the slice `reasons[start..]`.
                    if self.explain_memo_enabled {
                        memo.insert(a.0, b.0, &reasons[start..]);
                    }
                    return true;
                }
                // Partial append from a failed walk: restore the buffer so a
                // parent congruence frame's reasons are not corrupted. No cache
                // rollback needed — a cache entry is self-contained, and we only
                // ever store on full success (never a truncated set).
                reasons.truncate(start);
            }
        }
        false
    }

    /// Debug-only oracle for the batch explain cache
    /// (#i6-euf-explain-batch-memo): recompute the reason set for `(a, b)`
    /// WITHOUT the cache and assert it equals the just-appended cached slice
    /// `reasons[start..]` (as normalized literal sets). Guards against a stale
    /// cache entry surviving a forest mutation inside the cache lifetime.
    #[cfg(debug_assertions)]
    fn debug_assert_cached_explain(
        &mut self,
        a: TermId,
        b: TermId,
        start: usize,
        reasons: &[TheoryLit],
    ) {
        let root_a = self.find_proof_root(a.0);
        let root_b = self.find_proof_root(b.0);
        debug_assert_eq!(
            root_a, root_b,
            "cached explain for ({}, {}) but roots differ on recompute",
            a.0, b.0
        );
        // Recompute with the cache DISABLED (empty throwaway memo + memo gate
        // off) so no nested cache hit / recursive oracle fires — a full,
        // canonical re-walk of every sub-pair.
        let saved = self.explain_memo_enabled;
        self.explain_memo_enabled = false;
        let mut fresh: Vec<TheoryLit> = Vec::new();
        let mut throwaway = ExplainMemo::default();
        let lca = self.find_lca(a.0, b.0);
        let ok = self.collect_path_reasons_proof_forest(a.0, lca, &mut fresh, &mut throwaway)
            && self.collect_path_reasons_proof_forest(b.0, lca, &mut fresh, &mut throwaway);
        self.explain_memo_enabled = saved;
        debug_assert!(
            ok,
            "cached explain for ({}, {}) but recompute failed",
            a.0, b.0
        );
        let norm = |v: &[TheoryLit]| -> Vec<(u32, bool)> {
            let mut k: Vec<(u32, bool)> = v.iter().map(|l| (l.term.0, l.value)).collect();
            k.sort_unstable();
            k.dedup();
            k
        };
        debug_assert_eq!(
            norm(&reasons[start..]),
            norm(&fresh),
            "cached explain reasons diverged from fresh recompute for ({}, {})",
            a.0,
            b.0
        );
    }

    /// Explain why two terms are equal.
    ///
    /// In incremental mode: uses proof-forest LCA traversal (O(depth), no allocation).
    /// In legacy mode: falls back to BFS over equality_edges HashMap.
    ///
    /// The proof-forest approach fixes #3934: pop() no longer destroys pre-push
    /// equality information because proof edges are undone per-scope via
    /// UnmergeProofForest undo records, rather than cleared wholesale.
    pub fn explain(&mut self, a: TermId, b: TermId) -> Vec<TheoryLit> {
        // Standalone call: use the reusable per-call cache (kept on `self` only
        // for its capacity), cleared so no state leaks across independent calls.
        // A re-entrant BFS-fallback `explain` takes its own via this same path.
        let mut memo = std::mem::take(&mut self.explain_memo);
        memo.clear();
        let out = self.explain_using_memo(a, b, &mut memo);
        self.explain_memo = memo;
        out
    }

    /// Core of `explain`, parameterized by the reason cache so a caller can
    /// share ONE cache across a whole batch of pairs (see
    /// `propagate_equalities`, #i6-euf-explain-batch-memo). The cache is NOT
    /// cleared here, so the batch reuses shared congruence sub-proofs across
    /// calls; `explain` itself clears before delegating for standalone use.
    pub(crate) fn explain_using_memo(
        &mut self,
        a: TermId,
        b: TermId,
        memo: &mut ExplainMemo,
    ) -> Vec<TheoryLit> {
        let debug = self.debug_euf;
        self.debug_assert_solver_term_index(a, "explain lhs");
        self.debug_assert_solver_term_index(b, "explain rhs");
        if a == b {
            return Vec::new();
        }

        // Use proof-forest when available (incremental mode with initialized enodes)
        if self.enodes_init
            && (a.0 as usize) < self.enodes.len()
            && (b.0 as usize) < self.enodes.len()
        {
            let root_a = self.find_proof_root(a.0);
            let root_b = self.find_proof_root(b.0);
            if root_a == root_b {
                // Collect reasons across the whole proof-forest recursion into one
                // buffer, then sort+dedup ONCE here (see `explain_into`). This
                // replaces the old per-recursion sort+dedup, which did O(depth)
                // redundant sorts on deep congruence chains.
                let mut reasons = Vec::new();
                let did = self.explain_into(a, b, &mut reasons, memo);
                if did {
                    if debug {
                        safe_eprintln!(
                            "[EUF EXPLAIN] Proof-forest: {} to {}, {} reasons",
                            a.0,
                            b.0,
                            reasons.len()
                        );
                    }

                    reasons.sort_unstable_by_key(|l| (l.term.0, l.value));
                    reasons.dedup_by_key(|l| (l.term.0, l.value));
                    return reasons;
                }
                // Proof-forest walk failed (broken path or missing shared reason).
                // Fall through to BFS. (#6849, #3710)
                if debug {
                    safe_eprintln!(
                        "[EUF EXPLAIN] Proof-forest walk failed for {} to {}, BFS fallback",
                        a.0,
                        b.0
                    );
                }
            }
            // Not in same proof tree — fall through to BFS
            if debug {
                safe_eprintln!(
                    "[EUF EXPLAIN] Proof-forest: {} and {} not in same tree, BFS fallback",
                    a.0,
                    b.0
                );
            }
        }
        // Legacy BFS fallback (non-incremental mode or proof-forest unavailable)
        // We need to find paths through the actual term graph, not just representatives
        let mut visited: HashSet<u32> = HashSet::default();
        let mut queue: VecDeque<u32> = VecDeque::new();
        let mut parent: HashMap<u32, (u32, EqualityReason)> = HashMap::default();

        queue.push_back(a.0);
        visited.insert(a.0);

        // Build adjacency from equality_edges.
        // Sort neighbor lists by node ID for deterministic BFS paths (#3041).
        let mut adj: HashMap<u32, Vec<(u32, EqualityReason)>> = HashMap::default();
        for (&(x, y), reason) in &self.equality_edges {
            adj.entry(x).or_default().push((y, reason.clone()));
            adj.entry(y).or_default().push((x, reason.clone()));
        }
        for neighbors in adj.values_mut() {
            neighbors.sort_by_key(|(node, _)| *node);
        }

        while let Some(curr) = queue.pop_front() {
            if curr == b.0 {
                break;
            }
            if let Some(neighbors) = adj.get(&curr) {
                for (next, reason) in neighbors {
                    if !visited.contains(next) {
                        visited.insert(*next);
                        parent.insert(*next, (curr, reason.clone()));
                        queue.push_back(*next);
                    }
                }
            }
        }

        let mut reasons = Vec::new();
        let mut curr = b.0;

        if !parent.contains_key(&curr) && curr != a.0 {
            if debug {
                safe_eprintln!(
                    "[EUF EXPLAIN] No path from {} to {}, falling back",
                    a.0,
                    b.0
                );
            }
            return self.all_true_equalities();
        }

        while curr != a.0 {
            if let Some((prev, reason)) = parent.get(&curr) {
                self.collect_reason_literals(*prev, curr, reason, &mut reasons);
                curr = *prev;
            } else {
                break;
            }
        }

        if debug {
            safe_eprintln!(
                "[EUF EXPLAIN] Path from {} to {} needs {} reasons",
                a.0,
                b.0,
                reasons.len()
            );
        }

        reasons.sort_unstable_by_key(|l| (l.term.0, l.value));
        reasons.dedup_by_key(|l| (l.term.0, l.value));

        reasons
    }

    /// Recursively collect the direct equality literals for a reason
    pub(crate) fn collect_reason_literals(
        &mut self,
        a: u32,
        b: u32,
        reason: &EqualityReason,
        out: &mut Vec<TheoryLit>,
    ) {
        match reason {
            EqualityReason::Direct(eq_term) => {
                out.push(TheoryLit::new(*eq_term, true));
            }
            EqualityReason::Congruence { arg_pairs, .. } => {
                // For each argument pair that are in the same equivalence class,
                // we need to explain why they're equal
                for &(arg_a, arg_b) in arg_pairs {
                    // Use incremental enode structure if available, otherwise use uf
                    let (rep_a, rep_b) = (
                        self.enode_find_const(arg_a.0),
                        self.enode_find_const(arg_b.0),
                    );
                    if rep_a == rep_b && arg_a != arg_b {
                        // Recursively explain why arg_a = arg_b
                        let sub_reasons = self.explain(arg_a, arg_b);
                        out.extend(sub_reasons);
                    }
                }
            }
            EqualityReason::Shared => {
                // Shared equalities come from Nelson-Oppen with their own reasons
                // which are already tracked separately. For conflict explanation,
                // we look up the shared equality's reason literals.
                let key = Self::edge_key(a, b);
                if let Some(lits) = self.shared_equality_reasons.get(&key) {
                    out.extend(lits.iter().copied());
                }
            }
            EqualityReason::BoolValue { term, value } => {
                // Both endpoints share the same Bool truth value.
                // The reason is the truth-value assignment of both terms. (#4610)
                // #bool-arg-congruence: unwrap `Not` so reason literals reference
                // the SAT-owned atom (Not(inner)=v ⟺ inner=!v); constant
                // endpoints contribute no literal (skip None).
                if let Some(lit) = self.bool_value_reason_lit(*term, *value) {
                    out.push(lit);
                }
                // The other endpoint (the canonical representative) was merged
                // first and is found via the edge endpoints (a, b).
                let other = if *term == TermId(a) {
                    TermId(b)
                } else {
                    TermId(a)
                };
                if let Some(lit) = self.bool_value_reason_lit(other, *value) {
                    out.push(lit);
                }
            }
            EqualityReason::Ite { condition, value } => {
                // ITE axiom: ite(c,t,e) = t when c=true, or ite(c,t,e) = e when c=false.
                // The reason is the truth-value assignment of the condition. (#5081)
                out.push(TheoryLit::new(*condition, *value));
            }
        }
    }

    #[allow(clippy::unused_self)] // method for consistency; may use self in future
    pub(crate) fn conflict_with_reasons(
        &self,
        mut reasons: Vec<TheoryLit>,
        lit: TheoryLit,
    ) -> TheoryResult {
        reasons.push(lit);
        // Keep the clause reasonably small by removing duplicates.
        reasons.sort_unstable_by_key(|l| (l.term, l.value));
        reasons.dedup_by_key(|l| (l.term, l.value));
        TheoryResult::Unsat(reasons)
    }
}
