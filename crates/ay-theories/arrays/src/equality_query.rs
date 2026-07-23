// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality query and explanation methods for the array theory solver.
//!
//! Provides:
//! - known_equal / known_distinct queries
//! - Equivalence class retrieval and representative computation
//! - Select conflict candidate pair generation
//! - Equality/disequality explanation for conflict clause generation
//! - BFS equality path search

use super::*;

impl ArraySolver<'_> {
    fn canonicalize_explanation(reasons: &mut Vec<TheoryLit>) {
        reasons.sort_by_key(|lit| (lit.term.0, lit.value));
        reasons.dedup_by_key(|lit| (lit.term, lit.value));
    }

    fn explanation_better(candidate: &[TheoryLit], best: &[TheoryLit]) -> bool {
        candidate.len() < best.len()
            || (candidate.len() == best.len()
                && candidate
                    .iter()
                    .map(|lit| (lit.term.0, lit.value))
                    .lt(best.iter().map(|lit| (lit.term.0, lit.value))))
    }

    /// Check if two terms are known to be equal (direct equality asserted). O(1) via pair index.
    pub(crate) fn known_equal(&self, t1: TermId, t2: TermId) -> bool {
        if t1 == t2 {
            return true;
        }
        let key = Self::ordered_pair(t1, t2);
        if let Some(&eq_term) = self.eq_pair_index.get(&key) {
            if self.assigns.get(&eq_term) == Some(&true) {
                // M1: a directly-asserted equality is an eq_adj edge, so the
                // shadow union-find must agree whenever it mirrors the graph
                // (warm indices, no pending late registrations, not stale).
                #[cfg(debug_assertions)]
                debug_assert!(
                    self.dirty
                        || self.assign_dirty
                        || self.shadow_uf_stale
                        || !self.pending_registered_equalities.is_empty()
                        || !self.equality_cache.contains_key(&eq_term)
                        || self.shadow_uf.same_class(t1, t2),
                    "arrays M1: known_equal={t1:?}={t2:?} (via {eq_term:?}) \
                     but shadow union-find disagrees"
                );
                return true;
            }
        }
        self.equal_by_affine_form(t1, t2)
    }

    /// Check if two terms are known to be distinct.
    ///
    /// Uses O(1) constant check, O(1) diseq_set lookup, and O(|C1|×|C2|)
    /// equivalence class cross-product. Does NOT perform equality-substituted
    /// affine BFS (#6820): that reasoning belongs in the arithmetic theory,
    /// not the array theory. Z3 parity: `are_distinct()` is O(1) unique-value
    /// check only; index disequalities from `i = j + k` are propagated by
    /// the LRA/LIA solver into the EUF diseq_set.
    pub(crate) fn known_distinct(&self, t1: TermId, t2: TermId) -> bool {
        if t1 == t2 {
            return false;
        }

        // O(1): both are distinct constants (Z3 parity: is_unique_value).
        if self.known_distinct_direct(t1, t2) {
            return true;
        }

        // O(|C1|×|C2|): check equiv class members against diseq_set.
        self.known_distinct_via_equiv_classes(t1, t2)
    }

    /// Check equivalence class cross-product for known disequalities.
    fn known_distinct_via_equiv_classes(&self, t1: TermId, t2: TermId) -> bool {
        if self.equiv_class_cache_version == Some(self.eq_adj_version) {
            let c1 = self
                .equiv_class_map
                .get(&t1)
                .map(|&i| self.equiv_classes[i].as_slice());
            let c2 = self
                .equiv_class_map
                .get(&t2)
                .map(|&i| self.equiv_classes[i].as_slice());
            let t1_singleton = [t1];
            let t2_singleton = [t2];
            let c1 = c1.unwrap_or(&t1_singleton);
            let c2 = c2.unwrap_or(&t2_singleton);
            for &t1_equiv in c1 {
                for &t2_equiv in c2 {
                    if self.known_distinct_direct(t1_equiv, t2_equiv) {
                        return true;
                    }
                }
            }
        } else {
            // Fallback: BFS (used when cache hasn't been built yet, e.g. during propagate)
            let t1_class = self.get_equiv_class_bfs(t1);
            let t2_class = self.get_equiv_class_bfs(t2);
            for &t1_equiv in &t1_class {
                for &t2_equiv in &t2_class {
                    if self.known_distinct_direct(t1_equiv, t2_equiv) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Get the equivalence class of a term. Uses cached equiv classes when
    /// available (O(1) lookup), falls back to BFS when the cache is stale or unavailable.
    pub(crate) fn get_equiv_class(&self, term: TermId) -> Vec<TermId> {
        if self.equiv_class_cache_version == Some(self.eq_adj_version) {
            if let Some(&class_idx) = self.equiv_class_map.get(&term) {
                return self.equiv_classes[class_idx].clone();
            }
            // Term not in eq_adj — singleton class
            return vec![term];
        }

        self.equiv_class_shared(term).to_vec()
    }

    /// Shared-ownership equivalence class of `term`, memoized per
    /// `eq_adj_version`.
    ///
    /// Hot-path variant of `get_equiv_class()`: `notify_equality()` /
    /// `row2_fingerprint_seen()` query classes once per store×select pair, and
    /// the raw BFS fallback made each query O(class × degree) (dominant cost
    /// on QF_ALIA cs_lazy.i_*, 2026-07-11 profile). One BFS fills the memo for
    /// every member of the discovered class; subsequent queries are O(1)
    /// clones of an `Rc`. The memo is invalidated by `eq_adj_version`, exactly
    /// the staleness key the full `build_equiv_class_cache()` uses.
    pub(crate) fn equiv_class_shared(&self, term: TermId) -> Rc<[TermId]> {
        let mut cache = self.lazy_equiv_classes.borrow_mut();
        let (version, classes) = &mut *cache;
        if *version != Some(self.eq_adj_version) {
            classes.clear();
            *version = Some(self.eq_adj_version);
        }
        if let Some(class) = classes.get(&term) {
            return Rc::clone(class);
        }
        let class: Rc<[TermId]> = if self.equiv_class_cache_version == Some(self.eq_adj_version) {
            match self.equiv_class_map.get(&term) {
                Some(&class_idx) => Rc::from(self.equiv_classes[class_idx].as_slice()),
                None => Rc::from([term]),
            }
        } else {
            Rc::from(self.get_equiv_class_bfs(term))
        };
        for &member in class.iter() {
            classes.insert(member, Rc::clone(&class));
        }
        class
    }

    pub(crate) fn equiv_class_representative(&self, term: TermId) -> TermId {
        if self.equiv_class_cache_version == Some(self.eq_adj_version) {
            if let Some(&class_idx) = self.equiv_class_map.get(&term) {
                return self.equiv_classes[class_idx]
                    .iter()
                    .copied()
                    .min()
                    .unwrap_or(term);
            }
            return term;
        }

        self.get_equiv_class_bfs(term)
            .into_iter()
            .min()
            .unwrap_or(term)
    }

    /// Return select-term pairs that may have concrete distinctness evidence.
    ///
    /// Candidate discovery is intentionally cheap: the consumers re-check
    /// distinctness with explanations before producing any lemma. Avoid doing
    /// that proof search here too, because ROW2/storecomm final checks call this
    /// path repeatedly on large formulas.
    ///
    /// Memoized in the `eq_paths_cache` window (D1, SELECT-PAIRS blueprint):
    /// inside `propagate_equalities_impl`'s read-only scan the inputs
    /// (`select_cache`, class connectivity, `diseq_set`, term constants) are
    /// frozen, so a memo hit is byte-identical to recomputation (the output is
    /// sorted). Outside the window every call recomputes, exactly as before.
    pub(crate) fn select_conflict_candidate_pairs(&self) -> Rc<[(TermId, TermId)]> {
        self.candidate_pairs_calls
            .set(self.candidate_pairs_calls.get() + 1);
        if let Some(hit) = eq_paths_cache::get_candidate_pairs() {
            self.candidate_pairs_memo_hits
                .set(self.candidate_pairs_memo_hits.get() + 1);
            // M1 gate (4): spot-check (debug builds, 1-in-32 hits) that the
            // memoized set equals a fresh recomputation.
            #[cfg(debug_assertions)]
            if self.candidate_pairs_memo_hits.get().is_multiple_of(32) {
                debug_assert_eq!(
                    *hit,
                    *self.select_conflict_candidate_pairs_uncached(),
                    "arrays D1: memoized candidate-pair set must equal fresh recomputation"
                );
            }
            return hit;
        }
        let pairs: Rc<[(TermId, TermId)]> =
            Rc::from(self.select_conflict_candidate_pairs_uncached());
        self.candidate_pairs_generated
            .set(self.candidate_pairs_generated.get() + pairs.len() as u64);
        eq_paths_cache::put_candidate_pairs(&pairs);
        pairs
    }

    fn select_conflict_candidate_pairs_uncached(&self) -> Vec<(TermId, TermId)> {
        let insert_candidate =
            |candidate_pairs: &mut HashSet<(TermId, TermId)>, sel1: TermId, sel2: TermId| {
                if sel1 == sel2 {
                    return;
                }
                candidate_pairs.insert(Self::ordered_pair(sel1, sel2));
            };

        let mut selects_by_class: HashMap<TermId, Vec<TermId>> = HashMap::default();
        for &select_term in self.select_cache.keys() {
            selects_by_class
                .entry(self.equiv_class_representative(select_term))
                .or_default()
                .push(select_term);
        }
        for select_terms in selects_by_class.values_mut() {
            select_terms.sort_unstable_by_key(|term| term.0);
            select_terms.dedup();
        }

        // D2 (SELECT-PAIRS blueprint): dedup by CLASS PAIR before taking
        // cross-products. k parallel disequalities between the same two
        // classes previously redid the identical |C1|x|C2| insert storm k
        // times; the produced pair SET is unchanged (it was already deduped
        // at insert price in the HashSet below).
        let mut class_pairs: HashSet<(TermId, TermId)> = HashSet::default();
        for &(lhs, rhs) in &self.diseq_set {
            let lhs_class = self.equiv_class_representative(lhs);
            let rhs_class = self.equiv_class_representative(rhs);
            if !selects_by_class.contains_key(&lhs_class)
                || !selects_by_class.contains_key(&rhs_class)
            {
                continue;
            }
            class_pairs.insert(Self::ordered_pair(lhs_class, rhs_class));
        }

        let mut class_constants = Vec::new();
        for (&class_key, select_terms) in &selects_by_class {
            let constant = self
                .get_equiv_class(select_terms[0])
                .into_iter()
                .find_map(|term| match self.terms.get(term) {
                    TermData::Const(constant) => Some(constant.clone()),
                    _ => None,
                });
            if let Some(constant) = constant {
                class_constants.push((class_key, constant));
            }
        }
        class_constants.sort_unstable_by_key(|(class_key, _)| class_key.0);
        for i in 0..class_constants.len() {
            for j in (i + 1)..class_constants.len() {
                if class_constants[i].1 == class_constants[j].1 {
                    continue;
                }
                // Classes both disequal AND constant-distinct are enumerated
                // once: the class-pair set already dedups them (D2).
                class_pairs.insert(Self::ordered_pair(
                    class_constants[i].0,
                    class_constants[j].0,
                ));
            }
        }

        // INDEX-KEYED PRUNING. Both consumers of this candidate set discard any
        // pair whose two selects' indices are not provably equal (via
        // `explain_equal_if_provable` / `known_equal`). Partition the distinct
        // index terms into blocks that are a SOUND OVER-APPROXIMATION of that
        // index-equality relation `R` (see `index_conflict_partition`): every
        // pair the consumers would keep has both indices in one block, so
        // pairing only WITHIN a shared index block preserves the exact conflict
        // set while collapsing the store-permutation cross-products from
        // O(selects²) to O(Σ block-restricted products). Because the produced
        // set is a subset of the old one and is emitted through the SAME final
        // sort, surviving pairs keep byte-identical order.
        let mut index_terms: Vec<TermId> =
            self.select_cache.values().map(|&(_arr, idx)| idx).collect();
        index_terms.sort_unstable_by_key(|t| t.0);
        index_terms.dedup();
        let index_block = self.index_conflict_partition(&index_terms);
        let select_index_block = |sel: TermId| -> Option<TermId> {
            let &(_arr, idx) = self.select_cache.get(&sel)?;
            index_block.get(&idx).copied()
        };

        // Per value class: index block -> selects (preserving the sorted order
        // already established on `selects_by_class`).
        let mut class_block_groups: HashMap<TermId, HashMap<TermId, Vec<TermId>>> =
            HashMap::default();
        for (&class_rep, class_selects) in &selects_by_class {
            let mut groups: HashMap<TermId, Vec<TermId>> = HashMap::default();
            for &sel in class_selects {
                if let Some(block) = select_index_block(sel) {
                    groups.entry(block).or_default().push(sel);
                }
            }
            class_block_groups.insert(class_rep, groups);
        }

        let mut candidate_pairs = HashSet::default();
        for &(lhs_class, rhs_class) in &class_pairs {
            let lhs_groups = &class_block_groups[&lhs_class];
            let rhs_groups = &class_block_groups[&rhs_class];
            // Walk the smaller block map; only shared blocks can yield pairs
            // whose indices are provably equal.
            let (small, large) = if lhs_groups.len() <= rhs_groups.len() {
                (lhs_groups, rhs_groups)
            } else {
                (rhs_groups, lhs_groups)
            };
            for (block, small_selects) in small {
                let Some(large_selects) = large.get(block) else {
                    continue;
                };
                for &sel_a in small_selects {
                    for &sel_b in large_selects {
                        insert_candidate(&mut candidate_pairs, sel_a, sel_b);
                    }
                }
            }
        }

        let mut candidate_pairs: Vec<_> = candidate_pairs.into_iter().collect();
        candidate_pairs.sort_unstable_by_key(|&(lhs, rhs)| (lhs.0, rhs.0));
        candidate_pairs
    }

    /// Equivalence class of `term` when neither eager cache is current: the
    /// union-find serves it in O(class) member-copy with an O(log) find (M2);
    /// the eq_adj BFS remains as the fallback while the union-find is stale
    /// and as the debug-build oracle.
    fn get_equiv_class_bfs(&self, term: TermId) -> Vec<TermId> {
        if self.shadow_uf_ready() {
            let members = self.shadow_uf.class_members(term);
            // M2 switch guard: the union-find answer must match the BFS answer.
            #[cfg(debug_assertions)]
            {
                let mut uf_sorted = members.clone();
                uf_sorted.sort_unstable_by_key(|t| t.0);
                let mut bfs_sorted = self.get_equiv_class_bfs_via_eq_adj(term);
                bfs_sorted.sort_unstable_by_key(|t| t.0);
                debug_assert_eq!(
                    uf_sorted, bfs_sorted,
                    "arrays M2: union-find class of {term:?} must equal the eq_adj BFS class"
                );
            }
            return members;
        }
        self.get_equiv_class_bfs_via_eq_adj(term)
    }

    /// Legacy eq_adj BFS (pre-M2 read path); fallback + debug oracle.
    fn get_equiv_class_bfs_via_eq_adj(&self, term: TermId) -> Vec<TermId> {
        let mut class = vec![term];
        let mut to_process = vec![term];
        let mut seen = HashSet::default();
        seen.insert(term);

        while let Some(t) = to_process.pop() {
            if let Some(neighbors) = self.eq_adj.get(&t) {
                for &(other, _eq_term) in neighbors {
                    if seen.insert(other) {
                        class.push(other);
                        to_process.push(other);
                    }
                }
            }
        }

        class
    }

    /// Build equality paths as SAT-visible reasons.
    ///
    /// Asserted equality edges contribute their equality atom. Reason-carrying
    /// external equality edges contribute their stored guards. Unreasoned
    /// external equality edges are skipped so callers cannot produce a guarded
    /// conflict explanation that depends on an unguarded sentinel edge.
    /// Cached wrapper over `equality_reason_paths_from_uncached` (#no-cross-flood).
    /// Caching is enabled ONLY inside the read-only `propagate_equalities_impl`
    /// window (via `EqPathsCache::activate`), where `eq_adj`, `assigns` and the
    /// external-fact maps are provably immutable — so a cache hit is
    /// byte-identical to a recomputation and no staleness is possible. Outside
    /// that window every query recomputes, i.e. exactly the pre-cache path.
    fn equality_reason_paths_from(&self, start: TermId) -> Rc<HashMap<TermId, Vec<TheoryLit>>> {
        if let Some(hit) = eq_paths_cache::get_paths(start) {
            return hit;
        }
        let paths = Rc::new(self.equality_reason_paths_from_uncached(start));
        eq_paths_cache::put_paths(start, &paths);
        paths
    }

    fn equality_reason_paths_from_uncached(
        &self,
        start: TermId,
    ) -> HashMap<TermId, Vec<TheoryLit>> {
        // M2 note: the reason MAP stays on the eq_adj BFS. The union-find proof
        // forest produces a VALID explanation, but a *different* (union-tree,
        // not graph-shortest) one; the downstream ROW2 shadowing / lemma
        // selection is sensitive to which reasons back an equality, and a
        // non-shortest path was observed to change a produced model (arrays
        // diff-fuzz seed 2303). The blueprint's proof-lane risk (§5) requires
        // preserving the shortest/asserted `explanation_better` preference, so
        // reason CONTENT is left byte-identical to M1. The union-find is used
        // as the connectivity ORACLE on the asserted path below (a
        // behaviour-neutral negative short-circuit), and the forest walk
        // (`ArrayUnionFind::explain`) is validated + reserved for M3's delta
        // export where reason-shape stability is re-established holistically.
        let mut paths = HashMap::default();
        let mut queue = std::collections::VecDeque::new();
        paths.insert(start, Vec::new());
        queue.push_back(start);

        while let Some(current) = queue.pop_front() {
            let current_path = paths.get(&current).cloned().unwrap_or_default();
            if let Some(neighbors) = self.eq_adj.get(&current) {
                for &(other, eq_term) in neighbors {
                    if paths.contains_key(&other) {
                        continue;
                    }

                    let mut next_path = current_path.clone();
                    if eq_term.is_sentinel() {
                        let key = Self::ordered_pair(current, other);
                        let Some(edge_reasons) = self.external_eq_reasons.get(&key) else {
                            continue;
                        };
                        if edge_reasons.is_empty() {
                            continue;
                        }
                        next_path.extend(edge_reasons.iter().copied());
                    } else {
                        if self.assigns.get(&eq_term) != Some(&true) {
                            continue;
                        }
                        next_path.push(TheoryLit::new(eq_term, true));
                    }

                    paths.insert(other, next_path);
                    queue.push_back(other);
                }
            }
        }

        paths
    }

    /// Build an asserted-equality path between two terms.
    ///
    /// Like `equality_paths_from`, this skips sentinel edges so the result
    /// contains only asserted equality atoms.
    fn asserted_equality_path(&self, start: TermId, goal: TermId) -> Option<Vec<TermId>> {
        if start == goal {
            return Some(Vec::new());
        }

        // M2: union-find connectivity as a behaviour-neutral NEGATIVE
        // short-circuit. Asserted-only connectivity is a subset of the
        // union-find's full connectivity (asserted + external edges), so a pair
        // in DIFFERENT union-find classes provably has no asserted BFS path
        // either — skip the BFS entirely. The positive case falls through to
        // the BFS so the returned path stays the graph-SHORTEST asserted one
        // (proof-lane risk §5: the union-tree path is valid but a different
        // shape and must not replace the shortest-path reasons here).
        if self.shadow_uf_ready() && !self.shadow_uf.same_class(start, goal) {
            #[cfg(debug_assertions)]
            debug_assert!(
                self.asserted_equality_path_bfs(start, goal).is_none(),
                "arrays M2: union-find says {start:?} and {goal:?} are disconnected \
                 but the asserted-edge BFS found a path"
            );
            return None;
        }

        // #k1-explain-memo: inside a frozen-graph `eq_paths_cache` window,
        // run the BFS from `start` to EXHAUSTION once, memoize the predecessor
        // forest, and reconstruct every subsequent `(start, *)` query from it.
        // BFS discovery (and thus each node's recorded predecessor) is
        // deterministic and independent of any early exit, so the
        // reconstructed path is byte-identical to the legacy per-goal BFS —
        // only the O(component) re-traversal per query is saved. This is the
        // A1 permutation-conflict divergence fix: candidate-pair scans issue
        // O(pairs) same-class queries over the same component, which the
        // legacy path recomputed from scratch every time (#8373/#A1 chain).
        if let Some(window) = eq_paths_cache::get_asserted_prev(start) {
            let prev = match window {
                Some(prev) => prev,
                None => {
                    let prev = Rc::new(self.asserted_equality_prev_forest(start));
                    eq_paths_cache::put_asserted_prev(start, &prev);
                    prev
                }
            };
            let result = Self::reconstruct_asserted_path(&prev, start, goal);
            #[cfg(debug_assertions)]
            debug_assert_eq!(
                result,
                self.asserted_equality_path_bfs(start, goal),
                "arrays #k1-explain-memo: forest-reconstructed asserted path must be \
                 byte-identical to the legacy early-exit BFS ({start:?} -> {goal:?})"
            );
            return result;
        }
        self.asserted_equality_path_bfs(start, goal)
    }

    /// Full-traversal variant of `asserted_equality_path_bfs`: BFS from
    /// `start` over asserted (non-sentinel, assigned-true) equality edges to
    /// exhaustion, returning the predecessor forest `node -> (parent, eq)`.
    /// Iteration order matches `asserted_equality_path_bfs` exactly, so each
    /// node's predecessor entry is identical to what the early-exit BFS would
    /// have recorded when reaching that node.
    fn asserted_equality_prev_forest(&self, start: TermId) -> HashMap<TermId, (TermId, TermId)> {
        let mut queue = std::collections::VecDeque::new();
        let mut seen = HashSet::default();
        let mut prev: HashMap<TermId, (TermId, TermId)> = HashMap::default();
        queue.push_back(start);
        seen.insert(start);

        while let Some(current) = queue.pop_front() {
            let Some(neighbors) = self.eq_adj.get(&current) else {
                continue;
            };
            for &(other, eq_term) in neighbors {
                if eq_term.is_sentinel()
                    || self.assigns.get(&eq_term) != Some(&true)
                    || !seen.insert(other)
                {
                    continue;
                }
                prev.insert(other, (current, eq_term));
                queue.push_back(other);
            }
        }

        prev
    }

    /// Reconstruct the `start -> goal` asserted equality path from a
    /// predecessor forest produced by `asserted_equality_prev_forest`.
    fn reconstruct_asserted_path(
        prev: &HashMap<TermId, (TermId, TermId)>,
        start: TermId,
        goal: TermId,
    ) -> Option<Vec<TermId>> {
        if !prev.contains_key(&goal) {
            return None;
        }
        let mut path = Vec::new();
        let mut cursor = goal;
        while cursor != start {
            let &(parent, via_eq) = prev.get(&cursor)?;
            path.push(via_eq);
            cursor = parent;
        }
        path.reverse();
        Some(path)
    }

    /// Legacy asserted-edge BFS (pre-M2 read path); fallback + debug oracle.
    fn asserted_equality_path_bfs(&self, start: TermId, goal: TermId) -> Option<Vec<TermId>> {
        if start == goal {
            return Some(Vec::new());
        }

        let mut queue = std::collections::VecDeque::new();
        let mut seen = HashSet::default();
        let mut prev: HashMap<TermId, (TermId, TermId)> = HashMap::default();
        queue.push_back(start);
        seen.insert(start);

        while let Some(current) = queue.pop_front() {
            let Some(neighbors) = self.eq_adj.get(&current) else {
                continue;
            };
            for &(other, eq_term) in neighbors {
                if eq_term.is_sentinel()
                    || self.assigns.get(&eq_term) != Some(&true)
                    || !seen.insert(other)
                {
                    continue;
                }
                prev.insert(other, (current, eq_term));
                if other == goal {
                    let mut path = Vec::new();
                    let mut cursor = goal;
                    while cursor != start {
                        let &(parent, via_eq) = prev.get(&cursor)?;
                        path.push(via_eq);
                        cursor = parent;
                    }
                    path.reverse();
                    return Some(path);
                }
                queue.push_back(other);
            }
        }

        None
    }

    /// Explain why two terms are provably equal using only SAT-visible reasons.
    ///
    /// Returns:
    /// - `Some(vec![])` for tautological equalities (syntactic identity or
    ///   direct affine normalization)
    /// - `Some(non_empty)` when asserted equality atoms prove the equality
    /// - `None` when the equality is not provable without external/model-based
    ///   assumptions
    ///
    /// Call-scoped memoized wrapper (#no-cross-flood): during the read-only
    /// `propagate_equalities_impl` window this is a pure function of immutable
    /// state, so caching its result by the exact `(t1, t2)` is behaviour-neutral.
    pub(crate) fn explain_equal_if_provable(
        &self,
        t1: TermId,
        t2: TermId,
    ) -> Option<Vec<TheoryLit>> {
        if let Some(hit) = eq_paths_cache::get_equal(t1, t2) {
            return hit;
        }
        let reason = self.explain_equal_if_provable_uncached(t1, t2);
        eq_paths_cache::put_equal(t1, t2, &reason);
        reason
    }

    fn explain_equal_if_provable_uncached(&self, t1: TermId, t2: TermId) -> Option<Vec<TheoryLit>> {
        if let Some(reasons) = self.explain_equal_if_provable_base(t1, t2) {
            return Some(reasons);
        }
        // #7956 index-congruence: affine equality modulo provably-equal opaque
        // leaves (`(+ (seq_offset a) 1) = (+ (seq_offset b) 1)` given asserted
        // `(seq_offset a) = (seq_offset b)`). Leaf pairs are explained with the
        // BASE machinery only, so this cannot recurse. See the soundness note
        // on `explain_equal_by_affine_leaf_congruence`.
        self.explain_equal_by_affine_leaf_congruence(t1, t2)
    }

    /// Pre-#7956-index-congruence explanation core: syntactic identity /
    /// structural affine identity / direct asserted atom / asserted-equality
    /// BFS path. Used directly by the leaf-congruence matcher so the extended
    /// path stays non-recursive.
    pub(crate) fn explain_equal_if_provable_base(
        &self,
        t1: TermId,
        t2: TermId,
    ) -> Option<Vec<TheoryLit>> {
        if t1 == t2 || self.equal_by_affine_form(t1, t2) {
            return Some(Vec::new());
        }

        if let Some(eq_term) = self.get_eq_term(t1, t2) {
            if self.assigns.get(&eq_term) == Some(&true) {
                return Some(vec![TheoryLit::new(eq_term, true)]);
            }
        }

        let mut reasons: Vec<_> = self
            .asserted_equality_path(t1, t2)?
            .into_iter()
            .map(|eq_term| TheoryLit::new(eq_term, true))
            .collect();
        reasons.sort_by_key(|lit| (lit.term.0, lit.value));
        reasons.dedup_by_key(|lit| (lit.term, lit.value));
        Some(reasons)
    }

    /// Reconstruct a non-empty explanation for `t1 ≠ t2` when possible.
    fn explain_distinct(&self, t1: TermId, t2: TermId) -> Vec<TheoryLit> {
        if let Some(eq_term) = self.get_eq_term(t1, t2) {
            if self.assigns.get(&eq_term) == Some(&false) {
                return vec![TheoryLit::new(eq_term, false)];
            }
        }

        let lhs_paths = self.equality_reason_paths_from(t1);
        let rhs_paths = self.equality_reason_paths_from(t2);
        let mut best: Option<Vec<TheoryLit>> = None;

        for (lhs_rep, lhs_path) in lhs_paths.iter() {
            for (rhs_rep, rhs_path) in rhs_paths.iter() {
                if let (TermData::Const(lhs_const), TermData::Const(rhs_const)) =
                    (self.terms.get(*lhs_rep), self.terms.get(*rhs_rep))
                {
                    if lhs_const != rhs_const {
                        let mut reasons = Vec::new();
                        reasons.extend(lhs_path.iter().copied());
                        reasons.extend(rhs_path.iter().copied());
                        Self::canonicalize_explanation(&mut reasons);
                        if !reasons.is_empty() {
                            match &best {
                                Some(best_reasons)
                                    if !Self::explanation_better(&reasons, best_reasons) => {}
                                _ => best = Some(reasons),
                            }
                        }
                    }
                }

                if let Some(eq_term) = self.get_eq_term(*lhs_rep, *rhs_rep) {
                    if self.assigns.get(&eq_term) == Some(&false) {
                        let mut reasons = Vec::new();
                        reasons.extend(lhs_path.iter().copied());
                        reasons.extend(rhs_path.iter().copied());
                        reasons.push(TheoryLit::new(eq_term, false));
                        Self::canonicalize_explanation(&mut reasons);
                        match &best {
                            Some(best_reasons)
                                if !Self::explanation_better(&reasons, best_reasons) => {}
                            _ => best = Some(reasons),
                        }
                    }
                }

                let key = Self::ordered_pair(*lhs_rep, *rhs_rep);
                if let Some(diseq_reasons) = self.external_diseq_reasons.get(&key) {
                    let mut reasons = Vec::new();
                    reasons.extend(lhs_path.iter().copied());
                    reasons.extend(rhs_path.iter().copied());
                    reasons.extend(diseq_reasons.iter().copied());
                    Self::canonicalize_explanation(&mut reasons);
                    if !reasons.is_empty() {
                        match &best {
                            Some(best_reasons)
                                if !Self::explanation_better(&reasons, best_reasons) => {}
                            _ => best = Some(reasons),
                        }
                    }
                }
            }
        }

        best.unwrap_or_default()
    }

    /// Check if two terms are provably distinct WITH explanation reasons (#5086).
    ///
    /// Returns `Some(reasons)` if the disequality is known AND can be explained
    /// (safe for conflict clause generation). Returns `None` if the disequality
    /// is not known or cannot be explained (external disequalities from model
    /// evaluation that lack SAT-level reason terms).
    ///
    /// This is the safe alternative to `known_distinct()` + `explain_distinct()`
    /// for all code paths that generate conflict clauses. Using `known_distinct()`
    /// alone is unsafe because external disequalities have no reason terms.
    /// Call-scoped memoized wrapper (#no-cross-flood): during the read-only
    /// `propagate_equalities_impl` window this is a pure function of immutable
    /// state, so caching its result by the exact `(t1, t2)` is behaviour-neutral.
    pub(crate) fn explain_distinct_if_provable(
        &self,
        t1: TermId,
        t2: TermId,
    ) -> Option<Vec<TheoryLit>> {
        if let Some(hit) = eq_paths_cache::get_distinct(t1, t2) {
            return hit;
        }
        let reason = self.explain_distinct_if_provable_uncached(t1, t2);
        eq_paths_cache::put_distinct(t1, t2, &reason);
        reason
    }

    fn explain_distinct_if_provable_uncached(
        &self,
        t1: TermId,
        t2: TermId,
    ) -> Option<Vec<TheoryLit>> {
        if t1 == t2 {
            return None;
        }
        if self.explain_equal_if_provable(t1, t2).is_some() {
            return None;
        }

        // O(1): distinct constants need no reasons (Z3 parity: is_unique_value).
        let t1_is_const = matches!(self.terms.get(t1), TermData::Const(_));
        let t2_is_const = matches!(self.terms.get(t2), TermData::Const(_));
        if t1_is_const && t2_is_const {
            return Some(Vec::new());
        }

        // O(1) tautological affine offset (i vs i+1) — no reasons needed.
        if self.distinct_by_affine_offset(t1, t2) {
            return Some(Vec::new());
        }

        if !self.known_distinct(t1, t2) {
            return None;
        }

        let reasons = self.explain_distinct(t1, t2);
        if reasons.is_empty() {
            // known_distinct returned true but explain_distinct returned empty.
            // Check if this is a reason-carrying external disequality (#6546).
            let key = Self::ordered_pair(t1, t2);
            self.external_diseq_reasons.get(&key).cloned()
        } else {
            Some(reasons)
        }
    }

    /// Direct distinctness check without transitivity. O(1) via diseq_set + constant check.
    fn known_distinct_direct(&self, t1: TermId, t2: TermId) -> bool {
        if t1 == t2 {
            return false;
        }

        // Check syntactic distinctness of constants
        let t1_is_const = matches!(self.terms.get(t1), TermData::Const(_));
        let t2_is_const = matches!(self.terms.get(t2), TermData::Const(_));
        if t1_is_const && t2_is_const {
            return true;
        }

        // O(1) lookup in disequality set
        let key = Self::ordered_pair(t1, t2);
        self.diseq_set.contains(&key)
    }

    /// Get the equality term for two terms if it exists. O(1) via pair index.
    pub(crate) fn get_eq_term(&self, t1: TermId, t2: TermId) -> Option<TermId> {
        let key = Self::ordered_pair(t1, t2);
        self.eq_pair_index.get(&key).copied()
    }

    pub(crate) fn get_exact_select_term(&self, array: TermId, index: TermId) -> Option<TermId> {
        self.select_pair_index.get(&(array, index)).copied()
    }

    /// Find `select(array_alias, index)` where `array_alias` is provably equal to
    /// `array`, keeping the select index exact.
    pub(crate) fn get_exact_select_term_on_provable_array_alias(
        &self,
        array: TermId,
        index: TermId,
    ) -> Option<(TermId, Vec<TheoryLit>)> {
        if let Some(select_term) = self.get_exact_select_term(array, index) {
            return Some((select_term, Vec::new()));
        }

        const MAX_ARRAY_ALIAS_SELECTS: usize = 64;
        let mut aliases = self.get_equiv_class(array);
        aliases.sort_unstable_by_key(|term| term.0);
        aliases.dedup();

        for alias in aliases
            .into_iter()
            .filter(|&alias| alias != array)
            .take(MAX_ARRAY_ALIAS_SELECTS)
        {
            let Some(select_term) = self.get_exact_select_term(alias, index) else {
                continue;
            };
            let Some(reasons) = self.explain_equal_if_provable(array, alias) else {
                continue;
            };
            return Some((select_term, reasons));
        }

        None
    }

    /// Public wrapper for `asserted_equality_path` used by `check_select_map`
    /// to collect SAT-visible equality reasons along an equality path (#8598).
    pub(crate) fn asserted_equality_path_pub(
        &self,
        start: TermId,
        goal: TermId,
    ) -> Option<Vec<TermId>> {
        self.asserted_equality_path(start, goal)
    }

    /// Search for a function application `f(v1, ..., vn)` in the term store
    /// where each `vi` is in the equivalence class of `arg_selects[i]` (#8598).
    ///
    /// Returns `Some((func_app_term, eq_reasons))` where `eq_reasons` are the
    /// TheoryLit reasons justifying each `arg_selects[i] = vi` substitution.
    /// Returns `None` if no matching application is found within the budget.
    ///
    /// Budget-limited to avoid exponential blowup on large equivalence classes.
    pub(crate) fn find_func_app_via_equiv_classes(
        &self,
        func_name: &str,
        arg_selects: &[TermId],
    ) -> Option<(TermId, Vec<TheoryLit>)> {
        const MAX_EQUIV_COMBINATIONS: usize = 64;

        let equiv_classes: Vec<Vec<TermId>> = arg_selects
            .iter()
            .map(|&t| self.get_equiv_class(t))
            .collect();

        // Check total combination count to avoid exponential blowup.
        let total_combos: usize = equiv_classes
            .iter()
            .map(Vec::len)
            .try_fold(1usize, usize::checked_mul)
            .unwrap_or(usize::MAX);
        if total_combos > MAX_EQUIV_COMBINATIONS {
            return None;
        }

        // Unary case (most common for map[f] with single array argument).
        if arg_selects.len() == 1 {
            for &equiv_term in &equiv_classes[0] {
                if let Some(found) = self
                    .terms
                    .find_app(&Symbol::named(func_name), &[equiv_term])
                {
                    if equiv_term == arg_selects[0] {
                        // Direct match — no extra reasons needed (already
                        // handled by the caller's exact find_app check).
                        continue;
                    }
                    let reasons = self
                        .explain_equal_if_provable(arg_selects[0], equiv_term)
                        .unwrap_or_default();
                    return Some((found, reasons));
                }
            }
            return None;
        }

        // General multi-arg case: enumerate cartesian product.
        let mut indices = vec![0usize; arg_selects.len()];
        let mut checked = 0usize;
        loop {
            if checked >= MAX_EQUIV_COMBINATIONS {
                break;
            }
            checked += 1;

            // Build the current combination.
            let combo: Vec<TermId> = indices
                .iter()
                .enumerate()
                .map(|(dim, &idx)| equiv_classes[dim][idx])
                .collect();

            // Skip the all-original combination (already tried by caller).
            let all_original = combo.iter().zip(arg_selects.iter()).all(|(&a, &b)| a == b);
            if !all_original {
                if let Some(found) = self.terms.find_app(&Symbol::named(func_name), &combo) {
                    let mut reasons = Vec::new();
                    for (dim, (&orig, &equiv_term)) in
                        arg_selects.iter().zip(combo.iter()).enumerate()
                    {
                        if orig != equiv_term {
                            if let Some(eq_reasons) =
                                self.explain_equal_if_provable(orig, equiv_term)
                            {
                                reasons.extend(eq_reasons);
                            }
                        }
                        let _ = dim; // used in future extensions
                    }
                    return Some((found, reasons));
                }
            }

            // Advance to next combination (odometer-style).
            let mut carry = true;
            for dim in (0..indices.len()).rev() {
                if carry {
                    indices[dim] += 1;
                    if indices[dim] < equiv_classes[dim].len() {
                        carry = false;
                    } else {
                        indices[dim] = 0;
                    }
                }
            }
            if carry {
                break; // All combinations exhausted.
            }
        }

        None
    }
}
