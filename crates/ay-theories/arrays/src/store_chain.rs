// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Store chain navigation and resolution for the array theory solver.
//!
//! Implements store chain walking for ROW1/ROW2 reasoning:
//! - Following stores through equality chains
//! - Resolving selects through store chains
//! - Collecting effective store maps for extensionality

use super::*;

#[derive(Clone, Copy)]
enum SentinelEdgeMode {
    RequireReasons,
    Skip,
}

struct StoreThroughEq {
    base: TermId,
    index: TermId,
    value: TermId,
    eq_terms: Vec<TermId>,
    reasons: Vec<TheoryLit>,
}

pub(crate) type StoreChainEntry = (TermId, TermId, Vec<TheoryLit>);
pub(crate) type StoreChainEntries = Vec<StoreChainEntry>;
pub(crate) type StoreChainCollection = (TermId, Vec<TheoryLit>, StoreChainEntries);

impl ArraySolver<'_> {
    /// Speculative interface equalities are SAT guesses, not structural array facts.
    ///
    /// #8785: If array store-chain navigation walks through an equality edge that
    /// exists only because `check_interface_equalities()` asked SAT to branch on
    /// `(= a b)`, the array theory can use its own guess as evidence that one
    /// chain is another chain's base. That creates circular store reasoning on
    /// direct disequality formulas. Keep those edges out of structural walkers.
    fn is_speculative_interface_edge(&self, lhs: TermId, rhs: TermId, eq_term: TermId) -> bool {
        !eq_term.is_sentinel()
            && matches!(self.terms.sort(lhs), Sort::Array(_))
            && matches!(self.terms.sort(rhs), Sort::Array(_))
            && self
                .requested_interface_eqs
                .contains(&Self::ordered_pair(lhs, rhs))
    }

    pub(crate) fn canonicalize_theory_lits(reasons: &mut Vec<TheoryLit>) {
        reasons.sort_by_key(|lit| (lit.term.0, lit.value));
        reasons.dedup_by_key(|lit| (lit.term, lit.value));
    }

    fn extend_eq_path(
        &self,
        current: TermId,
        other: TermId,
        eq_term: TermId,
        eq_terms: &[TermId],
        reasons: &[TheoryLit],
        sentinel_edges: SentinelEdgeMode,
    ) -> Option<(Vec<TermId>, Vec<TheoryLit>)> {
        if self.is_speculative_interface_edge(current, other, eq_term) {
            return None;
        }

        let mut next_eq_terms = eq_terms.to_vec();
        let mut next_reasons = reasons.to_vec();
        if eq_term.is_sentinel() {
            match sentinel_edges {
                SentinelEdgeMode::RequireReasons => {
                    let key = Self::ordered_pair(current, other);
                    let edge_reasons = self.external_eq_reasons.get(&key)?;
                    if edge_reasons.is_empty() {
                        return None;
                    }
                    next_reasons.extend(edge_reasons.iter().copied());
                }
                SentinelEdgeMode::Skip => return None,
            }
        } else {
            next_eq_terms.push(eq_term);
            next_reasons.push(TheoryLit::new(eq_term, true));
        }
        Some((next_eq_terms, next_reasons))
    }

    /// Follow a term through equalities to find a store term.
    ///
    /// Performs BFS through the equality adjacency list up to a bounded depth,
    /// handling transitive equality chains like c = b = store(a, i, v) (#4304).
    pub(super) fn find_store_through_eq(
        &self,
        term: TermId,
    ) -> Option<(TermId, TermId, TermId, Vec<TermId>)> {
        self.find_store_through_eq_with_mode(term, SentinelEdgeMode::RequireReasons)
            .map(|found| (found.base, found.index, found.value, found.eq_terms))
    }

    fn find_store_through_eq_with_reasons(&self, term: TermId) -> Option<StoreThroughEq> {
        self.find_store_through_eq_with_mode(term, SentinelEdgeMode::RequireReasons)
    }

    fn find_store_through_asserted_eq(&self, term: TermId) -> Option<StoreThroughEq> {
        self.find_store_through_eq_with_mode(term, SentinelEdgeMode::Skip)
    }

    fn find_store_through_eq_with_mode(
        &self,
        term: TermId,
        sentinel_edges: SentinelEdgeMode,
    ) -> Option<StoreThroughEq> {
        // First check if term is directly a store
        if let Some(&(base, idx, val)) = self.store_cache.get(&term) {
            return Some(StoreThroughEq {
                base,
                index: idx,
                value: val,
                eq_terms: vec![],
                reasons: vec![],
            });
        }

        // #7956: window-scoped memo. Inside a frozen-graph `eq_paths_cache`
        // window this walk is a deterministic pure function of immutable state
        // (`store_cache`, `eq_adj`, `external_eq_reasons`,
        // `requested_interface_eqs`, term sorts), so a hit is byte-identical
        // to a recomputation. Store-chain drivers
        // (`store_chain_reaches_asserted`, `collect_complete_effective_stores*`)
        // re-walk the same chains once per candidate pair; the memo makes each
        // re-walk O(chain) hash hits instead of O(chain × class) reason-cloning
        // BFS. Outside a window every call recomputes, exactly as before.
        let skip_sentinels = matches!(sentinel_edges, SentinelEdgeMode::Skip);
        if let Some(hit) = eq_paths_cache::get_store_through(term, skip_sentinels) {
            return hit.map(|payload| StoreThroughEq {
                base: payload.0,
                index: payload.1,
                value: payload.2,
                eq_terms: payload.3.clone(),
                reasons: payload.4.clone(),
            });
        }
        let found = self.find_store_through_eq_with_mode_uncached(term, sentinel_edges);
        eq_paths_cache::put_store_through(
            term,
            skip_sentinels,
            &found.as_ref().map(|f| {
                Rc::new((
                    f.base,
                    f.index,
                    f.value,
                    f.eq_terms.clone(),
                    f.reasons.clone(),
                ))
            }),
        );
        found
    }

    fn find_store_through_eq_with_mode_uncached(
        &self,
        term: TermId,
        sentinel_edges: SentinelEdgeMode,
    ) -> Option<StoreThroughEq> {
        // Prefer a direct store-definition edge over learned/transitive aliases.
        // Store-commutativity instances can accumulate many later array aliases;
        // taking one of those first makes proof guards change from round to
        // round even when a stable asserted `(= a (store ...))` edge exists.
        if let Some(neighbors) = self.eq_adj.get(&term) {
            let mut direct_store_edges = Vec::new();
            for &(other, eq_term) in neighbors {
                let Some(&(base, idx, val)) = self.store_cache.get(&other) else {
                    continue;
                };
                let Some((path_eq_terms, mut path_reasons)) =
                    self.extend_eq_path(term, other, eq_term, &[], &[], sentinel_edges)
                else {
                    continue;
                };
                Self::canonicalize_theory_lits(&mut path_reasons);
                direct_store_edges.push(StoreThroughEq {
                    base,
                    index: idx,
                    value: val,
                    eq_terms: path_eq_terms,
                    reasons: path_reasons,
                });
            }
            direct_store_edges.sort_by_key(|edge| {
                (
                    edge.reasons.len(),
                    edge.eq_terms.first().map(|term| term.0).unwrap_or(u32::MAX),
                    edge.base.0,
                    edge.index.0,
                    edge.value.0,
                )
            });
            if let Some(edge) = direct_store_edges.into_iter().next() {
                // M1 weak-equivalence invariant: the walk traversed a subset
                // of the weak-equivalence graph's edges, so its endpoints must
                // be weakly connected.
                #[cfg(debug_assertions)]
                self.debug_assert_walk_endpoints_weakly_connected(term, edge.base);
                return Some(edge);
            }
        }

        // M2 union-find prefilter: the BFS below only visits members of
        // `term`'s equivalence class, so if the class holds no store term the
        // walk is a guaranteed miss — answer O(class) without per-node reason
        // cloning. (This negative case is the common one: every store-chain
        // walk terminates with one final miss per base array.) Positive hits
        // keep the exact legacy BFS so path preference, depth bounds, and
        // proof shapes stay byte-identical.
        if self.shadow_uf_ready() {
            {
                let members = self.shadow_uf.class_slice(term)?;
                if !members
                    .iter()
                    .any(|member| self.store_cache.contains_key(member))
                {
                    return None;
                }
            }
        }

        // BFS through equality adjacency list to find a store term
        const MAX_DEPTH: usize = 10;
        let mut queue: Vec<(TermId, Vec<TermId>, Vec<TheoryLit>, usize)> =
            vec![(term, vec![], vec![], 0)];
        let mut visited = HashSet::default();
        visited.insert(term);

        while let Some((current, eq_terms, reasons, depth)) = queue.pop() {
            if depth >= MAX_DEPTH {
                continue;
            }
            if let Some(neighbors) = self.eq_adj.get(&current) {
                for &(other, eq_term) in neighbors {
                    let Some((path_eq_terms, mut path_reasons)) = self.extend_eq_path(
                        current,
                        other,
                        eq_term,
                        &eq_terms,
                        &reasons,
                        sentinel_edges,
                    ) else {
                        continue;
                    };
                    if !visited.insert(other) {
                        continue;
                    }
                    if let Some(&(base, idx, val)) = self.store_cache.get(&other) {
                        Self::canonicalize_theory_lits(&mut path_reasons);
                        // M1 weak-equivalence invariant (see direct-edge case).
                        #[cfg(debug_assertions)]
                        self.debug_assert_walk_endpoints_weakly_connected(term, base);
                        return Some(StoreThroughEq {
                            base,
                            index: idx,
                            value: val,
                            eq_terms: path_eq_terms,
                            reasons: path_reasons,
                        });
                    }
                    queue.push((other, path_eq_terms, path_reasons, depth + 1));
                }
            }
        }
        None
    }

    /// Follow a term through equalities to find a const-array representative.
    ///
    /// Returns the const default term and SAT-visible equality reasons used to reach it.
    pub(crate) fn find_const_array_through_eq(
        &self,
        term: TermId,
    ) -> Option<(TermId, Vec<TheoryLit>)> {
        if let Some(&default) = self.const_array_cache.get(&term) {
            return Some((default, vec![]));
        }

        // M2 union-find prefilter (see find_store_through_eq_with_mode): no
        // const-array in the class means the BFS below cannot succeed.
        if self.shadow_uf_ready() {
            match self.shadow_uf.class_slice(term) {
                Some(members)
                    if members
                        .iter()
                        .any(|member| self.const_array_cache.contains_key(member)) => {}
                _ => return None,
            }
        }

        const MAX_DEPTH: usize = 10;
        let mut queue: Vec<(TermId, Vec<TermId>, Vec<TheoryLit>, usize)> =
            vec![(term, vec![], vec![], 0)];
        let mut visited = HashSet::default();
        visited.insert(term);

        while let Some((current, eq_terms, reasons, depth)) = queue.pop() {
            if depth >= MAX_DEPTH {
                continue;
            }
            if let Some(neighbors) = self.eq_adj.get(&current) {
                for &(other, eq_term) in neighbors {
                    let Some((path_eq_terms, mut path_reasons)) = self.extend_eq_path(
                        current,
                        other,
                        eq_term,
                        &eq_terms,
                        &reasons,
                        SentinelEdgeMode::RequireReasons,
                    ) else {
                        continue;
                    };
                    if !visited.insert(other) {
                        continue;
                    }
                    if let Some(&default) = self.const_array_cache.get(&other) {
                        Self::canonicalize_theory_lits(&mut path_reasons);
                        return Some((default, path_reasons));
                    }
                    queue.push((other, path_eq_terms, path_reasons, depth + 1));
                }
            }
        }

        None
    }

    /// Recursively simplify nested selects through stores.
    ///
    /// For select(select(select(Heap_post, 0), obj), f2):
    /// 1. Simplify select(Heap_post, 0) using ROW1 → gets middle value
    /// 2. If middle value is a store, continue simplifying
    /// 3. Eventually reaches a value or base array
    ///
    /// Returns (normalized_base_array, normalized_index, eq_reasons_used, diseq_reasons)
    /// The normalized form is a (base_array, index) pair that can be compared for equality.
    /// `diseq_reasons` contains disequality explanations from store chain ROW2 skipping (#5086).
    pub(crate) fn normalize_select(
        &self,
        select_term: TermId,
    ) -> (Option<(TermId, TermId)>, Vec<TheoryLit>, Vec<TheoryLit>) {
        let Some(&(array, index)) = self.select_cache.get(&select_term) else {
            return (None, vec![], vec![]);
        };

        // Track SAT-visible equality reasons used during normalization.
        let mut eq_reasons = Vec::new();
        let mut diseq_reasons = Vec::new();

        // First, get the effective array (follow through nested selects and stores)
        let effective_array = self.get_effective_array(array, &mut eq_reasons);

        // Now walk through stores at the effective array level
        let base =
            self.follow_stores_to_base(effective_array, index, &mut eq_reasons, &mut diseq_reasons);

        (Some((base, index)), eq_reasons, diseq_reasons)
    }

    /// Get the effective array by following nested selects.
    /// If array is select(A, i) and A=store(B, i, V), return V.
    fn get_effective_array(&self, array: TermId, eq_reasons: &mut Vec<TheoryLit>) -> TermId {
        // If array is a select term, try to simplify it
        if let Some(&(inner_array, inner_index)) = self.select_cache.get(&array) {
            // Recursively get the effective inner array
            let effective_inner = self.get_effective_array(inner_array, eq_reasons);

            // Try to apply ROW1: if effective_inner is a store at inner_index
            if let Some(found) = self.find_store_through_eq_with_reasons(effective_inner) {
                if let Some(index_eq_reasons) =
                    self.explain_equal_if_provable(inner_index, found.index)
                {
                    // ROW1: select(store(a, i, v), i) = v
                    eq_reasons.extend(found.reasons);
                    eq_reasons.extend(index_eq_reasons);
                    // v might itself be a store, so return it for further processing
                    return found.value;
                }
            }

            // Can't simplify further at this level
            return array;
        }

        // Not a select, return as-is
        array
    }

    /// Follow stores via ROW2 to find the base array.
    ///
    /// Uses `explain_distinct_if_provable` to ensure only provable index
    /// disequalities are used. Collects disequality reasons alongside
    /// equality terms so callers can build complete conflict clauses (#5086).
    fn follow_stores_to_base(
        &self,
        array: TermId,
        index: TermId,
        eq_reasons: &mut Vec<TheoryLit>,
        diseq_reasons: &mut Vec<TheoryLit>,
    ) -> TermId {
        let mut current = array;
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 20;

        loop {
            iterations += 1;
            if iterations > MAX_ITERATIONS {
                break;
            }

            if let Some(found) = self.find_store_through_eq_with_reasons(current) {
                // Only skip stores where the disequality is provable (#5086).
                if let Some(reasons) = self.explain_distinct_if_provable(index, found.index) {
                    eq_reasons.extend(found.reasons);
                    diseq_reasons.extend(reasons);
                    current = found.base;
                    continue;
                }
                // Can't skip - index might match or disequality not provable
                break;
            }

            // Not a store
            break;
        }

        current
    }

    /// Resolve select(array, index) through a chain of stores using ROW1+ROW2.
    ///
    /// Walks the store chain from `array`:
    /// - ROW2: if store index is known-distinct from `index`, skip to base
    /// - ROW1: if store index is known-equal to `index`, return the stored value
    ///
    /// Returns `Some((value, reasons))` if ROW1/ROW2 resolves the select to a
    /// concrete value, or `None` if the chain cannot be fully resolved.
    pub(crate) fn resolve_select_through_stores(
        &self,
        array: TermId,
        index: TermId,
    ) -> Option<(TermId, Vec<TheoryLit>)> {
        let mut current = array;
        let mut reasons = Vec::new();
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 200;

        loop {
            iterations += 1;
            if iterations > MAX_ITERATIONS {
                return None;
            }

            if let Some(found) = self.find_store_through_eq_with_reasons(current) {
                reasons.extend(found.reasons);
                if let Some(index_eq_reasons) = self.explain_equal_if_provable(index, found.index) {
                    // ROW1: select(store(a, i, v), i) = v
                    reasons.extend(index_eq_reasons);
                    reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                    reasons.dedup_by_key(|lit| (lit.term, lit.value));
                    return Some((found.value, reasons));
                }
                if let Some(diseq_reasons) = self.explain_distinct_if_provable(index, found.index) {
                    // ROW2: skip to base array when the disequality is
                    // provable and explainable with SAT-level reasons.
                    reasons.extend(diseq_reasons);
                    current = found.base;
                    continue;
                }
                // Index relationship unknown — can't resolve further
                return None;
            }

            if let Some((default_value, const_reasons)) = self.find_const_array_through_eq(current)
            {
                reasons.extend(const_reasons);
                reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                reasons.dedup_by_key(|lit| (lit.term, lit.value));
                return Some((default_value, reasons));
            }

            // Not a store term — can't resolve further
            return None;
        }
    }

    /// Store chain resolution for equality propagation with explicit reasons.
    ///
    /// Like `resolve_select_through_stores`, but returns the SAT-visible
    /// equality/disequality antecedents used while walking the store chain.
    /// Unlike the older relaxed propagation path, this rejects sentinel-only
    /// (external/model-based) equalities and only skips stores when the index
    /// relationship is provable with a real explanation.
    ///
    /// Returns the resolved base array after walking through all explainable
    /// stores. If ROW1 matches (index equals store index), returns
    /// `ResolvedValue`. Otherwise returns `ResolvedBase` with the ultimate base
    /// array that couldn't be resolved further.
    pub(crate) fn resolve_select_base_for_propagation_with_reasons(
        &self,
        array: TermId,
        index: TermId,
    ) -> (SelectResolution, Vec<TheoryLit>) {
        let mut current = array;
        let mut reasons = Vec::new();
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 200;

        loop {
            iterations += 1;
            if iterations > MAX_ITERATIONS {
                return (SelectResolution::Unresolved, reasons);
            }

            if let Some(found) = self.find_store_through_eq_with_reasons(current) {
                reasons.extend(found.reasons);
                if self.known_equal(index, found.index) {
                    // ROW1: select(store(a, i, v), i) = v
                    if let Some(eq_reasons) = self.explain_equal_if_provable(index, found.index) {
                        reasons.extend(eq_reasons);
                    } else {
                        return (SelectResolution::Unresolved, reasons);
                    }
                    reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                    reasons.dedup_by_key(|lit| (lit.term, lit.value));
                    return (SelectResolution::Value(found.value), reasons);
                }
                if let Some(diseq_reasons) = self.explain_distinct_if_provable(index, found.index) {
                    // ROW2: skip to base only when the disequality is
                    // provable with SAT-visible reasons. Sentinel-only
                    // model equalities/disequalities must not reach
                    // equality propagation (#5179, #6608).
                    reasons.extend(diseq_reasons);
                    current = found.base;
                    continue;
                }
                // Index relationship unknown — can't resolve further
                return (SelectResolution::Unresolved, reasons);
            }

            if let Some((default_value, const_reasons)) = self.find_const_array_through_eq(current)
            {
                reasons.extend(const_reasons);
                reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                reasons.dedup_by_key(|lit| (lit.term, lit.value));
                return (SelectResolution::Value(default_value), reasons);
            }

            // Reached a base array that is not a store — return it.
            reasons.sort_by_key(|lit| (lit.term.0, lit.value));
            reasons.dedup_by_key(|lit| (lit.term, lit.value));
            return (SelectResolution::Base(current), reasons);
        }
    }

    /// Collect the effective store map of a store chain (#5086).
    ///
    /// Walks a store chain top-down (outermost store first) and collects
    /// (index, value) pairs. Later stores (closer to the base) at the same
    /// index are shadowed by earlier ones (closer to the top).
    ///
    /// Returns `Some((base_array, base_reasons, effective_map))` where
    /// `effective_map` contains the first `(index, value, reasons)` tuple seen
    /// for each equivalence class of index terms. `base_reasons` contains the
    /// alias reasons used while reaching the final base. Entry reasons contain
    /// alias reasons plus the distinctness reasons that make that store
    /// effective. Returns `None` if the chain is too long or not a pure store
    /// chain.
    pub(crate) fn collect_effective_stores(&self, array: TermId) -> Option<StoreChainCollection> {
        let mut current = array;
        let mut path_reasons = Vec::new();
        let mut effective: StoreChainEntries = Vec::new();
        let mut seen_indices: Vec<TermId> = Vec::new();
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 200;

        loop {
            iterations += 1;
            if iterations > MAX_ITERATIONS {
                return None;
            }

            if let Some(&(base, store_idx, store_val)) = self.store_cache.get(&current) {
                // #7654: An inner store is only "effective" if its index is
                // PROVABLY DISTINCT from all outer store indices. If we merely
                // check `known_equal` (the old code), an inner store at index
                // `i` is included even when an outer store at index `j` might
                // equal `i` — the model can set i=j, making the outer store
                // overwrite the inner one. The effective map then claims the
                // inner value is visible, leading to false equality propagation
                // (e.g., store(store(a,i,v),j,x) = store(store(a,i,w),j,x)
                // falsely derives v=w).
                //
                // Fix: skip the inner store unless ALL outer indices are
                // provably distinct from it.
                if let Some(reasons) =
                    self.effective_store_reasons(&seen_indices, store_idx, &path_reasons)
                {
                    effective.push((store_idx, store_val, reasons));
                    seen_indices.push(store_idx);
                }
                current = base;
                continue;
            }

            // Also follow equalities to find store terms
            if let Some(found) = self.find_store_through_asserted_eq(current) {
                let mut store_reasons = path_reasons.clone();
                store_reasons.extend(found.reasons);
                Self::canonicalize_theory_lits(&mut store_reasons);

                // #7654: Same fix as above — require provable distinctness.
                if let Some(reasons) =
                    self.effective_store_reasons(&seen_indices, found.index, &store_reasons)
                {
                    effective.push((found.index, found.value, reasons));
                    seen_indices.push(found.index);
                }
                path_reasons = store_reasons;
                current = found.base;
                continue;
            }

            // Reached a non-store base — return it with the collected map
            Self::canonicalize_theory_lits(&mut path_reasons);
            return Some((current, path_reasons, effective));
        }
    }

    /// Collect a complete effective store map for equality/conflict proofs.
    ///
    /// Unlike `collect_effective_stores`, this rejects a chain when an inner
    /// write may or may not be shadowed by an outer write. That keeps callers
    /// from proving two store permutations equal from a partial map.
    pub(crate) fn collect_complete_effective_stores(
        &self,
        array: TermId,
    ) -> Option<StoreChainCollection> {
        self.collect_complete_effective_stores_with_mode(array, SentinelEdgeMode::RequireReasons)
    }

    /// Collect a complete effective store map using asserted equality edges only.
    pub(crate) fn collect_complete_effective_stores_asserted(
        &self,
        array: TermId,
    ) -> Option<StoreChainCollection> {
        self.collect_complete_effective_stores_with_mode(array, SentinelEdgeMode::Skip)
    }

    pub(crate) fn store_chain_reaches_asserted(&self, from: TermId, target: TermId) -> bool {
        let mut current = from;
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 200;

        while current != target {
            iterations += 1;
            if iterations > MAX_ITERATIONS {
                return false;
            }
            let Some(found) = self.find_store_through_eq_with_mode(current, SentinelEdgeMode::Skip)
            else {
                return false;
            };
            current = found.base;
        }

        true
    }

    fn collect_complete_effective_stores_with_mode(
        &self,
        array: TermId,
        sentinel_edges: SentinelEdgeMode,
    ) -> Option<StoreChainCollection> {
        let mut current = array;
        let mut path_reasons = Vec::new();
        let mut effective: StoreChainEntries = Vec::new();
        let mut seen_indices: Vec<TermId> = Vec::new();
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 200;

        loop {
            iterations += 1;
            if iterations > MAX_ITERATIONS {
                return None;
            }

            let Some(found) = self.find_store_through_eq_with_mode(current, sentinel_edges) else {
                Self::canonicalize_theory_lits(&mut path_reasons);
                return Some((current, path_reasons, effective));
            };

            let mut store_reasons = path_reasons.clone();
            store_reasons.extend(found.reasons);
            Self::canonicalize_theory_lits(&mut store_reasons);

            let mut shadow_reasons = None;
            for &seen_idx in &seen_indices {
                if let Some(eq_reasons) = self.explain_equal_if_provable(seen_idx, found.index) {
                    shadow_reasons = Some(eq_reasons);
                    break;
                }
            }

            if let Some(eq_reasons) = shadow_reasons {
                path_reasons = store_reasons;
                path_reasons.extend(eq_reasons);
                Self::canonicalize_theory_lits(&mut path_reasons);
                current = found.base;
                continue;
            }

            let mut entry_reasons = store_reasons.clone();
            for &seen_idx in &seen_indices {
                let distinct_reasons = self.explain_distinct_if_provable(seen_idx, found.index)?;
                entry_reasons.extend(distinct_reasons);
            }
            Self::canonicalize_theory_lits(&mut entry_reasons);

            effective.push((found.index, found.value, entry_reasons));
            seen_indices.push(found.index);
            path_reasons = store_reasons;
            current = found.base;
        }
    }

    fn effective_store_reasons(
        &self,
        seen_indices: &[TermId],
        store_idx: TermId,
        path_reasons: &[TheoryLit],
    ) -> Option<Vec<TheoryLit>> {
        let mut reasons = path_reasons.to_vec();
        for &seen_idx in seen_indices {
            if seen_idx == store_idx {
                return None;
            }
            let distinct_reasons = self.explain_distinct_if_provable(seen_idx, store_idx)?;
            reasons.extend(distinct_reasons);
        }
        Self::canonicalize_theory_lits(&mut reasons);
        Some(reasons)
    }

    /// Check if two effective store maps are identical up to equivalence classes.
    ///
    /// Two maps match if for every (index, value) in one map, there exists a
    /// corresponding (index', value') in the other where index ≡ index' and
    /// value ≡ value'. Both maps must have the same number of entries.
    pub(crate) fn effective_stores_match_with_reasons(
        &self,
        map1: &[(TermId, TermId, Vec<TheoryLit>)],
        map2: &[(TermId, TermId, Vec<TheoryLit>)],
    ) -> Option<Vec<TheoryLit>> {
        if map1.len() != map2.len() {
            return None;
        }

        // #6546: Greedy O(N^2) matcher replaces O(N!) backtracking matcher.
        let mut used = vec![false; map2.len()];
        let mut all_reasons = Vec::new();

        for (idx1, val1, store_reasons1) in map1 {
            let mut matched = false;
            for (candidate, (idx2, val2, store_reasons2)) in map2.iter().enumerate() {
                if used[candidate] {
                    continue;
                }

                let Some(idx_reasons) = self.explain_equal_if_provable(*idx1, *idx2) else {
                    continue;
                };
                let Some(val_reasons) = self.explain_equal_if_provable(*val1, *val2) else {
                    continue;
                };

                used[candidate] = true;
                all_reasons.extend(store_reasons1.iter().copied());
                all_reasons.extend(store_reasons2.iter().copied());
                all_reasons.extend(idx_reasons);
                all_reasons.extend(val_reasons);
                matched = true;
                break;
            }
            if !matched {
                return None;
            }
        }

        all_reasons.sort_by_key(|lit| (lit.term.0, lit.value));
        all_reasons.dedup_by_key(|lit| (lit.term, lit.value));
        Some(all_reasons)
    }

    /// #lemma-must-prune / #refine-theory-memory: is emitting `clause` a NO-OP
    /// that cannot move the refinement loop forward?
    ///
    /// Two ways a lemma is unproductive, and both cause the SAME livelock — the
    /// executor adds nothing, the SAT solver returns the same model, this check
    /// re-derives the same clause, forever:
    ///
    /// * ALREADY SATISFIED by the current assignment — it cannot exclude the
    ///   model it was derived for, so it prunes nothing. (Only a DEFINITELY-true
    ///   literal counts; an unassigned literal can still propagate.)
    /// * ALREADY APPLIED — the clause is in the SAT solver already, so the
    ///   executor's lemma dedup collapses it to nothing. The theory is rebuilt
    ///   every refinement round and so has no memory of its own emissions;
    ///   `note_applied_theory_lemma` is that memory, but until now only
    ///   `final_check` consulted it, and the `check_impl` axiom paths did not —
    ///   so they re-requested the same axioms every round (measured on the
    ///   AUFLIA ext_eq empty-next fixture: 879 lemmas, then the loop spins with
    ///   the lemma set frozen and no clause ever added).
    ///
    /// Skipping is sound on both counts: a satisfied clause has no pruning power
    /// to lose, and an applied clause is already enforced by the SAT solver. The
    /// caller falls through to its remaining checks, so a genuine conflict is
    /// still found and reported.
    pub(crate) fn lemma_is_unproductive(&self, clause: &[TheoryLit]) -> bool {
        clause
            .iter()
            .any(|lit| self.assigns.get(&lit.term) == Some(&lit.value))
            || self.applied_theory_lemmas.contains(clause)
    }

    pub(crate) fn conflict_reasons_to_lemma(
        &self,
        mut reasons: Vec<TheoryLit>,
    ) -> Option<TheoryResult> {
        if reasons.is_empty() {
            return None;
        }

        reasons.sort_by_key(|lit| (lit.term.0, lit.value));
        reasons.dedup_by_key(|lit| (lit.term, lit.value));

        let mut clause: Vec<TheoryLit> = reasons
            .into_iter()
            .map(|lit| TheoryLit::new(lit.term, !lit.value))
            .collect();
        clause.sort_by_key(|lit| (lit.term.0, lit.value));
        clause.dedup_by_key(|lit| (lit.term, lit.value));

        if clause.is_empty() {
            return None;
        }

        // #lemma-must-prune: a lemma emitted in RESPONSE to the current
        // assignment must be FALSIFIED by that assignment, or it cannot exclude
        // the model it was derived for.
        //
        // The reason set is built from this solver's own congruence closure,
        // which can prove an equality (e.g. that two store chains are
        // structurally equal) whose SAT atom the solver has assigned FALSE.
        // Negating such a reason yields a clause that is VALID but already
        // SATISFIED by the current model. Adding it prunes nothing: the SAT
        // solver returns the same model, this check re-derives the same
        // reasons, the executor dedups the clause to nothing, and the
        // refinement loop spins forever — the AUFLIA `ext_eq` hang (#7956),
        // measured at 3800+ rounds with the lemma set frozen at 5 and zero new
        // clauses added.
        //
        // Suppressing it is sound: a clause with an already-TRUE literal cannot
        // rule out the current assignment, so nothing is lost. The conflict is
        // not suppressed from the search either — the caller falls through to
        // its remaining checks, and if this model really is array-inconsistent
        // then a conflict whose reasons ARE all true under the assignment is
        // the one that must be reported.
        //
        // Only a DEFINITELY-true literal suppresses; an unassigned literal
        // leaves the clause able to propagate, so it is still emitted. This is
        // the same guard the ROW2-down path already applies in
        // `axiom_checkers`.
        if self.lemma_is_unproductive(&clause) {
            return None;
        }

        Some(TheoryResult::NeedLemmas(vec![TheoryLemma::new(clause)]))
    }
}
