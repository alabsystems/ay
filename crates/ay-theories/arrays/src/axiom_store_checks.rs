// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Store-related and structural axiom conflict checkers.
//!
//! Implements detection of:
//! - Store chain resolution
//! - Conflicting store equalities (extensionality)
//! - Disjunctive store-target equalities
//! - Nested select conflicts
//! - Const-array read axiom
//! - Self-store detection
//! - Array equality conflicts

use super::*;

type EqualityReasonCache = HashMap<(TermId, TermId), Option<Vec<TheoryLit>>>;
type EffectiveStoreMap = Vec<(TermId, TermId, Vec<TheoryLit>)>;
type EffectiveStoreChain = (TermId, Vec<TheoryLit>, EffectiveStoreMap);
type EffectiveStoreChainCache = HashMap<TermId, Option<EffectiveStoreChain>>;

#[derive(Clone, Copy, Eq, PartialEq)]
enum StoreChainSelectDifferenceWitnessMode {
    SingletonOnly,
    BroadFallback,
}

impl ArraySolver<'_> {
    fn explain_equal_cached(
        &self,
        cache: &mut EqualityReasonCache,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<Vec<TheoryLit>> {
        let key = Self::ordered_pair(lhs, rhs);
        if let Some(reasons) = cache.get(&key) {
            return reasons.clone();
        }

        let reasons = self.explain_equal_if_provable(lhs, rhs);
        cache.insert(key, reasons.clone());
        reasons
    }

    fn collect_complete_effective_stores_asserted_cached(
        &self,
        cache: &mut EffectiveStoreChainCache,
        array: TermId,
    ) -> Option<EffectiveStoreChain> {
        if let Some(chain) = cache.get(&array) {
            return chain.clone();
        }

        let chain = self.collect_complete_effective_stores_asserted(array);
        cache.insert(array, chain.clone());
        chain
    }

    /// Check for conflicts by resolving select terms through store chains (#4304).
    ///
    /// Event-driven (#6820 Step 4): drains `pending_store_chain` queue instead
    /// of scanning all selects. Candidates are queued in `register_select`,
    /// `register_store`, and `notify_equality` when a select is on a store chain.
    pub(crate) fn check_store_chain_resolution(&mut self) -> Option<TheoryResult> {
        let mut candidates = self.pending_store_chain.take();
        candidates.sort_unstable_by_key(|t| t.0);
        candidates.dedup();

        let mut retained = Vec::new();
        let mut iter = candidates.into_iter();
        while let Some(select_term) = iter.next() {
            let Some(&(array, index)) = self.select_cache.get(&select_term) else {
                continue;
            };
            if let Some((resolved_value, mut reasons)) =
                self.resolve_select_through_stores(array, index)
            {
                if let Some(val_diseq_reasons) =
                    self.explain_distinct_if_provable(select_term, resolved_value)
                {
                    reasons.extend(val_diseq_reasons);
                    reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                    reasons.dedup_by_key(|lit| (lit.term, lit.value));

                    if reasons.is_empty() {
                        retained.push(select_term);
                        continue;
                    }
                    retained.extend(iter);
                    self.pending_store_chain.replace(retained);
                    return self.conflict_reasons_to_lemma(reasons);
                }
            }
            // Retain selects whose chains couldn't be fully resolved —
            // they may resolve after more equalities/disequalities arrive.
            retained.push(select_term);
        }
        self.pending_store_chain.replace(retained);
        None
    }

    fn conflicting_store_pair_reasons(
        &self,
        first: (TermId, TermId, TermId, TermId),
        second: (TermId, TermId, TermId, TermId),
    ) -> Option<Vec<TheoryLit>> {
        let (s1, base1, idx1, val1) = first;
        let (s2, base2, idx2, val2) = second;
        let store_eq_reasons = self.explain_equal_if_provable(s1, s2)?;
        let base_eq_reasons = self.explain_equal_if_provable(base1, base2)?;
        let idx_eq_reasons = self.explain_equal_if_provable(idx1, idx2)?;

        let val_diseq_reasons = self.explain_distinct_if_provable(val1, val2)?;

        let mut reasons = Vec::new();
        reasons.extend(store_eq_reasons);
        reasons.extend(base_eq_reasons);
        reasons.extend(idx_eq_reasons);
        reasons.extend(val_diseq_reasons);
        if reasons.is_empty() {
            return None;
        }
        Some(reasons)
    }

    /// Check for conflicting store equalities (#4304).
    ///
    /// Event-driven (#6820 Step 4): drains `pending_conflicting_stores` queue
    /// instead of scanning all store equivalence classes. Candidates are queued
    /// when stores become equal via `notify_equality` or `register_store`.
    ///
    /// Falls back to full scan when the queue is empty but `assign_dirty` was
    /// recently cleared (indicating a new equality graph state).
    pub(crate) fn check_conflicting_store_equalities(&mut self) -> Option<TheoryResult> {
        let mut pairs = self.pending_conflicting_stores.take();
        pairs.sort_unstable_by_key(|&(a, b)| (a.0, b.0));
        pairs.dedup();

        let mut retained = Vec::new();
        for (s1, s2) in pairs {
            // Both must still be in cache (backtrack may have invalidated them).
            let Some(&(base1, idx1, val1)) = self.store_cache.get(&s1) else {
                continue;
            };
            let Some(&(base2, idx2, val2)) = self.store_cache.get(&s2) else {
                continue;
            };
            // Must be in the same equivalence class.
            if !self.known_equal(s1, s2) {
                continue;
            }
            if let Some(reasons) = self
                .conflicting_store_pair_reasons((s1, base1, idx1, val1), (s2, base2, idx2, val2))
            {
                let result = self.conflict_reasons_to_lemma(reasons);
                self.pending_conflicting_stores.replace(retained);
                return result;
            }
            // Retain for future re-checks as more equalities arrive.
            retained.push((s1, s2));
        }
        self.pending_conflicting_stores.replace(retained);
        None
    }

    /// Check direct `store(base, idx, val) = target` equalities for the
    /// disjunctive consequence `idx1 = idx2 ∨ base = target` (#5086, #6885).
    pub(crate) fn check_disjunctive_store_target_equalities(&mut self) -> Option<TheoryResult> {
        let mut grouped: HashMap<(TermId, TermId), Vec<(TermId, TermId)>> = HashMap::default();
        let mut eq_entries: Vec<_> = self.equality_cache.iter().collect();
        eq_entries.sort_by_key(|(&eq_term, _)| eq_term.0);

        for (&eq_term, &(lhs, rhs)) in &eq_entries {
            if self.assigns.get(&eq_term) != Some(&true) {
                continue;
            }
            let direct_store_eq = if let Some(&(base, idx, _val)) = self.store_cache.get(&lhs) {
                Some((base, idx, rhs))
            } else if let Some(&(base, idx, _val)) = self.store_cache.get(&rhs) {
                Some((base, idx, lhs))
            } else {
                None
            };
            let Some((base, idx, target)) = direct_store_eq else {
                continue;
            };
            grouped
                .entry((base, target))
                .or_default()
                .push((eq_term, idx));
        }

        let mut groups: Vec<_> = grouped.into_iter().collect();
        groups.sort_by_key(|&((base, target), _)| (base.0, target.0));

        for ((base, target), mut store_eqs) in groups {
            if self.known_equal(base, target) {
                continue;
            }
            store_eqs.sort_by_key(|&(eq_term, idx)| (eq_term.0, idx.0));

            for (i, &(eq_i, idx_i)) in store_eqs.iter().enumerate() {
                for &(eq_j, idx_j) in store_eqs.iter().skip(i + 1) {
                    if idx_i == idx_j || self.known_equal(idx_i, idx_j) {
                        continue;
                    }

                    let idx_eq = self.get_eq_term(idx_i, idx_j);
                    let base_eq = self.get_eq_term(base, target);

                    if let (Some(idx_eq), Some(base_eq)) = (idx_eq, base_eq) {
                        let idx_sat = self.assigns.get(&idx_eq) == Some(&true);
                        let base_sat = self.assigns.get(&base_eq) == Some(&true);
                        if idx_sat || base_sat {
                            continue;
                        }

                        let mut clause = vec![
                            TheoryLit::new(eq_i, false),
                            TheoryLit::new(eq_j, false),
                            TheoryLit::new(idx_eq, true),
                            TheoryLit::new(base_eq, true),
                        ];
                        clause.sort_by_key(|lit| (lit.term.0, lit.value));
                        clause.dedup_by_key(|lit| (lit.term, lit.value));
                        let lemmas = vec![TheoryLemma::new(clause)];
                        return Some(TheoryResult::NeedLemmas(lemmas));
                    }

                    let mut requests = Vec::new();
                    for (lhs, rhs) in [(idx_i, idx_j), (base, target)] {
                        // #8596: Skip Array-sorted model equality requests.
                        // Array equality is handled by extensionality axioms,
                        // not by Nelson-Oppen model equality speculation.
                        // Requesting array-level model equalities over-constrains
                        // the SAT problem and causes false UNSAT.
                        if matches!(self.terms.sort(lhs), Sort::Array(_)) {
                            continue;
                        }
                        if self.known_equal(lhs, rhs) || self.get_eq_term(lhs, rhs).is_some() {
                            continue;
                        }
                        let key = Self::ordered_pair(lhs, rhs);
                        if self.requested_model_eqs.insert(key) {
                            requests.push(ModelEqualityRequest {
                                lhs,
                                rhs,
                                reason: vec![
                                    TheoryLit::new(eq_i, true),
                                    TheoryLit::new(eq_j, true),
                                ],
                                implied: false,
                            });
                        }
                    }

                    match requests.len() {
                        0 => {}
                        1 => {
                            return Some(TheoryResult::NeedModelEquality(
                                requests.pop().expect("invariant: len checked above"),
                            ));
                        }
                        _ => return Some(TheoryResult::NeedModelEqualities(requests)),
                    }
                }
            }
        }

        None
    }

    /// Check conflicts via nested select simplification.
    pub(crate) fn check_nested_select_conflicts(&self) -> Option<TheoryResult> {
        struct NormalizedSelectState {
            select_term: TermId,
            normalized: Option<(TermId, TermId)>,
            eq_reasons: Vec<TheoryLit>,
            diseq_reasons: Vec<TheoryLit>,
        }

        let candidate_pairs = self.select_conflict_candidate_pairs();

        #[cfg(not(kani))]
        let mut needed: HashSet<TermId> =
            ay_core::kani_compat::det_hash_set_with_capacity(candidate_pairs.len() * 2);
        #[cfg(kani)]
        let mut needed: HashSet<TermId> = HashSet::default();
        for &(s1, s2) in candidate_pairs.iter() {
            needed.insert(s1);
            needed.insert(s2);
        }
        let select_terms: HashMap<_, _> = needed
            .iter()
            .copied()
            .map(|select_term| {
                let (normalized, eq_reasons, diseq_reasons) = self.normalize_select(select_term);
                (
                    select_term,
                    NormalizedSelectState {
                        select_term,
                        normalized,
                        eq_reasons,
                        diseq_reasons,
                    },
                )
            })
            .collect();

        for (pair_idx, &(sel1_term, sel2_term)) in candidate_pairs.iter().enumerate() {
            // #array-deadline-forward: same O(pairs x explain-BFS) shape as
            // `row2_extended_conflict_lemmas` — amortized interrupt/deadline
            // poll so one dense final_check cannot overshoot the caller's
            // wall budget. FAIL-CLOSED: `None` here means "no conflict found
            // this round"; the final_check boundary poll maps the stop to
            // Unknown.
            if pair_idx % 32 == 0 && self.interrupted_or_deadline() {
                return None;
            }
            let Some(sel1) = select_terms.get(&sel1_term) else {
                continue;
            };
            let Some(sel2) = select_terms.get(&sel2_term) else {
                continue;
            };

            if let (Some((base1, idx1)), Some((base2, idx2))) = (sel1.normalized, sel2.normalized) {
                let same_base_reasons = self.explain_equal_if_provable(base1, base2);
                let same_index_reasons = self.explain_equal_if_provable(idx1, idx2);
                let same_base = same_base_reasons.is_some();
                let same_index = same_index_reasons.is_some();

                if same_base && same_index {
                    let Some(sel_diseq_reasons) =
                        self.explain_distinct_if_provable(sel1.select_term, sel2.select_term)
                    else {
                        continue;
                    };

                    let mut reasons = sel_diseq_reasons;

                    reasons.extend(sel1.diseq_reasons.iter().copied());
                    reasons.extend(sel2.diseq_reasons.iter().copied());

                    reasons.extend(sel1.eq_reasons.iter().copied());
                    reasons.extend(sel2.eq_reasons.iter().copied());

                    if let Some(base_eq_reasons) = same_base_reasons {
                        reasons.extend(base_eq_reasons);
                    }

                    if let Some(idx_eq_reasons) = same_index_reasons {
                        reasons.extend(idx_eq_reasons);
                    }

                    return self.conflict_reasons_to_lemma(reasons);
                }
            }
        }
        None
    }

    /// Check exact-select conflicts over equal finite store permutations.
    ///
    /// Storecomm benchmarks often assert
    /// `select(store(...), k) != select(store(...), k)` where both arrays are
    /// finite store towers over the same base with the same effective writes in
    /// different orders. Once the store maps match, the select values are equal
    /// for every `k`, so an exact select disequality is a conflict.
    pub(crate) fn check_store_permutation_select_conflicts(&self) -> Option<TheoryResult> {
        for (pair_idx, &(sel1_term, sel2_term)) in
            self.select_conflict_candidate_pairs().iter().enumerate()
        {
            // #array-deadline-forward: amortized interrupt/deadline poll (see
            // check_nested_select_conflicts above; fail-closed the same way).
            if pair_idx % 32 == 0 && self.interrupted_or_deadline() {
                return None;
            }
            let Some(&(array1, index1)) = self.select_cache.get(&sel1_term) else {
                continue;
            };
            let Some(&(array2, index2)) = self.select_cache.get(&sel2_term) else {
                continue;
            };

            let Some(mut index_eq_reasons) = self.explain_equal_if_provable(index1, index2) else {
                continue;
            };
            let Some(mut select_diseq_reasons) =
                self.explain_distinct_if_provable(sel1_term, sel2_term)
            else {
                continue;
            };

            let Some((base1, mut base1_reasons, map1)) =
                self.collect_complete_effective_stores(array1)
            else {
                continue;
            };
            let Some((base2, mut base2_reasons, map2)) =
                self.collect_complete_effective_stores(array2)
            else {
                continue;
            };
            if map1.is_empty() && map2.is_empty() {
                continue;
            }

            let Some(mut base_eq_reasons) = self.explain_equal_if_provable(base1, base2) else {
                continue;
            };
            let Some(mut map_reasons) = self.effective_stores_match_with_reasons(&map1, &map2)
            else {
                continue;
            };

            let mut reasons = Vec::new();
            reasons.append(&mut select_diseq_reasons);
            reasons.append(&mut index_eq_reasons);
            reasons.append(&mut base1_reasons);
            reasons.append(&mut base2_reasons);
            reasons.append(&mut base_eq_reasons);
            reasons.append(&mut map_reasons);

            reasons.sort_by_key(|lit| (lit.term.0, lit.value));
            reasons.dedup_by_key(|lit| (lit.term, lit.value));
            return Some(TheoryResult::Unsat(reasons));
        }

        None
    }

    fn store_chain_difference_support(
        &self,
        map1: &[(TermId, TermId, Vec<TheoryLit>)],
        map2: &[(TermId, TermId, Vec<TheoryLit>)],
        eq_cache: &mut EqualityReasonCache,
    ) -> (Vec<TermId>, Vec<TheoryLit>) {
        let mut used = vec![false; map2.len()];
        let mut support = Vec::new();
        let mut reasons = Vec::new();

        for (idx1, val1, store_reasons1) in map1 {
            type StoreMatchScore = (usize, usize, u32, u32, usize);
            type StoreMatch = (
                StoreMatchScore,
                usize,
                TermId,
                Vec<TheoryLit>,
                Vec<TheoryLit>,
            );
            let mut matched: Option<StoreMatch> = None;
            for (candidate, (idx2, val2, store_reasons2)) in map2.iter().enumerate() {
                if used[candidate] {
                    continue;
                }
                let Some(idx_reasons) = self.explain_equal_cached(eq_cache, *idx1, *idx2) else {
                    continue;
                };
                let score = (
                    idx_reasons.len(),
                    store_reasons2.len(),
                    idx2.0,
                    val2.0,
                    candidate,
                );
                match &matched {
                    Some((best_score, ..)) if *best_score <= score => {}
                    _ => {
                        matched =
                            Some((score, candidate, *val2, idx_reasons, store_reasons2.clone()));
                    }
                }
            }

            let Some((_score, candidate, val2, idx_reasons, store_reasons2)) = matched else {
                support.push(*idx1);
                reasons.extend(store_reasons1.iter().copied());
                continue;
            };
            used[candidate] = true;

            reasons.extend(store_reasons1.iter().copied());
            reasons.extend(store_reasons2.iter().copied());
            reasons.extend(idx_reasons);

            if let Some(val_reasons) = self.explain_equal_cached(eq_cache, *val1, val2) {
                reasons.extend(val_reasons);
            } else {
                support.push(*idx1);
            }
        }

        for (used, (idx2, _val2, store_reasons2)) in used.into_iter().zip(map2.iter()) {
            if used {
                continue;
            }
            support.push(*idx2);
            reasons.extend(store_reasons2.iter().copied());
        }

        support.sort_unstable_by_key(|term| term.0);
        support.dedup();
        reasons.sort_by_key(|lit| (lit.term.0, lit.value));
        reasons.dedup_by_key(|lit| (lit.term, lit.value));
        (support, reasons)
    }

    fn direct_alias_diseq_reasons(&self, lhs: TermId, rhs: TermId) -> Option<Vec<TheoryLit>> {
        if lhs == rhs {
            return None;
        }

        if let Some(eq_term) = self.get_eq_term(lhs, rhs) {
            if self.assigns.get(&eq_term) == Some(&false) {
                return Some(vec![TheoryLit::new(eq_term, false)]);
            }
        }

        let lhs_is_const = matches!(self.terms.get(lhs), TermData::Const(_));
        let rhs_is_const = matches!(self.terms.get(rhs), TermData::Const(_));
        if lhs_is_const && rhs_is_const && self.terms.get(lhs) != self.terms.get(rhs) {
            return Some(Vec::new());
        }

        let key = Self::ordered_pair(lhs, rhs);
        self.external_diseq_reasons.get(&key).cloned()
    }

    fn explain_distinct_select_aliases(
        &self,
        eq_cache: &mut EqualityReasonCache,
        lhs_select: TermId,
        rhs_select: TermId,
    ) -> Option<Vec<TheoryLit>> {
        if let Some(reasons) = self.explain_distinct_if_provable(lhs_select, rhs_select) {
            return Some(reasons);
        }

        const MAX_SELECT_ALIASES: usize = 64;
        let explanation_better = |candidate: &[TheoryLit], best: &[TheoryLit]| {
            candidate.len() < best.len()
                || (candidate.len() == best.len()
                    && candidate
                        .iter()
                        .map(|lit| (lit.term.0, lit.value))
                        .lt(best.iter().map(|lit| (lit.term.0, lit.value))))
        };

        let mut lhs_aliases = self.get_equiv_class(lhs_select);
        lhs_aliases.sort_unstable_by_key(|term| term.0);
        lhs_aliases.dedup();
        lhs_aliases.truncate(MAX_SELECT_ALIASES);

        let mut rhs_aliases = self.get_equiv_class(rhs_select);
        rhs_aliases.sort_unstable_by_key(|term| term.0);
        rhs_aliases.dedup();
        rhs_aliases.truncate(MAX_SELECT_ALIASES);

        let mut best: Option<Vec<TheoryLit>> = None;
        for lhs_alias in lhs_aliases {
            let Some(lhs_eq_reasons) = self.explain_equal_cached(eq_cache, lhs_select, lhs_alias)
            else {
                continue;
            };
            for &rhs_alias in &rhs_aliases {
                let Some(rhs_eq_reasons) =
                    self.explain_equal_cached(eq_cache, rhs_select, rhs_alias)
                else {
                    continue;
                };
                let Some(alias_diseq_reasons) =
                    self.direct_alias_diseq_reasons(lhs_alias, rhs_alias)
                else {
                    continue;
                };

                let mut reasons = Vec::new();
                reasons.extend(lhs_eq_reasons.iter().copied());
                reasons.extend(rhs_eq_reasons.iter().copied());
                reasons.extend(alias_diseq_reasons);
                reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                reasons.dedup_by_key(|lit| (lit.term, lit.value));
                match &best {
                    Some(best_reasons) if !explanation_better(&reasons, best_reasons) => {}
                    _ => best = Some(reasons),
                }
            }
        }

        best
    }

    fn select_alias_diseq_candidate_pairs(&self) -> Vec<(TermId, TermId)> {
        // #7956: window memo. Pure function of `diseq_set`, `select_cache`,
        // `eq_adj`, `assigns` and the shadow union-find — all frozen inside an
        // `eq_paths_cache` window — with sorted + deduped output, so a hit is
        // byte-identical to a recomputation.
        if let Some(hit) = eq_paths_cache::get_alias_diseq_pairs() {
            return hit.to_vec();
        }
        let pairs = self.select_alias_diseq_candidate_pairs_uncached();
        eq_paths_cache::put_alias_diseq_pairs(&Rc::from(pairs.as_slice()));
        pairs
    }

    fn select_alias_diseq_candidate_pairs_uncached(&self) -> Vec<(TermId, TermId)> {
        const MAX_SELECT_ALIASES_PER_ENDPOINT: usize = 16;

        // #arraytax: candidate endpoints can only be select terms (directly or
        // via `nearest_select_aliases`, which only collects `select_cache`
        // members). With no selects registered this loop provably yields no
        // pairs, yet it scanned the whole diseq_set with a per-endpoint
        // eq-graph BFS on array-free DT problems — skip it.
        if self.select_cache.is_empty() {
            return Vec::new();
        }

        let nearest_select_aliases = |endpoint: TermId| -> Vec<TermId> {
            // M2 union-find prefilter: the asserted-edge BFS below only ever
            // visits members of `endpoint`'s equivalence class, so a class
            // holding no select term is a guaranteed empty answer. Positive
            // candidates keep the exact legacy nearest-depth BFS (depth
            // minimality is load-bearing for candidate selection).
            if self.shadow_uf_ready() {
                match self.shadow_uf.class_slice(endpoint) {
                    Some(members)
                        if members
                            .iter()
                            .any(|member| self.select_cache.contains_key(member)) => {}
                    _ => return Vec::new(),
                }
            }

            let mut queue = std::collections::VecDeque::new();
            let mut seen = HashSet::default();
            queue.push_back((endpoint, 0usize));
            seen.insert(endpoint);

            let mut aliases = Vec::new();
            let mut found_depth = None;
            while let Some((current, depth)) = queue.pop_front() {
                if found_depth.is_some_and(|best_depth| depth > best_depth) {
                    break;
                }
                if self.select_cache.contains_key(&current) {
                    found_depth = Some(depth);
                    aliases.push(current);
                    if aliases.len() >= MAX_SELECT_ALIASES_PER_ENDPOINT {
                        break;
                    }
                    continue;
                }

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
                    queue.push_back((other, depth + 1));
                }
            }

            aliases.sort_unstable_by_key(|term| term.0);
            aliases.dedup();
            aliases
        };

        let mut pairs = Vec::new();
        for &(lhs, rhs) in &self.diseq_set {
            let lhs_selects = if self.select_cache.contains_key(&lhs) {
                vec![lhs]
            } else {
                nearest_select_aliases(lhs)
            };
            if lhs_selects.is_empty() {
                continue;
            }

            let rhs_selects = if self.select_cache.contains_key(&rhs) {
                vec![rhs]
            } else {
                nearest_select_aliases(rhs)
            };
            if rhs_selects.is_empty() {
                continue;
            }

            for lhs_select in lhs_selects {
                for &rhs_select in &rhs_selects {
                    if lhs_select != rhs_select {
                        pairs.push(Self::ordered_pair(lhs_select, rhs_select));
                    }
                }
            }
        }

        pairs.sort_unstable_by_key(|&(lhs, rhs)| (lhs.0, rhs.0));
        pairs.dedup();
        pairs
    }

    /// Propagate the singleton support equality for same-base finite store chains.
    ///
    /// If two reads over complete same-base store chains are currently disequal,
    /// and their effective maps differ at exactly one support index, then the
    /// read index must be that support. This keeps storecomm rows on the
    /// witness branch instead of proving the complement through broad ROW2 /
    /// permutation clauses.
    pub(crate) fn singleton_support_propagations(&self) -> Vec<TheoryPropagation> {
        // #7956: `&self` read-only scan — the eq_paths_cache window soundness
        // precondition holds trivially (no `&mut self` alias can exist), same
        // argument as `check_row2_extended`. See
        // `check_store_chain_select_difference_witness_with_mode` for the
        // memoized-function input inventory.
        let _eq_paths_cache_guard = eq_paths_cache::activate_if_inactive();

        let mut propagations = Vec::new();
        let mut seen = HashSet::default();
        let mut eq_cache = HashMap::default();
        let mut store_chain_cache = HashMap::default();
        for (sel1_term, sel2_term) in self.select_alias_diseq_candidate_pairs() {
            let Some(&(array1, index1)) = self.select_cache.get(&sel1_term) else {
                continue;
            };
            let Some(&(array2, index2)) = self.select_cache.get(&sel2_term) else {
                continue;
            };

            if self.store_chain_reaches_asserted(array1, array2)
                || self.store_chain_reaches_asserted(array2, array1)
            {
                continue;
            }

            let Some(index_eq_reasons) = self.explain_equal_cached(&mut eq_cache, index1, index2)
            else {
                continue;
            };
            let Some(select_diseq_reasons) =
                self.explain_distinct_select_aliases(&mut eq_cache, sel1_term, sel2_term)
            else {
                continue;
            };
            let Some((base1, base1_reasons, map1)) = self
                .collect_complete_effective_stores_asserted_cached(&mut store_chain_cache, array1)
            else {
                continue;
            };
            let Some((base2, base2_reasons, map2)) = self
                .collect_complete_effective_stores_asserted_cached(&mut store_chain_cache, array2)
            else {
                continue;
            };
            let Some(base_eq_reasons) = self.explain_equal_cached(&mut eq_cache, base1, base2)
            else {
                continue;
            };

            let (support, map_reasons) =
                self.store_chain_difference_support(&map1, &map2, &mut eq_cache);
            let [support_idx] = support.as_slice() else {
                continue;
            };
            // #qfax-vacuous-loop: the support index IS the read index (after
            // EUF canonicalization) — the equality is the constant true term,
            // which never appears in `assigns`, so without this guard the
            // same vacuous propagation re-emits every propagate call
            // (measured: 36k re-emissions/5s, 700k tautological learned
            // clauses, timeout on swap_invalid_t1_pp_sf_ai_00002_002).
            if *support_idx == index1 {
                continue;
            }
            let Some(eq_term) = self.terms.find_eq(index1, *support_idx) else {
                continue;
            };
            if self.assigns.get(&eq_term) == Some(&true) {
                continue;
            }
            if !seen.insert(eq_term) {
                continue;
            }

            let mut reason = Vec::new();
            reason.extend(select_diseq_reasons);
            reason.extend(index_eq_reasons);
            reason.extend(base1_reasons);
            reason.extend(base2_reasons);
            reason.extend(base_eq_reasons);
            reason.extend(map_reasons);
            reason.sort_by_key(|lit| (lit.term.0, lit.value));
            reason.dedup_by_key(|lit| (lit.term, lit.value));
            // Structural well-formedness (#qf-ax-swap-sf-false-sat): the
            // support-difference explanation can itself cite the propagated
            // atom. A NEGATED self-occurrence (`(= index1 support) = false`
            // inside the reason of `(= index1 support) = true`) is removable —
            // `(rest ∧ ¬L) → L` is the SAME clause as `rest → L` — while a
            // SAME-polarity occurrence makes the propagation vacuous (`L → L`)
            // and it must be dropped, not emitted with the self-literal
            // filtered (that would fabricate an unjustified `rest → L`).
            // Without this, `verify_theory_propagation` rejects the
            // propagation as circular (debug builds assert, #4666).
            let mut circular_same_value = false;
            reason.retain(|lit| {
                if lit.term != eq_term {
                    return true;
                }
                if lit.value {
                    circular_same_value = true;
                }
                false
            });
            if circular_same_value || reason.is_empty() {
                continue;
            }

            propagations.push(TheoryPropagation {
                literal: TheoryLit::new(eq_term, true),
                reason,
                reason_data: None,
            });
        }

        propagations
    }

    /// If two same-base finite store chains differ only on a finite support,
    /// a disequal read at witness index `k` implies `k` is in that support.
    pub(crate) fn check_store_chain_select_difference_witness(&mut self) -> Option<TheoryResult> {
        self.check_store_chain_select_difference_witness_with_mode(
            StoreChainSelectDifferenceWitnessMode::BroadFallback,
        )
    }

    /// Run only the narrow singleton-support part of
    /// `check_store_chain_select_difference_witness`.
    ///
    /// This gives exact ROW2/store-permutation checks a chance to learn smaller
    /// clauses before the broad finite-support fallback emits large disjunctions.
    pub(crate) fn check_store_chain_select_difference_witness_singleton(
        &mut self,
    ) -> Option<TheoryResult> {
        self.check_store_chain_select_difference_witness_with_mode(
            StoreChainSelectDifferenceWitnessMode::SingletonOnly,
        )
    }

    fn check_store_chain_select_difference_witness_with_mode(
        &mut self,
        mode: StoreChainSelectDifferenceWitnessMode,
    ) -> Option<TheoryResult> {
        // #7956 store-chain eq-path wall: arm the frozen-graph memo window for
        // the pair loop below. Every memoized function it reaches
        // (`find_store_through_eq_with_mode`, `equality_reason_paths_from`,
        // `explain_equal/distinct_if_provable`,
        // `select_alias_diseq_candidate_pairs`) is a pure function of the
        // equality graph, assignments, external-fact maps, `store_cache`,
        // `diseq_set` and `requested_interface_eqs` — none of which the loop
        // mutates. The only `&mut self` effect on this path
        // (`mark_model_equality_requested` → `requested_model_eqs`) is not an
        // input to any memoized function, so hits stay byte-identical to
        // recomputation. `activate_if_inactive` keeps an enclosing window
        // (none today) warm instead of shadowing it.
        let _eq_paths_cache_guard = eq_paths_cache::activate_if_inactive();

        const MAX_SUPPORT_LEMMAS: usize = 1;
        const MAX_SUPPORT_SELECT_DISEQ_REASONS: usize = 3;

        type SupportCandidateScore = (bool, usize, bool, bool, usize, usize, usize);

        let mut lemma_candidates: Vec<(SupportCandidateScore, TheoryLemma, Vec<TermId>)> =
            Vec::new();
        let mut eq_cache = HashMap::default();
        let mut store_chain_cache = HashMap::default();
        for (sel1_term, sel2_term) in self.select_alias_diseq_candidate_pairs() {
            let Some(&(array1, index1)) = self.select_cache.get(&sel1_term) else {
                continue;
            };
            let Some(&(array2, index2)) = self.select_cache.get(&sel2_term) else {
                continue;
            };

            // M5 verdict-only authority flip (SingletonOnly witness only): the
            // near-linear weak-equivalence graph authoritatively decides
            // *no conflict*. If `array1` and `array2` are in different weak-eq
            // components they cannot share a common base, so the legacy
            // `base_eq` below (`explain_equal_if_provable`, over `eq_adj`)
            // provably fails and no witness can ever fire — prune here, before
            // the O(store-chain) effective-store collection, instead of
            // discovering it several expensive steps later. Legacy stays the
            // SOLE (support, reasons) producer on surviving pairs, so reasons
            // are byte-identical. Sound: `build_weak_equiv_graph` ingests a
            // superset of the edges `explain_equal_if_provable` can traverse, so
            // `base_eq ⟹ weakly_connected` by construction (enforced corpus-wide
            // by the `weq5_shadow` differential assert after the support step).
            if mode == StoreChainSelectDifferenceWitnessMode::SingletonOnly
                && !self.weakly_connected(array1, array2)
            {
                #[cfg(debug_assertions)]
                weak_equiv::weq5_shadow::record_graph_pruned();
                continue;
            }

            if self.store_chain_reaches_asserted(array1, array2)
                || self.store_chain_reaches_asserted(array2, array1)
            {
                continue;
            }

            let Some(index_eq_reasons) = self.explain_equal_cached(&mut eq_cache, index1, index2)
            else {
                continue;
            };
            let Some(select_diseq_reasons) =
                self.explain_distinct_select_aliases(&mut eq_cache, sel1_term, sel2_term)
            else {
                continue;
            };
            if select_diseq_reasons.len() > MAX_SUPPORT_SELECT_DISEQ_REASONS {
                continue;
            }

            let Some((base1, base1_reasons, map1)) = self
                .collect_complete_effective_stores_asserted_cached(&mut store_chain_cache, array1)
            else {
                continue;
            };
            let Some((base2, base2_reasons, map2)) = self
                .collect_complete_effective_stores_asserted_cached(&mut store_chain_cache, array2)
            else {
                continue;
            };
            let Some(base_eq_reasons) = self.explain_equal_cached(&mut eq_cache, base1, base2)
            else {
                continue;
            };

            let (support, map_reasons) =
                self.store_chain_difference_support(&map1, &map2, &mut eq_cache);

            // M5 differential (shadow, debug-only): this pair's legacy `base_eq`
            // holds (we are past its `?`), so it is a witness-eligible pair.
            // Record the graph verdict against the legacy support outcome. The
            // `record_base_eq` call asserts the wrong-SAT soundness gate
            // (`base_eq ⟹ weakly_connected`, the M3 ext-eq vector) and
            // accumulates the M6-feasibility contingency (`sc` / `mj` vs support
            // emptiness). Runs in BOTH modes so the assert covers the widest
            // corpus, including the BroadFallback pairs the flip does not prune.
            #[cfg(debug_assertions)]
            weak_equiv::weq5_shadow::record_base_eq(
                self.weakly_connected(array1, array2),
                self.weak_equiv_graph().strongly_connected(array1, array2),
                self.weakly_equiv_mod_j(array1, array2, index1),
                support.is_empty(),
            );

            if support.is_empty() {
                continue;
            }
            if mode == StoreChainSelectDifferenceWitnessMode::SingletonOnly && support.len() != 1 {
                continue;
            }

            let mut support_reason = Vec::new();
            support_reason.extend(select_diseq_reasons.iter().copied());
            support_reason.extend(index_eq_reasons.iter().copied());
            support_reason.extend(base1_reasons.iter().copied());
            support_reason.extend(base2_reasons.iter().copied());
            support_reason.extend(base_eq_reasons.iter().copied());
            support_reason.extend(map_reasons.iter().copied());
            support_reason.sort_by_key(|lit| (lit.term.0, lit.value));
            support_reason.dedup_by_key(|lit| (lit.term, lit.value));
            let candidate_score = (
                support.len() == 1,
                usize::MAX.saturating_sub(support.len()),
                index_eq_reasons.is_empty(),
                base1_reasons.is_empty() && base2_reasons.is_empty() && base_eq_reasons.is_empty(),
                usize::MAX.saturating_sub(select_diseq_reasons.len()),
                usize::MAX.saturating_sub(support_reason.len()),
                map1.len() + map2.len(),
            );

            let mut support_eq_terms = Vec::new();
            let mut candidate_requests = Vec::new();
            let mut seen_candidate_requests = HashSet::default();
            let mut support_already_satisfied = false;
            for &idx in &support {
                // #qfax-vacuous-loop: idx == index1 means the disequal read
                // is already located AT the differing support index — the
                // support is satisfied by identity; find_eq would return the
                // constant true term, which is never in `assigns`, so the
                // old check missed it and re-learned a tautology forever.
                if idx == index1 {
                    support_already_satisfied = true;
                    break;
                }
                if let Some(eq_term) = self.terms.find_eq(index1, idx) {
                    if self.assigns.get(&eq_term) == Some(&true) {
                        support_already_satisfied = true;
                        break;
                    }
                    let key = Self::ordered_pair(index1, idx);
                    if !self.model_equality_already_requested(index1, idx)
                        && seen_candidate_requests.insert(key)
                    {
                        let request = ModelEqualityRequest {
                            lhs: index1,
                            rhs: idx,
                            reason: support_reason.clone(),
                            implied: true,
                        };
                        candidate_requests.push(request);
                        continue;
                    }
                    support_eq_terms.push(eq_term);
                    continue;
                }

                let key = Self::ordered_pair(index1, idx);
                if !self.model_equality_already_requested(index1, idx)
                    && seen_candidate_requests.insert(key)
                {
                    let request = ModelEqualityRequest {
                        lhs: index1,
                        rhs: idx,
                        reason: support_reason.clone(),
                        implied: true,
                    };
                    candidate_requests.push(request);
                    continue;
                }
            }

            if support_already_satisfied {
                continue;
            }

            if !candidate_requests.is_empty() {
                if support.len() != 1 {
                    continue;
                }
                for request in &candidate_requests {
                    self.mark_model_equality_requested(request.lhs, request.rhs);
                }
                return match candidate_requests.len() {
                    1 => Some(TheoryResult::NeedModelEquality(
                        candidate_requests
                            .pop()
                            .expect("invariant: len checked above"),
                    )),
                    _ => Some(TheoryResult::NeedModelEqualities(candidate_requests)),
                };
            }

            if support_eq_terms.len() != support.len() {
                continue;
            }
            support_eq_terms.sort_unstable_by_key(|term| term.0);
            support_eq_terms.dedup();
            if support_eq_terms.is_empty() || support_reason.is_empty() {
                continue;
            }

            if support_eq_terms
                .iter()
                .any(|term| self.assigns.get(term) == Some(&true))
            {
                continue;
            }

            let mut clause: Vec<TheoryLit> = support_reason
                .into_iter()
                .map(|lit| TheoryLit::new(lit.term, !lit.value))
                .collect();
            for support_eq_term in &support_eq_terms {
                clause.push(TheoryLit::new(*support_eq_term, true));
            }
            clause.sort_by_key(|lit| (lit.term.0, lit.value));
            clause.dedup_by_key(|lit| (lit.term, lit.value));
            if clause.is_empty() {
                continue;
            }

            // #lemma-must-prune / #refine-theory-memory: an already-satisfied or
            // already-applied clause is a no-op — emitting it stalls the loop.
            if self.lemma_is_unproductive(&clause) {
                continue;
            }

            if support_eq_terms.len() == 1 {
                let lemma = TheoryLemma::new(clause);
                return Some(TheoryResult::NeedLemmas(vec![lemma]));
            }

            if mode == StoreChainSelectDifferenceWitnessMode::SingletonOnly {
                continue;
            }

            lemma_candidates.push((candidate_score, TheoryLemma::new(clause), support_eq_terms));
        }

        if !lemma_candidates.is_empty() {
            lemma_candidates.sort_by_key(|right| std::cmp::Reverse(right.0));
            let mut seen = HashSet::default();
            let mut lemmas = Vec::new();
            for (_score, lemma, _support_eq_terms) in lemma_candidates {
                if lemma.clause.is_empty() || !seen.insert(lemma.clause.clone()) {
                    continue;
                }
                lemmas.push(lemma);
                if lemmas.len() >= MAX_SUPPORT_LEMMAS {
                    break;
                }
            }
            if lemmas.is_empty() {
                return None;
            }
            return Some(TheoryResult::NeedLemmas(lemmas));
        }

        None
    }

    /// Check const-array read axiom:
    /// select(const-array(v), i) = v for any index i.
    ///
    /// Event-driven (#6546 Step 1): processes `pending_const_reads` queue.
    pub(crate) fn check_const_array_read(&mut self) -> Option<TheoryResult> {
        let pairs = self.pending_const_reads.take();
        let mut sorted = pairs;
        sorted.sort_by_key(|&(sel, _)| sel.0);
        sorted.dedup();

        // Only the pathological "array merged with two const-arrays" guard needs
        // to scan for sibling const-arrays; skip that work in the common case.
        let multiple_const_arrays = self.const_array_cache.len() >= 2;

        let mut retained = Vec::new();
        for (select_term, const_array_term) in sorted {
            let Some(&default_val) = self.const_array_cache.get(&const_array_term) else {
                retained.push((select_term, const_array_term));
                continue;
            };

            // SOUNDNESS (const-read): the read axiom `select(arr,i) = default(C)`
            // is conditional on `arr =_E C`. Building a value-distinctness
            // conflict lemma from the value reasons ALONE dropped that premise.
            // For example with `I = const(1)` and a *decided* `I = const(0)`,
            // `select(I,d)` is read as both 1 (via const(1)) and 0 (via
            // const(0)); the unit lemma `NOT(= 1 (select I d))` was then emitted,
            // asserting `select(I,d) != 1` unconditionally and — because lemmas
            // persist across backtracking — producing spurious UNSAT on the SAT
            // formula `I = const(1) /\ J = store(const(0),5,1) /\ I != J`.
            //
            // Guard 1: when `arr`'s class is joined to two const-arrays with
            // provably-distinct defaults, those const-arrays are extensionally
            // distinct, so the equality chain that joined them is itself the
            // conflict. Resolve that (`NOT(C =_E C')`) — a sound clause whose
            // reasons fully justify the contradiction.
            if multiple_const_arrays {
                if let Some(conflict) =
                    self.const_array_class_distinct_default_conflict(const_array_term, default_val)
                {
                    self.pending_const_reads.replace(retained);
                    return Some(conflict);
                }
            }

            // Guard 2: re-verify `arr =_E C` before emitting a value-distinctness
            // lemma, AND capture the equality's reasons so they enter the lemma.
            //
            // The const-read axiom `select(arr, i) = default(C)` is conditional on
            // `arr =_E C`. Two failures of the previous boolean guard produced false
            // UNSAT (#A1 family):
            //   * It accepted equiv-class membership established only by a SPECULATIVE
            //     Nelson-Oppen interface equality (a sentinel/model merge, not a
            //     theorem) — e.g. a free array's store `store(A1,a,b)` gets merged
            //     with a const-array during the N-O split, so the const default leaks
            //     onto an unrelated free select and an actually-SAT formula is closed.
            //   * Even for a genuine equality it dropped that premise from the lemma,
            //     so the emitted `NOT(select = v)` was unconditional and SAT could not
            //     backtrack into the `arr != C` branch.
            //
            // `explain_equal_if_provable` skips sentinel edges, so it returns `None`
            // for a speculative-only merge — fail closed (retain, no lemma) there.
            // When it returns reasons they are real SAT literals; fold them into the
            // lemma so `NOT[(arr =_E C) AND (select != default)]` is a sound, fully
            // justified clause SAT can resolve against. The direct-const-read case
            // (`arr == C`) yields empty reasons, so well-behaved reads are unaffected.
            let Some(&(arr, _)) = self.select_cache.get(&select_term) else {
                retained.push((select_term, const_array_term));
                continue;
            };
            let Some(arr_eq_reasons) = self.explain_equal_if_provable(arr, const_array_term) else {
                retained.push((select_term, const_array_term));
                continue;
            };

            if let Some(val_diseq_reasons) =
                self.explain_distinct_if_provable(select_term, default_val)
            {
                if val_diseq_reasons.is_empty() {
                    retained.push((select_term, const_array_term));
                    continue;
                }
                let mut reasons = arr_eq_reasons;
                reasons.extend(val_diseq_reasons);
                reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                reasons.dedup_by_key(|lit| (lit.term, lit.value));
                self.pending_const_reads.replace(retained);
                return self.conflict_reasons_to_lemma(reasons);
            }
            retained.push((select_term, const_array_term));
        }
        self.pending_const_reads.replace(retained);
        None
    }

    /// If `const_array_term`'s equivalence class contains another const-array
    /// whose default value is provably distinct, the two const-arrays are
    /// extensionally distinct yet currently equal — a conflict. Returns the
    /// conflict lemma negating the equality chain that joined them
    /// (`NOT(C =_E C')`), which is sound and fully justified.
    fn const_array_class_distinct_default_conflict(
        &self,
        const_array_term: TermId,
        default_val: TermId,
    ) -> Option<TheoryResult> {
        for other in self.get_equiv_class(const_array_term) {
            if other == const_array_term {
                continue;
            }
            let Some(&other_default) = self.const_array_cache.get(&other) else {
                continue;
            };
            // Defaults must be provably distinct for the arrays to be distinct.
            let Some(default_diseq_reasons) =
                self.explain_distinct_if_provable(default_val, other_default)
            else {
                continue;
            };
            // The SAT-visible equality chain joining the two const-arrays is the
            // set of literals that must be negated.
            let Some(eq_reasons) = self.explain_equal_if_provable(const_array_term, other) else {
                continue;
            };
            let mut reasons = eq_reasons;
            reasons.extend(default_diseq_reasons);
            reasons.sort_by_key(|lit| (lit.term.0, lit.value));
            reasons.dedup_by_key(|lit| (lit.term, lit.value));
            if reasons.is_empty() {
                continue;
            }
            return self.conflict_reasons_to_lemma(reasons);
        }
        None
    }

    /// Check select-map axiom (#8533):
    /// select(map[f](a1,...,an), i) = f(select(a1,i),...,select(an,i))
    ///
    /// The primary select-map rewrite is handled eagerly in `mk_select()` at
    /// term construction time (Z3 array_rewriter.cpp:296-306). This theory
    /// solver check handles the case where a map term becomes equal to a
    /// select's array through the equality graph at runtime.
    ///
    /// For each `(select_term, map_term)` pair in the queue, if the select's
    /// array is equal to the map term, we generate a lemma asserting
    /// `select(X, i) = f(select(a1,i), ..., select(an,i))`.
    ///
    /// This is modeled after Z3's `instantiate_select_map_axiom` in
    /// `theory_array_full.cpp:458`.
    ///
    /// Event-driven (#8533): processes `pending_select_map` queue.
    pub(crate) fn check_select_map(&mut self) -> Option<TheoryResult> {
        let pairs = self.pending_select_map.take();
        if pairs.is_empty() {
            return None;
        }

        let mut sorted = pairs;
        sorted.sort_by_key(|&(sel, map)| (sel.0, map.0));
        sorted.dedup();

        let mut lemmas: Vec<TheoryLemma> = Vec::new();
        let mut retained = Vec::new();

        for (select_term, map_term) in sorted {
            // Validate that the select and map are still in the caches.
            let Some(&(sel_array, sel_index)) = self.select_cache.get(&select_term) else {
                continue;
            };
            let Some((func_name, map_arrays)) = self.map_cache.get(&map_term).cloned() else {
                continue;
            };

            // Check: the select's array must be equal to the map term
            // (either syntactically or through the equality graph).
            if sel_array != map_term && !self.known_equal(sel_array, map_term) {
                retained.push((select_term, map_term));
                continue;
            }

            // Build the RHS: f(select(a1, i), ..., select(an, i))
            // We need to create select terms for each map array argument,
            // then apply the function. The terms are created via TermStore.
            //
            // Note: we cannot borrow self.terms mutably here since we hold
            // a shared ref to self. Instead, collect the data we need, then
            // check if the rewrite result is already known to conflict.
            //
            // The select-map axiom creates new terms:
            //   select(a_k, i) for each k, and f(select(a1,i),...,select(an,i))
            // These are created lazily by mk_select (which itself applies
            // the eager rewrite for nested map terms).
            //
            // For the theory solver, we cannot create terms (TermStore is
            // borrowed immutably). Instead, check if matching select terms
            // already exist and detect conflicts through those.
            //
            // If no existing select terms match, the axiom was already handled
            // by the eager rewrite at term construction time.

            // Look for existing select(a_k, i) terms for each map array arg.
            let mut all_selects_exist = true;
            let mut arg_select_terms: Vec<TermId> = Vec::with_capacity(map_arrays.len());
            for &arr in &map_arrays {
                if let Some(&existing_sel) = self.select_pair_index.get(&(arr, sel_index)) {
                    arg_select_terms.push(existing_sel);
                } else {
                    // No existing select(a_k, i) term. The eager rewrite in
                    // mk_select would have created it if the select was syntactically
                    // over this map term. Since it wasn't, we may need a model equality
                    // request to expose the axiom. Retain for later.
                    all_selects_exist = false;
                    break;
                }
            }

            if !all_selects_exist {
                retained.push((select_term, map_term));
                continue;
            }

            // Now check if there's a function application f(select(a1,i),...,select(an,i))
            // already in the term store. If so, check for a conflict between
            // select_term and that function application.
            //
            // We search for an App(func_name, arg_select_terms) in the term store.
            // If it exists and is known distinct from select_term, that's a conflict.
            //
            // #8598: Also search through equivalence classes of arg_select_terms.
            // When select(b, i) is over an alias of map[f](a) and the formula
            // contains f(v) where v =_E select(a,i), find_app with exact TermIds
            // won't match. Searching equivalence classes finds f(v) through the
            // equality graph.
            let func_app_result: Option<(TermId, Vec<TheoryLit>)> = self
                .terms
                .find_app(&Symbol::named(&func_name), &arg_select_terms)
                .map(|fa| (fa, Vec::new()))
                .or_else(|| self.find_func_app_via_equiv_classes(&func_name, &arg_select_terms));

            if let Some((func_app, equiv_eq_reasons)) = func_app_result {
                // The select-map axiom says select_term = func_app.
                // If they're known distinct, we have a conflict.
                if let Some(diseq_reasons) =
                    self.explain_distinct_if_provable(select_term, func_app)
                {
                    let mut reasons = diseq_reasons;

                    // Add the equality justification: sel_array =_E map_term
                    if sel_array != map_term {
                        if let Some(eq_path) = self.asserted_equality_path_pub(sel_array, map_term)
                        {
                            for eq_term in eq_path {
                                reasons.push(TheoryLit::new(eq_term, true));
                            }
                        } else if let Some(eq) = self.get_eq_term(sel_array, map_term) {
                            reasons.push(TheoryLit::new(eq, true));
                        }
                    }

                    // #8598: Add reasons for arg equivalence class substitutions.
                    reasons.extend(equiv_eq_reasons.iter().copied());

                    reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                    reasons.dedup_by_key(|lit| (lit.term, lit.value));

                    if !reasons.is_empty() {
                        self.pending_select_map.replace(retained);
                        return self.conflict_reasons_to_lemma(reasons);
                    }
                }

                // Not a conflict yet. Generate the axiom as a lemma:
                // NOT(sel_array = map_term) OR select_term = func_app
                //
                // This ensures the SAT solver learns the select-map relationship.
                if let Some(eq_atom) = self.get_eq_term(select_term, func_app) {
                    // If the equality atom already exists and is assigned true,
                    // the axiom is already satisfied — skip.
                    if self.assigns.get(&eq_atom) == Some(&true) {
                        continue;
                    }

                    let mut clause = Vec::new();
                    if sel_array != map_term {
                        if let Some(arr_eq) = self.get_eq_term(sel_array, map_term) {
                            clause.push(TheoryLit::new(arr_eq, false));
                        }
                    }
                    clause.push(TheoryLit::new(eq_atom, true));

                    if !clause.is_empty() {
                        clause.sort_by_key(|lit| (lit.term.0, lit.value));
                        clause.dedup_by_key(|lit| (lit.term, lit.value));
                        // #lemma-must-prune / #refine-theory-memory: skip no-op lemmas.
                        if self.lemma_is_unproductive(&clause) {
                            continue;
                        }
                        lemmas.push(TheoryLemma::new(clause));
                    }
                }
            }

            // Retain: the axiom may become relevant as more terms are created.
            retained.push((select_term, map_term));
        }

        self.pending_select_map.replace(retained);

        if lemmas.is_empty() {
            None
        } else {
            Some(TheoryResult::NeedLemmas(lemmas))
        }
    }

    /// Check select-as-array axiom (#8598):
    /// select(as-array[f], i) = f(i)
    ///
    /// When as-array[f] becomes equal to an array X through the equality graph,
    /// and we have select(X, i), generate the axiom select(X, i) = f(i).
    ///
    /// This handles the case where the eager rewrite in mk_select couldn't fire
    /// because the select was syntactically over X, not over as-array[f].
    ///
    /// Modeled after Z3's `instantiate_select_as_array_axiom` in
    /// `theory_array_full.cpp:637-666`.
    ///
    /// Event-driven: processes `pending_select_as_array` queue.
    pub(crate) fn check_select_as_array(&mut self) -> Option<TheoryResult> {
        let pairs = self.pending_select_as_array.take();
        if pairs.is_empty() {
            return None;
        }

        let mut sorted = pairs;
        sorted.sort_by_key(|&(sel, aa)| (sel.0, aa.0));
        sorted.dedup();

        let mut lemmas: Vec<TheoryLemma> = Vec::new();
        let mut retained = Vec::new();

        for (select_term, as_array_term) in sorted {
            // Validate that the select is still in cache.
            let Some(&(sel_array, sel_index)) = self.select_cache.get(&select_term) else {
                continue;
            };
            let Some(func_name) = self.as_array_cache.get(&as_array_term).cloned() else {
                continue;
            };

            // Check: the select's array must be equal to the as-array term.
            if sel_array != as_array_term && !self.known_equal(sel_array, as_array_term) {
                retained.push((select_term, as_array_term));
                continue;
            }

            // The axiom says: select(as-array[f], i) = f(i)
            // Look for f(i) or f(v) where v =_E i in the term store.
            let func_app_result: Option<(TermId, Vec<TheoryLit>)> = self
                .terms
                .find_app(&Symbol::named(&func_name), &[sel_index])
                .map(|fa| (fa, Vec::new()))
                .or_else(|| self.find_func_app_via_equiv_classes(&func_name, &[sel_index]));

            if let Some((func_app, equiv_eq_reasons)) = func_app_result {
                // The axiom says select_term = func_app.
                // If they're known distinct, we have a conflict.
                if let Some(diseq_reasons) =
                    self.explain_distinct_if_provable(select_term, func_app)
                {
                    let mut reasons = diseq_reasons;

                    // Add the equality justification: sel_array =_E as_array_term
                    if sel_array != as_array_term {
                        if let Some(eq_path) =
                            self.asserted_equality_path_pub(sel_array, as_array_term)
                        {
                            for eq_term in eq_path {
                                reasons.push(TheoryLit::new(eq_term, true));
                            }
                        } else if let Some(eq) = self.get_eq_term(sel_array, as_array_term) {
                            reasons.push(TheoryLit::new(eq, true));
                        }
                    }

                    // Add reasons for arg equivalence class substitutions.
                    reasons.extend(equiv_eq_reasons.iter().copied());

                    reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                    reasons.dedup_by_key(|lit| (lit.term, lit.value));

                    if !reasons.is_empty() {
                        self.pending_select_as_array.replace(retained);
                        return self.conflict_reasons_to_lemma(reasons);
                    }
                }

                // Not a conflict yet. Generate the axiom as a lemma:
                // NOT(sel_array = as_array_term) OR select_term = func_app
                if let Some(eq_atom) = self.get_eq_term(select_term, func_app) {
                    if self.assigns.get(&eq_atom) == Some(&true) {
                        continue;
                    }

                    let mut clause = Vec::new();
                    if sel_array != as_array_term {
                        if let Some(arr_eq) = self.get_eq_term(sel_array, as_array_term) {
                            clause.push(TheoryLit::new(arr_eq, false));
                        }
                    }
                    clause.push(TheoryLit::new(eq_atom, true));

                    if !clause.is_empty() {
                        clause.sort_by_key(|lit| (lit.term.0, lit.value));
                        clause.dedup_by_key(|lit| (lit.term, lit.value));
                        // #lemma-must-prune / #refine-theory-memory: skip no-op lemmas.
                        if self.lemma_is_unproductive(&clause) {
                            continue;
                        }
                        lemmas.push(TheoryLemma::new(clause));
                    }
                }
            }

            // Retain: the axiom may become relevant as more terms are created.
            retained.push((select_term, as_array_term));
        }

        self.pending_select_as_array.replace(retained);

        if lemmas.is_empty() {
            None
        } else {
            Some(TheoryResult::NeedLemmas(lemmas))
        }
    }

    /// Check default-const axiom (#8598):
    /// default(X) = v when X =_E const-array(v).
    ///
    /// Event-driven: processes `pending_default_const` queue.
    /// When `default(a)` exists and `a` becomes equal to `const-array(v)` through
    /// the equality graph, this detects the conflict if `default(a) != v`.
    pub(crate) fn check_default_const(&mut self) -> Option<TheoryResult> {
        let pairs = self.pending_default_const.take();
        if pairs.is_empty() {
            return None;
        }

        let mut sorted = pairs;
        sorted.sort_by_key(|&(def, ca)| (def.0, ca.0));
        sorted.dedup();

        let mut retained = Vec::new();

        for (default_term, const_array_term) in sorted {
            // Validate that the const-array is still in the cache.
            let Some(&default_val) = self.const_array_cache.get(&const_array_term) else {
                continue;
            };

            // Validate that the default term is still tracked.
            // default_cache maps array_arg -> default_term, so we need to find
            // the array_arg for this default_term.
            let default_array_arg = match self.terms.get(default_term) {
                TermData::App(sym, args) if sym.name() == "default" && args.len() == 1 => args[0],
                _ => continue,
            };

            // Check: the default's array arg must be equal to the const-array term.
            // Use equivalence class membership rather than known_equal() because
            // known_equal() only checks direct equality terms and affine form, but
            // the transitive chain a =_E b =_E const-array(v) requires graph traversal.
            let is_equal = default_array_arg == const_array_term
                || self.known_equal(default_array_arg, const_array_term)
                || {
                    let equiv = self.get_equiv_class(default_array_arg);
                    equiv.contains(&const_array_term)
                };
            if !is_equal {
                retained.push((default_term, const_array_term));
                continue;
            }

            // The axiom says: default(X) = v where X =_E const-array(v).
            // If default_term != default_val is provable, we have a conflict.
            if let Some(diseq_reasons) =
                self.explain_distinct_if_provable(default_term, default_val)
            {
                let mut reasons = diseq_reasons;

                // Add the equality justification: default_array_arg =_E const_array_term
                if default_array_arg != const_array_term {
                    if let Some(eq_path) =
                        self.asserted_equality_path_pub(default_array_arg, const_array_term)
                    {
                        for eq_term in eq_path {
                            reasons.push(TheoryLit::new(eq_term, true));
                        }
                    } else if let Some(eq) = self.get_eq_term(default_array_arg, const_array_term) {
                        reasons.push(TheoryLit::new(eq, true));
                    }
                }

                reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                reasons.dedup_by_key(|lit| (lit.term, lit.value));

                if !reasons.is_empty() {
                    self.pending_default_const.replace(retained);
                    return self.conflict_reasons_to_lemma(reasons);
                }
            }

            // Not a conflict yet. Try to generate a lemma:
            // NOT(default_array_arg = const_array_term) OR default_term = default_val
            if let Some(eq_atom) = self.get_eq_term(default_term, default_val) {
                if self.assigns.get(&eq_atom) == Some(&true) {
                    // Axiom already satisfied — skip.
                    continue;
                }

                let mut clause = Vec::new();
                if default_array_arg != const_array_term {
                    if let Some(arr_eq) = self.get_eq_term(default_array_arg, const_array_term) {
                        clause.push(TheoryLit::new(arr_eq, false));
                    }
                }
                clause.push(TheoryLit::new(eq_atom, true));

                if !clause.is_empty() {
                    clause.sort_by_key(|lit| (lit.term.0, lit.value));
                    clause.dedup_by_key(|lit| (lit.term, lit.value));
                    // #lemma-must-prune / #refine-theory-memory: emit only a
                    // lemma that can actually move the loop. An unproductive one
                    // is left PENDING (fall through to `retained`) so it is
                    // re-offered once it can prune.
                    if !self.lemma_is_unproductive(&clause) {
                        self.pending_default_const.replace(retained);
                        return Some(TheoryResult::NeedLemmas(vec![TheoryLemma::new(clause)]));
                    }
                }
            }

            // Retain: the axiom may become relevant as more terms are created.
            retained.push((default_term, const_array_term));
        }

        self.pending_default_const.replace(retained);
        None
    }

    /// Check self-store conflicts:
    /// If store(a, i, v) = a is asserted, then select(a, i) must equal v.
    pub(crate) fn check_self_store(&mut self) -> Option<TheoryResult> {
        let mut pairs = std::mem::take(&mut self.pending_self_store);
        pairs.sort_unstable_by_key(|&(eq, st)| (eq.0, st.0));
        pairs.dedup();

        let mut retained = Vec::new();
        let mut iter = pairs.into_iter();
        while let Some((eq_term, store_term)) = iter.next() {
            if self.assigns.get(&eq_term) != Some(&true) {
                continue;
            }

            let Some(&(lhs, rhs)) = self.equality_cache.get(&eq_term) else {
                continue;
            };
            let base_term = if lhs == store_term {
                rhs
            } else if rhs == store_term {
                lhs
            } else {
                continue;
            };

            let Some(&(store_base, store_idx, store_val)) = self.store_cache.get(&store_term)
            else {
                continue;
            };

            if !self.known_equal(base_term, store_base) {
                retained.push((eq_term, store_term));
                continue;
            }

            // Collect candidate selects from targeted sources (#6820):
            // 1. Exact select_pair_index lookups for (base_term, store_idx) and (store_base, store_idx)
            // 2. parent_selects from array_vars for base_term and store_base,
            //    filtered to those whose index is known-equal to store_idx
            //
            // This replaces the previous O(|select_cache|) fallback scan.
            let mut candidate_selects = Vec::with_capacity(8);
            if let Some(select_term) = self.get_exact_select_term(base_term, store_idx) {
                candidate_selects.push(select_term);
            }
            if store_base != base_term {
                if let Some(select_term) = self.get_exact_select_term(store_base, store_idx) {
                    candidate_selects.push(select_term);
                }
            }
            // Gather from parent_selects: these are all select(X, j) terms
            // where X is base_term or store_base. Filter to those where j is
            // known-equal to store_idx.
            for &arr_term in &[base_term, store_base] {
                if let Some(data) = self.array_vars.get(&arr_term) {
                    for &sel in &data.parent_selects {
                        if let Some(&(_, sel_idx)) = self.select_cache.get(&sel) {
                            if sel_idx == store_idx || self.known_equal(sel_idx, store_idx) {
                                candidate_selects.push(sel);
                            }
                        }
                    }
                }
            }
            candidate_selects.sort_unstable_by_key(|term| term.0);
            candidate_selects.dedup();

            for select_term in candidate_selects.iter().copied() {
                let Some(&(sel_array, sel_index)) = self.select_cache.get(&select_term) else {
                    continue;
                };
                if !self.known_equal(sel_array, base_term)
                    && !self.known_equal(sel_array, store_base)
                {
                    continue;
                }
                if !self.known_equal(sel_index, store_idx) {
                    continue;
                }

                if let Some(val_diseq_reasons) =
                    self.explain_distinct_if_provable(select_term, store_val)
                {
                    let mut reasons = val_diseq_reasons;

                    reasons.push(TheoryLit::new(eq_term, true));

                    if sel_array != base_term && sel_array != store_base {
                        if let Some(arr_eq) = self.get_eq_term(sel_array, base_term) {
                            reasons.push(TheoryLit::new(arr_eq, true));
                        } else if let Some(arr_eq) = self.get_eq_term(sel_array, store_base) {
                            reasons.push(TheoryLit::new(arr_eq, true));
                        }
                    }

                    if base_term != store_base {
                        if let Some(base_eq) = self.get_eq_term(base_term, store_base) {
                            reasons.push(TheoryLit::new(base_eq, true));
                        }
                    }

                    if sel_index != store_idx {
                        if let Some(idx_eq) = self.get_eq_term(sel_index, store_idx) {
                            reasons.push(TheoryLit::new(idx_eq, true));
                        }
                    }

                    if reasons.is_empty() {
                        continue;
                    }

                    retained.extend(iter);
                    self.pending_self_store = retained;
                    return self.conflict_reasons_to_lemma(reasons);
                }
            }

            retained.push((eq_term, store_term));
        }
        self.pending_self_store = retained;
        None
    }

    /// Check array equality conflicts:
    /// If a = b is asserted, then for any index i where we have both select(a, i) and select(b, i),
    /// they must be equal.
    ///
    /// Event-driven (#6820 Step 4): drains `pending_array_eqs` queue instead of
    /// scanning all equality_cache entries. Candidates are queued in
    /// `record_assignment` when an array equality is assigned true.
    /// Sound under-approximation of "this sort has exactly one inhabitant".
    ///
    /// Returns `true` ONLY when the sort is provably a singleton; returns
    /// `false` whenever cardinality is greater than one OR cannot be determined
    /// (uninterpreted sorts, recursive datatypes, etc.). This conservatism is
    /// required for soundness: the caller refutes an array disequality only when
    /// this returns `true`, so a false positive would drop genuine models.
    ///
    /// - `Bool`, `Int`, `Real`, `String`, `RegLan`, `BitVec` (width >= 1):
    ///   cardinality > 1 (or infinite) -> `false`.
    /// - `Array(_, elem)`: singleton iff the element sort is a singleton (the
    ///   only function into a singleton codomain is the constant function,
    ///   regardless of the index domain — including an empty domain).
    /// - `Datatype`: singleton iff it has exactly one constructor whose field
    ///   sorts are ALL singletons (recursively). A recursive occurrence is
    ///   treated as non-singleton (fail closed).
    /// - Uninterpreted / unknown sorts: `false` (cannot prove singleton).
    fn sort_cardinality_is_one(sort: &Sort) -> bool {
        Self::sort_cardinality_is_one_inner(sort, &mut Vec::new())
    }

    fn sort_cardinality_is_one_inner<'s>(sort: &'s Sort, in_progress: &mut Vec<&'s str>) -> bool {
        match sort {
            Sort::Array(arr) => Self::sort_cardinality_is_one_inner(&arr.element_sort, in_progress),
            Sort::Datatype(dt) => {
                if dt.constructors.len() != 1 {
                    return false;
                }
                // Guard against recursive datatypes: a constructor that refers
                // back to its own sort is not a provable singleton.
                if in_progress.contains(&dt.name.as_str()) {
                    return false;
                }
                in_progress.push(dt.name.as_str());
                let result = dt.constructors[0]
                    .fields
                    .iter()
                    .all(|field| Self::sort_cardinality_is_one_inner(&field.sort, in_progress));
                in_progress.pop();
                result
            }
            // Bool (2), Int/Real/String (infinite), RegLan (infinite),
            // BitVec (>= 2 for width >= 1), and any other / uninterpreted sort
            // are NOT provable singletons.
            _ => false,
        }
    }

    /// Refute an array disequality `a != b` when the array's ELEMENT sort has
    /// cardinality exactly one.
    ///
    /// If the element sort is a singleton, the array sort `(Array I E)` has a
    /// single inhabitant (the unique constant function), so `a` and `b` must be
    /// equal — any asserted disequality `a != b` is a theory conflict. We only
    /// fire when `sort_cardinality_is_one` PROVES the element sort is a
    /// singleton; otherwise we leave the disequality satisfiable (we never guess
    /// Sat/Unsat for an undetermined cardinality).
    /// (Soundness fix: card-1 element-sort array distinctness wrong-SAT family.)
    pub(crate) fn check_singleton_element_array_diseq(&self) -> Option<TheoryResult> {
        if self.diseq_set.is_empty() {
            return None;
        }
        for &(lhs, rhs) in &self.diseq_set {
            let lhs_sort = self.terms.sort(lhs);
            if !matches!(lhs_sort, Sort::Array(_)) {
                continue;
            }
            let Some(elem_sort) = lhs_sort.array_element() else {
                continue;
            };
            if !Self::sort_cardinality_is_one(elem_sort) {
                continue;
            }
            // The two arrays are forced equal, contradicting the disequality.
            // Justify with the disequality literal (the false-assigned equality
            // atom) or a reason-carrying external disequality.
            if let Some(eq_term) = self.get_eq_term(lhs, rhs) {
                if self.assigns.get(&eq_term) == Some(&false) {
                    return self.conflict_reasons_to_lemma(vec![TheoryLit::new(eq_term, false)]);
                }
            }
            if let Some(reasons) = self
                .external_diseq_reasons
                .get(&Self::ordered_pair(lhs, rhs))
            {
                if !reasons.is_empty() {
                    return self.conflict_reasons_to_lemma(reasons.clone());
                }
            }
        }
        None
    }

    /// Decide const-array vs const-array equality directly (sound + complete).
    ///
    /// `(= (as const A d1) (as const A d2))` is satisfiable iff `d1 = d2` as
    /// values: two const-arrays with distinct default values differ at EVERY
    /// index, so they can never be equal. When such an equality is asserted
    /// true and the two defaults are provably distinct, that is a theory
    /// conflict. This is the exact dual of the const-array read axiom
    /// (`select(const(d), i) = d`) and needs no index enumeration, so it is
    /// safe to run even when no selects/stores exist on the arrays.
    ///
    /// Non-destructive (does not drain `pending_array_eqs`) so it can be called
    /// from both `check_array_equality` and `final_check`'s early-Sat
    /// short-circuit. (Soundness fix: const-array=const-array wrong-SAT family.)
    pub(crate) fn check_const_array_equality_conflict(&self) -> Option<TheoryResult> {
        if self.const_array_cache.is_empty() || self.pending_array_eqs.is_empty() {
            return None;
        }
        for &(eq_term, lhs, rhs) in &self.pending_array_eqs {
            if self.assigns.get(&eq_term) != Some(&true) {
                continue;
            }
            let (Some(&lhs_default), Some(&rhs_default)) = (
                self.const_array_cache.get(&lhs),
                self.const_array_cache.get(&rhs),
            ) else {
                continue;
            };
            if lhs_default == rhs_default {
                continue;
            }
            if let Some(default_diseq_reasons) =
                self.explain_distinct_if_provable(lhs_default, rhs_default)
            {
                let mut reasons = default_diseq_reasons;
                reasons.push(TheoryLit::new(eq_term, true));
                return self.conflict_reasons_to_lemma(reasons);
            }
        }
        None
    }

    /// Effective read value of a store chain `(base, map)` at index `k`.
    ///
    /// Returns the term that `select(chain, k)` is provably equal to, together
    /// with the SAT-visible reasons justifying that equality, or `None` when the
    /// value cannot be pinned down (e.g. the base is an opaque array, or no
    /// provable index relation exists for an overlapping store).
    ///
    /// The returned reasons are exactly the read-over-write justification:
    /// for the matching store entry, `idx(entry) = k` plus the store's path
    /// reasons; for a const-array base, the reasons reaching that const-array.
    /// This is a logical consequence (read-over-write / const-read axiom), so
    /// it can only constrain — it never refutes a real model.
    fn effective_read_value_at(
        &self,
        base: TermId,
        map: &[(TermId, TermId, Vec<TheoryLit>)],
        k: TermId,
    ) -> Option<(TermId, Vec<TheoryLit>)> {
        // The map is ordered most-recent-store first (see
        // collect_complete_effective_stores). The first entry whose index is
        // provably equal to `k` wins; any entry whose index is provably
        // distinct from `k` is skipped. If an entry's index relation to `k` is
        // unknown, we cannot pin the read value, so bail.
        for (idx, val, store_reasons) in map {
            if let Some(idx_eq_reasons) = self.explain_equal_if_provable(*idx, k) {
                let mut reasons = store_reasons.clone();
                reasons.extend(idx_eq_reasons);
                Self::canonicalize_theory_lits(&mut reasons);
                return Some((*val, reasons));
            }
            self.explain_distinct_if_provable(*idx, k)?;
        }

        // No store overlaps `k`; the read falls through to the base. We can
        // only name the value when the base resolves to a const-array.
        let (default, base_reasons) = self.find_const_array_through_eq(base)?;
        Some((default, base_reasons))
    }

    /// Read-over-write conflict for an array equality between two finite store
    /// chains, neither of which need pre-existing selects.
    ///
    /// When `(= lhs rhs)` is asserted true and the two chains' effective store
    /// maps differ on some support index `k`, extensionality forces
    /// `select(lhs, k) = select(rhs, k)`. If the effective read values at `k`
    /// are provably distinct, that is a theory conflict. This materializes the
    /// extensionality witness at `k` directly from the asserted equality, rather
    /// than only off a pre-existing select disequality.
    ///
    /// Sound by construction: the only lemma emitted is
    /// `(= lhs rhs) -> select(lhs,k) = select(rhs,k)` (read-over-write +
    /// extensionality), combined with the already-asserted `select` value
    /// reasons and a provable `val_lhs != val_rhs`. It can only constrain.
    fn check_store_chain_equality_value_conflict(&self) -> Option<TheoryResult> {
        // Bound work: a handful of asserted array equalities, short chains.
        const MAX_CHAIN_LEN: usize = 64;
        let mut eq_cache: EqualityReasonCache = HashMap::default();

        for &(eq_term, lhs, rhs) in &self.pending_array_eqs {
            if self.assigns.get(&eq_term) != Some(&true) {
                continue;
            }
            if lhs == rhs {
                continue;
            }

            let Some((base1, base1_reasons, map1)) = self.collect_complete_effective_stores(lhs)
            else {
                continue;
            };
            let Some((base2, base2_reasons, map2)) = self.collect_complete_effective_stores(rhs)
            else {
                continue;
            };
            if map1.len() > MAX_CHAIN_LEN || map2.len() > MAX_CHAIN_LEN {
                continue;
            }
            if map1.is_empty() && map2.is_empty() {
                continue;
            }

            let (support, _support_reasons) =
                self.store_chain_difference_support(&map1, &map2, &mut eq_cache);

            for &k in &support {
                let Some((val1, val1_reasons)) = self.effective_read_value_at(base1, &map1, k)
                else {
                    continue;
                };
                let Some((val2, val2_reasons)) = self.effective_read_value_at(base2, &map2, k)
                else {
                    continue;
                };
                let Some(diseq_reasons) = self.explain_distinct_if_provable(val1, val2) else {
                    continue;
                };

                // Conflict: (= lhs rhs) forces select(lhs,k) = select(rhs,k),
                // but the reads are val1 and val2, which are provably distinct.
                let mut reasons = Vec::new();
                reasons.push(TheoryLit::new(eq_term, true));
                reasons.extend(base1_reasons.iter().copied());
                reasons.extend(base2_reasons.iter().copied());
                reasons.extend(val1_reasons);
                reasons.extend(val2_reasons);
                reasons.extend(diseq_reasons);
                return self.conflict_reasons_to_lemma(reasons);
            }
        }
        None
    }

    /// Decide const-array vs store-chain equality directly (sound, no selects).
    ///
    /// When a const-array `const(d)` is asserted equal to a store chain over an
    /// arbitrary (possibly FREE, non-const) base, the restricted-extensionality
    /// consequence is: for EVERY effective written index `i_k` of that chain,
    /// `select(arr, i_k) = d`. By ROW1 the chain reads `v_k` at `i_k`, and since
    /// `arr =_E const(d)`, that read also equals `d`; hence `v_k = d`. If the
    /// stored value `v_k` is provably distinct from `d`, that is a theory
    /// conflict — driven purely by the store INDEX, regardless of whether `v_k`
    /// is a leaf or a non-leaf arithmetic term.
    ///
    /// This is the dual of the const-array read axiom for the case where no
    /// `select` terms exist on the arrays (so `check_const_array_read` never
    /// fires). `collect_complete_effective_stores` supplies each effective
    /// entry's reasons (the alias path plus the provable index-distinctness that
    /// makes ROW1 read `v_k`), which fully justify the conflict.
    ///
    /// SOUNDNESS: every emitted clause is the negation of a set of currently-true
    /// SAT literals that TOGETHER imply `v_k = d`, contradicted by a provable
    /// `v_k != d`. No speculative/sentinel edge is used (`collect_complete_*`
    /// requires real reasons; `find_const_array_through_eq` skips reason-less
    /// sentinel edges). Posting only a logical consequence, it can never close a
    /// genuine model — i.e. it cannot introduce false UNSAT.
    ///
    /// Non-destructive (does not drain `pending_array_eqs`) so it can run from
    /// both `check_array_equality` and `final_check`'s early-Sat short-circuit.
    pub(crate) fn check_const_array_store_chain_conflict(&self) -> Option<TheoryResult> {
        if self.const_array_cache.is_empty() || self.pending_array_eqs.is_empty() {
            return None;
        }
        for &(eq_term, lhs, rhs) in &self.pending_array_eqs {
            if self.assigns.get(&eq_term) != Some(&true) {
                continue;
            }
            // One side must reach a const-array default; the other a store chain.
            // Try both orientations.
            for (const_side, chain_side) in [(lhs, rhs), (rhs, lhs)] {
                let Some((default_val, const_reasons)) =
                    self.find_const_array_through_eq(const_side)
                else {
                    continue;
                };
                let Some((_base, base_reasons, effective_map)) =
                    self.collect_complete_effective_stores(chain_side)
                else {
                    continue;
                };
                if effective_map.is_empty() {
                    // Pure const = const (no writes) is handled elsewhere.
                    continue;
                }
                // Examine every effective written index: each carries the
                // obligation select(arr, i_k) = d, i.e. v_k = d.
                for (_idx_k, val_k, entry_reasons) in &effective_map {
                    let Some(val_diseq_reasons) =
                        self.explain_distinct_if_provable(*val_k, default_val)
                    else {
                        continue;
                    };
                    // TERMINATION/STABILITY: only fire when `v_k != d` is a
                    // STRUCTURAL distinctness (distinct constants or a
                    // tautological affine offset), which yields EMPTY reasons.
                    // A non-empty justification means the distinctness rests on
                    // a SAT-level disequality or a transient arithmetic decision
                    // (e.g. `1 != x` after the solver tries `x = 5`); re-deriving
                    // the obligation under each such decision would emit a stream
                    // of ever-different conflict clauses and churn the DPLL(T)
                    // loop without progress (and the formula is typically SAT
                    // there). The refutation this bug needs (`5 != 8`: a concrete
                    // written value vs the const default) is always structural,
                    // so this restriction preserves the fix while guaranteeing
                    // bounded, terminating emission.
                    if !val_diseq_reasons.is_empty() {
                        continue;
                    }
                    let mut reasons = Vec::new();
                    // arr =_E const(d): the asserted array equality plus the
                    // alias path that reaches the const default.
                    reasons.push(TheoryLit::new(eq_term, true));
                    reasons.extend(const_reasons.iter().copied());
                    // arr's chain structure + the ROW1 index-distinctness that
                    // makes this write effective (so select(arr, i_k) = v_k).
                    reasons.extend(base_reasons.iter().copied());
                    reasons.extend(entry_reasons.iter().copied());
                    // v_k != d (the refutation).
                    reasons.extend(val_diseq_reasons);
                    reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                    reasons.dedup_by_key(|lit| (lit.term, lit.value));
                    if reasons.is_empty() {
                        continue;
                    }
                    return self.conflict_reasons_to_lemma(reasons);
                }
            }
        }
        None
    }

    pub(crate) fn check_array_equality(&mut self) -> Option<TheoryResult> {
        // Const-array equality is decided directly, before the select-driven
        // O(N^2) loop, because it needs no selects/stores. Non-destructive so
        // it can also be invoked from final_check's early-Sat short-circuit.
        if let Some(conflict) = self.check_const_array_equality_conflict() {
            return Some(conflict);
        }

        // Store-chain equality read-over-write conflict (wrapped store-of-const
        // = store-chain extensionality witness). Non-destructive; runs before
        // the select-driven loop so it can fire with zero pre-existing selects.
        if let Some(conflict) = self.check_store_chain_equality_value_conflict() {
            return Some(conflict);
        }

        // Const-array = store-chain over a FREE base: post the const-read obligation
        // at every effective written index (drives by store INDEX, so a non-leaf
        // arith store value no longer suppresses the const-conflicting outer entry).
        if let Some(conflict) = self.check_const_array_store_chain_conflict() {
            return Some(conflict);
        }

        let mut candidates = std::mem::take(&mut self.pending_array_eqs);
        candidates.sort_unstable_by_key(|&(eq, _, _)| eq.0);
        candidates.dedup();

        // Build array_selects index from parent_selects (#6820), avoiding
        // O(|select_cache|) full scan. parent_selects for each array term
        // already tracks all select(arr, idx) terms syntactically on that array.
        let mut array_selects: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
        let mut needed_arrays: HashSet<TermId> = HashSet::default();
        for &(_, lhs, rhs) in &candidates {
            needed_arrays.insert(lhs);
            needed_arrays.insert(rhs);
        }
        for &arr in &needed_arrays {
            if let Some(data) = self.array_vars.get(&arr) {
                for &sel in &data.parent_selects {
                    if let Some(&(_, idx)) = self.select_cache.get(&sel) {
                        array_selects.entry(arr).or_default().push((idx, sel));
                    }
                }
            }
        }

        let mut retained = Vec::new();
        // #array-deadline-forward: this O(eqs x selects^2 x explain-BFS)
        // triple loop was measured running 30+s past the caller's wall
        // budget on QF_AX storecomm nf subset re-solves. Amortized
        // interrupt/deadline poll every 64 select pairs. FAIL-CLOSED on
        // stop: the current + remaining candidates are retained in
        // `pending_array_eqs` (exactly what a no-conflict pass does), and
        // the final_check boundary poll maps the stop to Unknown.
        let mut poll_tick: u32 = 0;
        for ci in 0..candidates.len() {
            let (eq_term, lhs, rhs) = candidates[ci];
            if self.assigns.get(&eq_term) != Some(&true) {
                continue;
            }

            let lhs_selects = array_selects.get(&lhs);
            let rhs_selects = array_selects.get(&rhs);
            if let (Some(lhs_selects), Some(rhs_selects)) = (lhs_selects, rhs_selects) {
                for &(idx1, sel1) in lhs_selects {
                    for &(idx2, sel2) in rhs_selects {
                        poll_tick = poll_tick.wrapping_add(1);
                        if poll_tick & 63 == 0 && self.interrupted_or_deadline() {
                            retained.push((eq_term, lhs, rhs));
                            retained.extend_from_slice(&candidates[ci + 1..]);
                            self.pending_array_eqs = retained;
                            return None;
                        }
                        // SOUNDNESS (#arr_lia561 wrong-UNSAT): `parent_selects` is
                        // merged across the equality/alias closure (including
                        // model/sentinel equalities), so a select listed under
                        // `lhs` may actually be `select(other, idx1)` for some
                        // `other` that is only equal to `lhs` via a MODEL equality
                        // not captured below. The read-over-write conflict
                        //   lhs = rhs ∧ idx1 = idx2  ⟹  select(lhs,idx1) = select(rhs,idx2)
                        // is only valid when `sel1` is genuinely a select on `lhs`
                        // and `sel2` on `rhs` (or on arrays PROVABLY equal to them,
                        // with that proof added to the reason set). Without this
                        // guard the lemma `sel1 = sel2 ∨ ¬(lhs=rhs) ∨ ¬(idx1=idx2)`
                        // is a false theorem (e.g. `sel1 = select(a3,K)` with
                        // `lhs = a1`, `a1 ≠ a3`), closing a spurious UNSAT.
                        let (sel1_array, _) = match self.select_cache.get(&sel1) {
                            Some(&entry) => entry,
                            None => continue,
                        };
                        let (sel2_array, _) = match self.select_cache.get(&sel2) {
                            Some(&entry) => entry,
                            None => continue,
                        };
                        let mut array_alias_reasons = Vec::new();
                        if sel1_array != lhs {
                            let Some(alias) = self.explain_equal_if_provable(sel1_array, lhs)
                            else {
                                continue;
                            };
                            array_alias_reasons.extend(alias);
                        }
                        if sel2_array != rhs {
                            let Some(alias) = self.explain_equal_if_provable(sel2_array, rhs)
                            else {
                                continue;
                            };
                            array_alias_reasons.extend(alias);
                        }
                        let Some(idx_eq_reasons) = self.explain_equal_if_provable(idx1, idx2)
                        else {
                            continue;
                        };
                        let Some(sel_diseq_reasons) = self.explain_distinct_if_provable(sel1, sel2)
                        else {
                            continue;
                        };

                        let mut reasons = sel_diseq_reasons;
                        reasons.push(TheoryLit::new(eq_term, true));
                        reasons.extend(idx_eq_reasons);
                        reasons.extend(array_alias_reasons);

                        self.pending_array_eqs = retained;
                        return self.conflict_reasons_to_lemma(reasons);
                    }
                }
            }
            // Retain for future re-checks.
            retained.push((eq_term, lhs, rhs));
        }
        self.pending_array_eqs = retained;
        None
    }
}
