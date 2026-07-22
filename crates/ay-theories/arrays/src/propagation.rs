// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality propagation for the array theory solver.
//!
//! Implements Nelson-Oppen equality propagation derived from array axioms:
//! - ROW1/ROW2 select-store resolution
//! - Store-chain resolution
//! - Array congruence propagation
//! - Store value injectivity
//! - Effective store map decomposition
//! - Cross-chain resolution through asserted array equalities
//! - Store permutation equality detection

use super::*;

struct StorePermutationForest {
    parent: Vec<usize>,
}

impl StorePermutationForest {
    fn new(len: usize) -> Self {
        Self {
            parent: (0..len).collect(),
        }
    }

    fn find(&mut self, idx: usize) -> usize {
        let parent = self.parent[idx];
        if parent == idx {
            idx
        } else {
            let root = self.find(parent);
            self.parent[idx] = root;
            root
        }
    }

    fn connected(&mut self, lhs: usize, rhs: usize) -> bool {
        self.find(lhs) == self.find(rhs)
    }

    fn union(&mut self, lhs: usize, rhs: usize) {
        let lhs_root = self.find(lhs);
        let rhs_root = self.find(rhs);
        if lhs_root != rhs_root {
            self.parent[rhs_root] = lhs_root;
        }
    }
}

impl ArraySolver<'_> {
    fn push_discovered_equality(
        seen_equalities: &mut HashSet<(TermId, TermId)>,
        result: &mut EqualityPropagationResult,
        lhs: TermId,
        rhs: TermId,
        mut reason: Vec<TheoryLit>,
    ) -> bool {
        if lhs == rhs {
            return false;
        }
        let key = Self::ordered_pair(lhs, rhs);
        if seen_equalities.insert(key) {
            reason.sort_by_key(|lit| (lit.term.0, lit.value));
            reason.dedup_by_key(|lit| (lit.term, lit.value));
            result
                .equalities
                .push(DiscoveredEquality::new(lhs, rhs, reason));
            true
        } else {
            false
        }
    }

    fn equality_already_discovered(
        seen_equalities: &HashSet<(TermId, TermId)>,
        lhs: TermId,
        rhs: TermId,
    ) -> bool {
        if lhs == rhs {
            return true;
        }
        seen_equalities.contains(&Self::ordered_pair(lhs, rhs))
    }

    fn equality_already_known_or_assigned_true(&self, lhs: TermId, rhs: TermId) -> bool {
        // #8785: Fresh array-theory instances can import equality facts from
        // the current N-O graph without retaining `sent_equalities`. Do not
        // send those facts back to EUF as if they were new propagation work.
        if self.known_equal(lhs, rhs) {
            return true;
        }
        let key = Self::ordered_pair(lhs, rhs);
        self.eq_pair_index
            .get(&key)
            .is_some_and(|eq_term| self.assigns.get(eq_term) == Some(&true))
    }

    fn store_map_indices_are_decided(
        &self,
        lhs: &[(TermId, TermId, Vec<TheoryLit>)],
        rhs: &[(TermId, TermId, Vec<TheoryLit>)],
    ) -> bool {
        let mut indices = Vec::with_capacity(lhs.len() + rhs.len());
        indices.extend(lhs.iter().map(|(idx, _, _)| *idx));
        indices.extend(rhs.iter().map(|(idx, _, _)| *idx));

        for i in 0..indices.len() {
            for j in (i + 1)..indices.len() {
                let a = indices[i];
                let b = indices[j];
                if a == b || self.get_equiv_class(a).contains(&b) {
                    continue;
                }
                if self.known_distinct(a, b) || self.distinct_by_affine_offset(a, b) {
                    continue;
                }
                return false;
            }
        }

        true
    }

    /// `select_cache` grouped by syntactic array term, memoized in the
    /// `eq_paths_cache` window (D3, SELECT-PAIRS blueprint) where
    /// `select_cache` is frozen; outside the window it is rebuilt per call.
    fn selects_by_array(&self) -> Rc<HashMap<TermId, Vec<TermId>>> {
        if let Some(hit) = eq_paths_cache::get_selects_by_array() {
            return hit;
        }
        let mut map: HashMap<TermId, Vec<TermId>> = HashMap::default();
        for (&select_term, &(array, _index)) in &self.select_cache {
            map.entry(array).or_default().push(select_term);
        }
        for selects in map.values_mut() {
            selects.sort_unstable_by_key(|term| term.0);
        }
        let map = Rc::new(map);
        eq_paths_cache::put_selects_by_array(&map);
        map
    }

    /// D3 (SELECT-PAIRS blueprint): enumerate only the selects on the two
    /// queried arrays instead of generating the global candidate universe and
    /// filtering it afterwards.
    ///
    /// Accepted-set preservation: the old path required (1) candidate-set
    /// membership (select classes disequal or constant-distinct), (2) a
    /// syntactic array match against `(lhs_array, rhs_array)`, (3) provable
    /// index equality, (4) `explain_distinct_if_provable` re-proving the
    /// select disequality with reasons. (2) means every pair the old code
    /// could accept lies inside `selects_by_array[lhs] x selects_by_array[rhs]`
    /// (both orientations covered: checks (3)/(4) are symmetric); (1) is
    /// subsumed by the independent re-proof (4), which draws on exactly the
    /// diseq_set / distinct-constant facts the candidate pre-filter used.
    fn has_select_disequality_witness_between_arrays(
        &self,
        lhs_array: TermId,
        rhs_array: TermId,
    ) -> bool {
        let by_array = self.selects_by_array();
        let (Some(lhs_selects), Some(rhs_selects)) =
            (by_array.get(&lhs_array), by_array.get(&rhs_array))
        else {
            return false;
        };

        for &sel_lhs in lhs_selects {
            let Some(&(_, sel_lhs_index)) = self.select_cache.get(&sel_lhs) else {
                continue;
            };
            for &sel_rhs in rhs_selects {
                if sel_lhs == sel_rhs {
                    continue;
                }
                let Some(&(_, sel_rhs_index)) = self.select_cache.get(&sel_rhs) else {
                    continue;
                };
                if self
                    .explain_equal_if_provable(sel_lhs_index, sel_rhs_index)
                    .is_none()
                {
                    continue;
                }
                if self
                    .explain_distinct_if_provable(sel_lhs, sel_rhs)
                    .is_some()
                {
                    return true;
                }
            }
        }

        false
    }

    /// Discover equalities implied by array axioms for Nelson-Oppen propagation (#4665).
    ///
    /// When `select(store(a, i, v), j)` and `i ≠ j` (including from external
    /// disequalities injected by the combined solver), ROW2 implies:
    ///   `select(store(a, i, v), j) = select(a, j)`
    ///
    /// When `select(store(a, i, v), j)` and `i = j`, ROW1 implies:
    ///   `select(store(a, i, v), j) = v`
    ///
    /// These discovered equalities are propagated to EUF so that transitive
    /// reasoning can detect conflicts (e.g., `sel1 = 42` and `sel2 ≠ 42`
    /// with ROW2-derived `sel1 = sel2`).
    pub(super) fn propagate_equalities_impl(&mut self) -> EqualityPropagationResult {
        // #8615: Early exit if the external interrupt flag is set. Array equality
        // propagation can be very expensive on seq push_back chains; returning
        // an empty result allows the DPLL(T) loop to check the interrupt flag
        // and return Unknown.
        if self.is_interrupted() {
            return EqualityPropagationResult::default();
        }

        self.populate_caches();
        // (#6820) Ensure equiv class cache is fresh for select_pair_index lookups.
        self.build_equiv_class_cache();

        // #6546: Short-circuit when the equality graph, term caches, and
        // external facts haven't changed since the last call. The sent_equalities
        // dedup set prevents returning duplicates, so if no new information was
        // added, the scan will find nothing new. This avoids O(n^2) re-scanning
        // on every N-O iteration when only the SAT assignment changed without
        // affecting the equality structure.
        let current_snapshot = (
            self.eq_adj_version,
            self.select_cache.len(),
            self.store_cache.len(),
            self.external_diseqs.len(),
            self.external_eqs.len(),
            self.diseq_set.len(),
        );
        if self.prop_eq_snapshot == Some(current_snapshot) {
            return EqualityPropagationResult::default();
        }

        // Enable `equality_reason_paths_from` memoization for the duration of the
        // (read-only w.r.t. the equality graph / assigns / external facts) select
        // scan below (#no-cross-flood). The RAII guard restores the prior cache
        // state on EVERY exit path — including the mid-loop interrupt returns and
        // panics — so the cache is never observed from a context where the inputs
        // may have changed.
        let _eq_paths_cache_guard = eq_paths_cache::activate();

        let mut result = EqualityPropagationResult::default();
        // Seed seen set with previously-sent equalities to prevent re-discovery
        // across N-O fixpoint iterations (#5121).
        let mut seen_equalities = self.sent_equalities.clone();
        macro_rules! push_equality {
            // `$source` names the deriving rule at each call site (kept for
            // readability; the former per-source trace counters are removed
            // with the `AY_8785_TRACE_ARRAY_PROP_EQ` instrumentation).
            ($source:ident, $lhs:expr, $rhs:expr, $reason:expr $(,)?) => {
                if !self.equality_already_known_or_assigned_true($lhs, $rhs) {
                    let _ = Self::push_discovered_equality(
                        &mut seen_equalities,
                        &mut result,
                        $lhs,
                        $rhs,
                        $reason,
                    );
                }
            };
        }
        let proven_equal_reasons =
            |lhs: TermId, rhs: TermId| self.explain_equal_if_provable(lhs, rhs);

        for (&select_term, &(array, index)) in &self.select_cache {
            // #8615: Check interrupt periodically to avoid indefinite looping.
            if self.is_interrupted() {
                return result;
            }
            // Check if array is a store term (possibly through equalities)
            let store_info =
                if let Some(&(base, store_idx, store_val)) = self.store_cache.get(&array) {
                    Some((base, store_idx, store_val, Vec::new()))
                } else {
                    // Check through equality-linked store terms
                    self.eq_adj.get(&array).and_then(|neighbors| {
                        neighbors.iter().find_map(|&(other, _)| {
                            let &(base, store_idx, store_val) = self.store_cache.get(&other)?;
                            let reasons = proven_equal_reasons(array, other)?;
                            Some((base, store_idx, store_val, reasons))
                        })
                    })
                };

            let Some((base_array, store_idx, store_val, store_reasons)) = store_info else {
                continue;
            };

            if let Some(diseq_reasons) = self.explain_distinct_if_provable(index, store_idx) {
                // ROW2: select(store(a, i, v), j) = select(a, j) when i ≠ j

                // Case 1: direct select(base_array, index) lookup
                if let Some(&other_select) = self.select_pair_index.get(&(base_array, index)) {
                    if other_select != select_term
                        && !Self::equality_already_discovered(
                            &seen_equalities,
                            select_term,
                            other_select,
                        )
                    {
                        let mut reasons = store_reasons.clone();
                        reasons.extend(diseq_reasons.clone());
                        push_equality!(row2_direct, select_term, other_select, reasons);
                    }
                }

                // Case 2: select(equiv_member, index) where equiv_member = base_array
                if let Some(class_idx) = self.equiv_class_map.get(&base_array) {
                    if let Some(class) = self.equiv_classes.get(*class_idx) {
                        for &member in class {
                            if member == base_array {
                                continue;
                            }
                            if let Some(&other_select) =
                                self.select_pair_index.get(&(member, index))
                            {
                                if other_select != select_term {
                                    if Self::equality_already_discovered(
                                        &seen_equalities,
                                        select_term,
                                        other_select,
                                    ) {
                                        continue;
                                    }
                                    let Some(mut reasons) =
                                        proven_equal_reasons(member, base_array)
                                    else {
                                        continue;
                                    };
                                    reasons.extend(store_reasons.clone());
                                    reasons.extend(diseq_reasons.clone());
                                    push_equality!(row2_alias, select_term, other_select, reasons,);
                                }
                            }
                        }
                    }
                }
            } else if self.known_equal(index, store_idx) {
                // ROW1: select(store(a, i, v), i) = v
                if !Self::equality_already_discovered(&seen_equalities, select_term, store_val) {
                    let mut reasons = store_reasons.clone();
                    reasons.extend(proven_equal_reasons(index, store_idx).unwrap_or_default());
                    push_equality!(row1, select_term, store_val, reasons);
                }
            }

            // Store-chain resolution
            if let Some((resolved_value, reasons)) =
                self.resolve_select_through_stores(array, index)
            {
                push_equality!(store_chain_direct, select_term, resolved_value, reasons);
            }
        }

        // #8615: Check interrupt before store-chain resolution loop.
        if self.is_interrupted() {
            return result;
        }

        // Store-chain resolution for N-O equality propagation (#5086, #6608).
        let select_entries: Vec<_> = self.select_cache.iter().map(|(&k, &v)| (k, v)).collect();
        type SelectReasonEntry = (TermId, Vec<TheoryLit>);
        type BaseSelectGroups = HashMap<(TermId, TermId), Vec<SelectReasonEntry>>;

        let mut base_groups: BaseSelectGroups = HashMap::default();
        let mut value_resolved: Vec<(TermId, TermId, Vec<TheoryLit>)> = Vec::new();
        for &(select_term, (array, index)) in &select_entries {
            let (resolution, reasons) =
                self.resolve_select_base_for_propagation_with_reasons(array, index);
            match resolution {
                SelectResolution::Value(val) => {
                    value_resolved.push((select_term, val, reasons));
                }
                SelectResolution::Base(base) => {
                    base_groups
                        .entry((base, index))
                        .or_default()
                        .push((select_term, reasons));
                }
                SelectResolution::Unresolved => {}
            }
        }
        for (select_term, val, reasons) in value_resolved {
            push_equality!(store_chain_value, select_term, val, reasons);
        }
        for (_key, group) in &base_groups {
            if group.len() < 2 {
                continue;
            }
            for i in 1..group.len() {
                let mut reasons = group[0].1.clone();
                reasons.extend(group[i].1.clone());
                push_equality!(store_chain_base_group, group[0].0, group[i].0, reasons);
            }
        }

        // Array congruence propagation (#5086).
        let mut array_to_selects: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
        for &(select_term, (array, index)) in &select_entries {
            array_to_selects
                .entry(array)
                .or_default()
                .push((index, select_term));
        }
        for (&_eq_term, &(lhs, rhs)) in &self.equality_cache {
            // #8615: Check interrupt in O(n^2) array congruence propagation loop.
            if self.is_interrupted() {
                return result;
            }
            if self.assigns.get(&_eq_term) != Some(&true) {
                continue;
            }
            if !matches!(self.terms.sort(lhs), Sort::Array(_)) {
                continue;
            }
            let lhs_selects = array_to_selects.get(&lhs).cloned().unwrap_or_default();
            let rhs_selects = array_to_selects.get(&rhs).cloned().unwrap_or_default();
            let mut propagated_index_classes: HashSet<TermId> = HashSet::default();
            for &(idx_l, sel_l) in &lhs_selects {
                for &(idx_r, sel_r) in &rhs_selects {
                    if sel_l != sel_r {
                        if Self::equality_already_discovered(&seen_equalities, sel_l, sel_r) {
                            continue;
                        }
                        let Some(mut reasons) = proven_equal_reasons(lhs, rhs) else {
                            continue;
                        };
                        let Some(idx_reasons) = proven_equal_reasons(idx_l, idx_r) else {
                            continue;
                        };
                        // #8785: For one asserted array equality and one
                        // equality class of select indices, a single
                        // representative select equality is enough. Other
                        // selects with the same array and an equal index are
                        // EUF-congruent to that representative, while affine
                        // or otherwise non-class equal indices still keep
                        // their own propagation below.
                        if self.known_equal(idx_l, idx_r)
                            && !propagated_index_classes
                                .insert(self.equiv_class_representative(idx_l))
                        {
                            continue;
                        }
                        reasons.extend(idx_reasons);
                        push_equality!(array_congruence, sel_l, sel_r, reasons);
                    }
                }
            }
        }
        // Same-array READ CONGRUENCE (#seed-1213-case-187): for two selects
        // over the SAME array term with PROVABLY EQUAL indices, propagate
        // `select(a,i) = select(a,j)` with the index-equality reasons. The
        // array-congruence loop above only covers selects over TWO arrays
        // linked by an asserted array equality; a single free array read at
        // `x` and `(+ y -1)` had NO propagation rule, so when the split
        // loop's model-equality atom `(= x (+ y -1))` was decided TRUE the
        // select equality was never derived, the arithmetic solver kept the
        // two reads at DISTINCT values (`(< (select arr2 x) (select arr2 (+ y
        // -1)))` stayed "satisfied"), and the candidate model violated read
        // congruence — the seed-1213/187 wrong-model witness. With this rule
        // the TRUE branch immediately yields `sel1 = sel2`, the arithmetic
        // conflict flips the atom, and the FALSE branch separates the
        // indices: the split becomes productive in both directions.
        for (&_array, sels) in &array_to_selects {
            if sels.len() < 2 {
                continue;
            }
            // Same bound as `undecided_index_pairs`' read-congruence class
            // bound: the rule exists for small formulas (the fuzz wrong-model
            // class); on 50+-read unsat families the O(reads^2) pass costs
            // seconds per solve for pairs that are never provably index-equal.
            const READ_CONGRUENCE_CLASS_BOUND: usize = 16;
            if sels.len() > READ_CONGRUENCE_CLASS_BOUND {
                continue;
            }
            if self.is_interrupted() {
                return result;
            }
            let mut propagated_index_classes: HashSet<TermId> = HashSet::default();
            for i in 0..sels.len() {
                for j in (i + 1)..sels.len() {
                    let (idx_l, sel_l) = sels[i];
                    let (idx_r, sel_r) = sels[j];
                    if sel_l == sel_r || idx_l == idx_r {
                        continue;
                    }
                    // #7956 index-congruence: keep the legacy `known_equal`
                    // class byte-identical (same gate, same reasons), and ADD
                    // exactly the affine-leaf-congruence class (`(+
                    // (seq_offset a) 1) = (+ (seq_offset b) 1)` from asserted
                    // `(seq_offset a) = (seq_offset b)`) that `known_equal`
                    // cannot see — the slices/range select-conflict discard
                    // chain. Int-only by construction (the leaf matcher
                    // rejects non-Int sorts), so BV/EUF index behavior is
                    // untouched.
                    let legacy_known_equal = self.known_equal(idx_l, idx_r);
                    let leaf_congruence_reasons = if legacy_known_equal {
                        None
                    } else {
                        self.explain_equal_by_affine_leaf_congruence(idx_l, idx_r)
                    };
                    if !legacy_known_equal && leaf_congruence_reasons.is_none() {
                        continue;
                    }
                    if Self::equality_already_discovered(&seen_equalities, sel_l, sel_r) {
                        continue;
                    }
                    // One representative per index equality class (same
                    // reasoning as the #8785 dedup above).
                    if !propagated_index_classes.insert(self.equiv_class_representative(idx_l)) {
                        continue;
                    }
                    let reasons = if legacy_known_equal {
                        let Some(reasons) = proven_equal_reasons(idx_l, idx_r) else {
                            continue;
                        };
                        reasons
                    } else {
                        leaf_congruence_reasons.expect("checked above")
                    };
                    push_equality!(same_array_read_congruence, sel_l, sel_r, reasons);
                }
            }
        }

        // Transitive array equalities via eq_adj
        let array_terms: Vec<TermId> = array_to_selects.keys().copied().collect();
        for &arr in &array_terms {
            // #8615: Check interrupt in transitive array equality propagation.
            if self.is_interrupted() {
                return result;
            }
            let equiv_class = self.get_equiv_class(arr);
            for &other_arr in &equiv_class {
                if other_arr == arr {
                    continue;
                }
                if let Some(other_selects) = array_to_selects.get(&other_arr) {
                    let arr_selects = array_to_selects.get(&arr).cloned().unwrap_or_default();
                    let mut propagated_index_classes: HashSet<TermId> = HashSet::default();
                    for &(idx_a, sel_a) in &arr_selects {
                        for &(idx_o, sel_o) in other_selects {
                            if sel_a != sel_o {
                                if Self::equality_already_discovered(&seen_equalities, sel_a, sel_o)
                                {
                                    continue;
                                }
                                let Some(mut reasons) = proven_equal_reasons(arr, other_arr) else {
                                    continue;
                                };
                                let Some(idx_reasons) = proven_equal_reasons(idx_a, idx_o) else {
                                    continue;
                                };
                                if self.known_equal(idx_a, idx_o)
                                    && !propagated_index_classes
                                        .insert(self.equiv_class_representative(idx_a))
                                {
                                    continue;
                                }
                                reasons.extend(idx_reasons);
                                push_equality!(transitive_array, sel_a, sel_o, reasons);
                            }
                        }
                    }
                }
            }
        }

        // #8615: Check interrupt before expensive O(n^2) propagation sections.
        if self.is_interrupted() {
            return result;
        }

        // Store value injectivity propagation (#6282).
        {
            let store_terms: Vec<TermId> = self.store_cache.keys().copied().collect();
            for &s1 in &store_terms {
                // #8615: Check interrupt in store value injectivity O(n^2) loop.
                if self.is_interrupted() {
                    return result;
                }
                let &(_base1, idx1, val1) = match self.store_cache.get(&s1) {
                    Some(v) => v,
                    None => continue,
                };
                let equiv = self.get_equiv_class(s1);
                for s2 in equiv {
                    if s2 <= s1 {
                        continue;
                    }
                    let &(_base2, idx2, val2) = match self.store_cache.get(&s2) {
                        Some(v) => v,
                        None => continue,
                    };
                    if !self.known_equal(idx1, idx2) {
                        continue;
                    }
                    if Self::equality_already_discovered(&seen_equalities, val1, val2) {
                        continue;
                    }
                    let Some(mut reasons) = proven_equal_reasons(s1, s2) else {
                        continue;
                    };
                    let Some(idx_reasons) = proven_equal_reasons(idx1, idx2) else {
                        continue;
                    };
                    reasons.extend(idx_reasons);
                    push_equality!(store_value_injective, val1, val2, reasons);
                }
            }
        }

        // Effective store map decomposition (#5086).
        for (&_eq_term, &(lhs, rhs)) in &self.equality_cache {
            // #8615: Check interrupt in effective store map decomposition.
            if self.is_interrupted() {
                return result;
            }
            if self.assigns.get(&_eq_term) != Some(&true) {
                continue;
            }
            if !matches!(self.terms.sort(lhs), Sort::Array(_)) {
                continue;
            }
            let lhs_map = self.collect_effective_stores(lhs);
            let rhs_map = self.collect_effective_stores(rhs);
            if let (
                Some((_base_a, _base_reasons_a, map_a)),
                Some((_base_b, _base_reasons_b, map_b)),
            ) = (lhs_map, rhs_map)
            {
                for (idx_a, val_a, store_reasons_a) in &map_a {
                    for (idx_b, val_b, store_reasons_b) in &map_b {
                        if Self::equality_already_discovered(&seen_equalities, *val_a, *val_b) {
                            continue;
                        }
                        let Some(mut reasons) = proven_equal_reasons(lhs, rhs) else {
                            continue;
                        };
                        let Some(idx_reasons) = proven_equal_reasons(*idx_a, *idx_b) else {
                            continue;
                        };
                        reasons.extend(store_reasons_a.iter().copied());
                        reasons.extend(store_reasons_b.iter().copied());
                        reasons.extend(idx_reasons);
                        push_equality!(effective_store, *val_a, *val_b, reasons);
                    }
                }
            }
        }

        // #8615: Check interrupt before cross-chain resolution.
        if self.is_interrupted() {
            return result;
        }

        // Cross-chain resolution through asserted array equalities (#6282).
        {
            let mut select_indices: Vec<TermId> =
                select_entries.iter().map(|&(_, (_, idx))| idx).collect();
            select_indices.sort_by_key(|t| t.0);
            select_indices.dedup();

            let mut index_to_selects: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
            for &(select_term, (array, index)) in &select_entries {
                index_to_selects
                    .entry(index)
                    .or_default()
                    .push((select_term, array));
            }

            let mut eq_pairs_seen: HashSet<(TermId, TermId)> = HashSet::default();
            let mut eq_pairs: Vec<(TermId, TermId)> = Vec::new();
            for (&_eq_term, &(lhs, rhs)) in &self.equality_cache {
                if self.assigns.get(&_eq_term) != Some(&true) {
                    continue;
                }
                if !matches!(self.terms.sort(lhs), Sort::Array(_)) {
                    continue;
                }
                let key = Self::ordered_pair(lhs, rhs);
                if eq_pairs_seen.insert(key) {
                    eq_pairs.push((lhs, rhs));
                }
            }

            for (lhs, rhs) in eq_pairs {
                // #8615: Check interrupt in cross-chain resolution O(n^2) loop.
                if self.is_interrupted() {
                    return result;
                }
                let Some(array_eq_reasons) = proven_equal_reasons(lhs, rhs) else {
                    continue;
                };
                for &idx in &select_indices {
                    let (lhs_res, lhs_res_reasons) =
                        self.resolve_select_base_for_propagation_with_reasons(lhs, idx);
                    let (rhs_res, rhs_res_reasons) =
                        self.resolve_select_base_for_propagation_with_reasons(rhs, idx);

                    let selects_at_idx = index_to_selects.get(&idx).cloned().unwrap_or_default();

                    match (lhs_res, rhs_res) {
                        (SelectResolution::Base(base_l), SelectResolution::Base(base_r)) => {
                            if base_l == base_r {
                                continue;
                            }
                            let lhs_sels: Vec<(TermId, Vec<TheoryLit>)> = selects_at_idx
                                .iter()
                                .filter_map(|&(sel, arr)| {
                                    if arr == base_l {
                                        Some((sel, Vec::new()))
                                    } else {
                                        proven_equal_reasons(arr, base_l)
                                            .map(|reasons| (sel, reasons))
                                    }
                                })
                                .collect();
                            let rhs_sels: Vec<(TermId, Vec<TheoryLit>)> = selects_at_idx
                                .iter()
                                .filter_map(|&(sel, arr)| {
                                    if arr == base_r {
                                        Some((sel, Vec::new()))
                                    } else {
                                        proven_equal_reasons(arr, base_r)
                                            .map(|reasons| (sel, reasons))
                                    }
                                })
                                .collect();
                            for (sel_l, sel_l_reasons) in &lhs_sels {
                                for (sel_r, sel_r_reasons) in &rhs_sels {
                                    if Self::equality_already_discovered(
                                        &seen_equalities,
                                        *sel_l,
                                        *sel_r,
                                    ) {
                                        continue;
                                    }
                                    let mut reasons = array_eq_reasons.clone();
                                    reasons.extend(lhs_res_reasons.clone());
                                    reasons.extend(rhs_res_reasons.clone());
                                    reasons.extend(sel_l_reasons.clone());
                                    reasons.extend(sel_r_reasons.clone());
                                    push_equality!(cross_chain_base_base, *sel_l, *sel_r, reasons);
                                }
                            }
                        }
                        (SelectResolution::Value(val_l), SelectResolution::Base(base_r)) => {
                            for &(sel, arr) in &selects_at_idx {
                                if Self::equality_already_discovered(&seen_equalities, sel, val_l) {
                                    continue;
                                }
                                let Some(mut reasons) = (if arr == base_r {
                                    Some(Vec::new())
                                } else {
                                    proven_equal_reasons(arr, base_r)
                                }) else {
                                    continue;
                                };
                                reasons.extend(array_eq_reasons.clone());
                                reasons.extend(lhs_res_reasons.clone());
                                reasons.extend(rhs_res_reasons.clone());
                                push_equality!(cross_chain_value_base, sel, val_l, reasons);
                            }
                        }
                        (SelectResolution::Base(base_l), SelectResolution::Value(val_r)) => {
                            for &(sel, arr) in &selects_at_idx {
                                if Self::equality_already_discovered(&seen_equalities, sel, val_r) {
                                    continue;
                                }
                                let Some(mut reasons) = (if arr == base_l {
                                    Some(Vec::new())
                                } else {
                                    proven_equal_reasons(arr, base_l)
                                }) else {
                                    continue;
                                };
                                reasons.extend(array_eq_reasons.clone());
                                reasons.extend(lhs_res_reasons.clone());
                                reasons.extend(rhs_res_reasons.clone());
                                push_equality!(cross_chain_base_value, sel, val_r, reasons);
                            }
                        }
                        (SelectResolution::Value(val_l), SelectResolution::Value(val_r)) => {
                            if Self::equality_already_discovered(&seen_equalities, val_l, val_r) {
                                continue;
                            }
                            let mut reasons = array_eq_reasons.clone();
                            reasons.extend(lhs_res_reasons.clone());
                            reasons.extend(rhs_res_reasons.clone());
                            push_equality!(cross_chain_value_value, val_l, val_r, reasons);
                        }
                        _ => {}
                    }
                }
            }
        }

        // #8615: Check interrupt before store permutation equality detection.
        if self.is_interrupted() {
            return result;
        }

        // Store permutation equality detection (#5086).
        {
            let mut chain_candidates: Vec<TermId> = Vec::new();
            for &(array, _index) in self.select_cache.values() {
                chain_candidates.push(array);
            }
            for (_eq_term, &(lhs, rhs)) in self.equality_cache.iter() {
                if matches!(self.terms.sort(lhs), Sort::Array(_)) {
                    chain_candidates.push(lhs);
                    chain_candidates.push(rhs);
                }
            }
            chain_candidates.sort();
            chain_candidates.dedup();

            type ReasonedStoreMap = Vec<(TermId, TermId, Vec<TheoryLit>)>;
            type ReasonedStoreChainEntry = (StoreChainEntry, Vec<TheoryLit>, ReasonedStoreMap);

            let mut chain_maps: Vec<ReasonedStoreChainEntry> = Vec::new();
            for array_term in &chain_candidates {
                if let Some((base, base_reasons, effective_map)) =
                    self.collect_effective_stores(*array_term)
                {
                    if !effective_map.is_empty() {
                        let plain_effective_map = effective_map
                            .iter()
                            .map(|(idx, val, _)| (*idx, *val))
                            .collect();
                        chain_maps.push((
                            (*array_term, base, plain_effective_map),
                            base_reasons,
                            effective_map,
                        ));
                    }
                }
            }

            let mut store_perm_forest = StorePermutationForest::new(chain_maps.len());

            // Group by base array and compare effective maps
            chain_maps.sort_by_key(|&((_, base, _), _, _)| base.0);
            let mut i = 0;
            while i < chain_maps.len() {
                // #8615: Check interrupt in store permutation O(n^2) loop.
                if self.is_interrupted() {
                    return result;
                }
                let base = (chain_maps[i].0).1;
                let mut j = i + 1;
                while j < chain_maps.len() && (chain_maps[j].0).1 == base {
                    j += 1;
                }
                for a in i..j {
                    for b in (a + 1)..j {
                        let base_a = (chain_maps[a].0).1;
                        let base_b = (chain_maps[b].0).1;
                        if Self::equality_already_discovered(
                            &seen_equalities,
                            (chain_maps[a].0).0,
                            (chain_maps[b].0).0,
                        ) {
                            store_perm_forest.union(a, b);
                            continue;
                        }
                        if store_perm_forest.connected(a, b) {
                            continue;
                        }
                        let Some(mut reasons) = self.effective_stores_match_with_reasons(
                            &chain_maps[a].2,
                            &chain_maps[b].2,
                        ) else {
                            continue;
                        };
                        let Some(base_reasons) = proven_equal_reasons(base_a, base_b) else {
                            continue;
                        };
                        let indices_decided =
                            self.store_map_indices_are_decided(&chain_maps[a].2, &chain_maps[b].2);
                        if indices_decided {
                            let lhs_array = (chain_maps[a].0).0;
                            let rhs_array = (chain_maps[b].0).0;
                            // #8785: For finite same-base store chains whose
                            // effective store indices are already equal or
                            // provably distinct, ROW/store-chain select
                            // reasoning carries the concrete obligations.
                            // Propagating the array-level permutation equality
                            // here only creates fresh interface waves in AUFLIA
                            // storecomm. The exception is an explicit
                            // select-disequality witness between the final
                            // arrays: then the equality is the direct path to
                            // the conflict, but only if the complete store maps
                            // really match. The partial effective-map walker can
                            // match subchains in `storecomm_invalid_*` cases.
                            if !self
                                .has_select_disequality_witness_between_arrays(lhs_array, rhs_array)
                            {
                                store_perm_forest.union(a, b);
                                continue;
                            }

                            let Some((complete_base_a, mut complete_reasons_a, complete_map_a)) =
                                self.collect_complete_effective_stores(lhs_array)
                            else {
                                continue;
                            };
                            let Some((complete_base_b, mut complete_reasons_b, complete_map_b)) =
                                self.collect_complete_effective_stores(rhs_array)
                            else {
                                continue;
                            };
                            let Some(mut complete_base_reasons) =
                                self.explain_equal_if_provable(complete_base_a, complete_base_b)
                            else {
                                continue;
                            };
                            let Some(mut complete_map_reasons) = self
                                .effective_stores_match_with_reasons(
                                    &complete_map_a,
                                    &complete_map_b,
                                )
                            else {
                                continue;
                            };

                            reasons.clear();
                            reasons.append(&mut complete_reasons_a);
                            reasons.append(&mut complete_reasons_b);
                            reasons.append(&mut complete_base_reasons);
                            reasons.append(&mut complete_map_reasons);
                        } else {
                            reasons.extend(chain_maps[a].1.clone());
                            reasons.extend(chain_maps[b].1.clone());
                            reasons.extend(base_reasons);
                        }
                        push_equality!(
                            store_permutation_same_base,
                            (chain_maps[a].0).0,
                            (chain_maps[b].0).0,
                            reasons,
                        );
                        store_perm_forest.union(a, b);
                    }
                }
                i = j;
            }

            // Cross-base equiv class store permutation
            for a in 0..chain_maps.len() {
                // #8615: Check interrupt in cross-base store permutation O(n^2) loop.
                if self.is_interrupted() {
                    return result;
                }
                for b in (a + 1)..chain_maps.len() {
                    let base_a = (chain_maps[a].0).1;
                    let base_b = (chain_maps[b].0).1;
                    if base_a == base_b {
                        continue;
                    }
                    if Self::equality_already_discovered(
                        &seen_equalities,
                        (chain_maps[a].0).0,
                        (chain_maps[b].0).0,
                    ) {
                        store_perm_forest.union(a, b);
                        continue;
                    }
                    if store_perm_forest.connected(a, b) {
                        continue;
                    }
                    let Some(mut reasons) = self
                        .effective_stores_match_with_reasons(&chain_maps[a].2, &chain_maps[b].2)
                    else {
                        continue;
                    };
                    let Some(base_reasons) = proven_equal_reasons(base_a, base_b) else {
                        continue;
                    };
                    reasons.extend(chain_maps[a].1.clone());
                    reasons.extend(chain_maps[b].1.clone());
                    reasons.extend(base_reasons);
                    push_equality!(
                        store_permutation_cross_base,
                        (chain_maps[a].0).0,
                        (chain_maps[b].0).0,
                        reasons,
                    );
                    store_perm_forest.union(a, b);
                }
            }
        }

        // Remember which equalities were sent so fresh AUFLIA combiners can
        // replay them and seed the array duplicate filter. Empty reasons are
        // unconditional array facts, so they are valid across assignments.
        for eq in &result.equalities {
            let replay = ArrayPropagatedEqualityReplay::new(eq.lhs, eq.rhs, eq.reason.clone());
            if self.sent_equality_replays.insert(replay.clone()) {
                self.sent_equality_replay_log.push(replay);
            }
        }
        self.sent_equalities = seen_equalities;
        // #6546: Save snapshot so the next call short-circuits if nothing changed.
        self.prop_eq_snapshot = Some(current_snapshot);
        result
    }
}
