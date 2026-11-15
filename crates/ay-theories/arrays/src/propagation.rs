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

mod cross_chain;
use cross_chain::CrossChainInput;

/// Process-wide counters for `propagate_equalities_impl` (`--stats-full`
/// `arrays_prop_eq_*`). Process-wide rather than per-instance because the
/// combined lanes construct a fresh `ArraySolver` per split-loop round and
/// the statistics block reports the LAST instance only (2026-09-17 trap);
/// these accumulate across every instance so they measure the solve.
pub(crate) mod prop_eq_stats {
    // The statics are named after the `--stats-full` keys they print.
    #![allow(non_upper_case_globals)]
    use std::sync::atomic::{AtomicU64, Ordering};

    macro_rules! counters {
        ($($name:ident),* $(,)?) => {
            $(pub(crate) static $name: AtomicU64 = AtomicU64::new(0);)*
            pub(crate) fn snapshot() -> Vec<(&'static str, u64)> {
                vec![$((concat!("arrays_prop_eq_", stringify!($name)), $name.load(Ordering::Relaxed)),)*]
            }
        };
    }

    counters!(
        calls,
        interrupted,
        snapshot_hits,
        scans,
        selects_scanned,
        sent_seed_size,
        discovered,
        suppressed_known,
        suppressed_dup,
        distinct_uncached,
        equal_uncached,
        paths_bfs,
        resolve_base_uncached,
        seed_empty,
        first_scan,
        delta_eq_adj,
        delta_select_cache,
        delta_store_cache,
        delta_external_diseqs,
        delta_external_eqs,
        delta_diseq_set,
        delta_only_external_diseqs,
        cross_chain_eq_pairs,
        cross_chain_indices,
        store_perm_chain_maps,
        store_perm_pairs,
        ns_store_perm_collect,
        ns_cross_chain_candidates,
        cross_chain_visits,
        ns_effective_store_collect,
        ns_select_scan,
        ns_store_chain,
        ns_array_congruence,
        ns_read_congruence,
        ns_transitive,
        ns_injectivity,
        ns_effective_store,
        ns_cross_chain,
        ns_store_perm,
        ns_total,
        disc_select_scan,
        disc_store_chain,
        disc_array_congruence,
        disc_read_congruence,
        disc_transitive,
        disc_injectivity,
        disc_effective_store,
        disc_cross_chain,
        disc_store_perm,
    );

    #[inline]
    pub(crate) fn add(counter: &AtomicU64, n: u64) {
        counter.fetch_add(n, Ordering::Relaxed);
    }
}

struct StorePermutationForest {
    parent: Vec<usize>,
}

impl StorePermutationForest {
    fn new(len: usize) -> Self {
        // Every node starts as its own root. The reservation is a capacity
        // hint only: if it fails, the pushes grow the vector as they go.
        let mut parent = Vec::new();
        let _ = parent.try_reserve_exact(len);
        for idx in 0..len {
            parent.push(idx);
        }
        Self { parent }
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
            prop_eq_stats::add(&prop_eq_stats::suppressed_dup, 1);
            false
        }
    }

    fn equality_already_discovered(
        seen_equalities: &HashSet<(TermId, TermId)>,
        lhs: TermId,
        rhs: TermId,
    ) -> bool {
        // Not counted: this is the hottest call in the function (523 M
        // lookups per 60 s on s3_srvr.06 before the pair filters), and an
        // atomic per call would cost more than the lookup.
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

    /// Consume the per-scan representative slot of `idx_l`'s equality class
    /// for a select pair whose indices are `known_equal`, returning whether the
    /// caller may emit the pair.
    ///
    /// The #8785 "one representative select equality per (array pair, index
    /// class)" bound is sound because EUF derives every other pair of the class
    /// from the representative by congruence over the index equalities it
    /// already holds. That argument names the FIRST pair the scan meets, sent
    /// or not: an already-sent pair therefore consumes the slot exactly as a
    /// freshly pushed one does. Skipping already-sent pairs without marking
    /// the class made `propagate_equalities` non-idempotent — every re-scan
    /// of an unchanged assignment elected one more representative per class,
    /// so the N-O loop's drain and the Sat-time convergence re-drain answered
    /// differently on the same state whenever the `prop_eq_snapshot` cache
    /// was invalidated in between (always-on `AX fixpoint violation` abort on
    /// QF_AUFLIA `swap_invalid_t1_pp_sf_ai_00010_002`, 2026-09-21).
    ///
    /// Returns `true` when the indices are not class-equal (affine or other
    /// provable equalities keep their own propagation) or when this is the
    /// first pair of the class; `false` when the class slot is already taken.
    fn note_index_class_covered(
        &self,
        propagated_index_classes: &mut HashSet<TermId>,
        idx_l: TermId,
        idx_r: TermId,
    ) -> bool {
        if !self.known_equal(idx_l, idx_r) {
            return true;
        }
        propagated_index_classes.insert(self.equiv_class_representative(idx_l))
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
        prop_eq_stats::add(&prop_eq_stats::calls, 1);
        if self.is_interrupted() {
            prop_eq_stats::add(&prop_eq_stats::interrupted, 1);
            return EqualityPropagationResult::default();
        }
        let prop_eq_t0 = std::time::Instant::now();

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
            prop_eq_stats::add(&prop_eq_stats::snapshot_hits, 1);
            prop_eq_stats::add(
                &prop_eq_stats::ns_total,
                prop_eq_t0.elapsed().as_nanos() as u64,
            );
            return EqualityPropagationResult::default();
        }
        prop_eq_stats::add(&prop_eq_stats::scans, 1);
        prop_eq_stats::add(
            &prop_eq_stats::selects_scanned,
            self.select_cache.len() as u64,
        );
        prop_eq_stats::add(
            &prop_eq_stats::sent_seed_size,
            self.sent_equalities.len() as u64,
        );
        if self.sent_equalities.is_empty() {
            prop_eq_stats::add(&prop_eq_stats::seed_empty, 1);
        }
        if self.prop_eq_snapshot.is_none() {
            prop_eq_stats::add(&prop_eq_stats::first_scan, 1);
        }
        match self.prop_eq_last_scan_snapshot {
            None => {}
            Some(prev) => {
                let cur = current_snapshot;
                if prev.0 != cur.0 {
                    prop_eq_stats::add(&prop_eq_stats::delta_eq_adj, 1);
                }
                let grow = |a: usize, b: usize| b.saturating_sub(a) as u64;
                prop_eq_stats::add(&prop_eq_stats::delta_select_cache, grow(prev.1, cur.1));
                prop_eq_stats::add(&prop_eq_stats::delta_store_cache, grow(prev.2, cur.2));
                prop_eq_stats::add(&prop_eq_stats::delta_external_diseqs, grow(prev.3, cur.3));
                prop_eq_stats::add(&prop_eq_stats::delta_external_eqs, grow(prev.4, cur.4));
                prop_eq_stats::add(&prop_eq_stats::delta_diseq_set, grow(prev.5, cur.5));
                if prev.0 == cur.0
                    && prev.1 == cur.1
                    && prev.2 == cur.2
                    && prev.3 != cur.3
                    && prev.4 == cur.4
                    && prev.5 == cur.5
                {
                    prop_eq_stats::add(&prop_eq_stats::delta_only_external_diseqs, 1);
                }
            }
        }
        // Enable `equality_reason_paths_from` memoization for the duration of the
        // (read-only w.r.t. the equality graph / assigns / external facts) select
        // scan below (#no-cross-flood). The RAII guard restores the prior cache
        // state on EVERY exit path — including the mid-loop interrupt returns and
        // panics — so the cache is never observed from a context where the inputs
        // may have changed.
        let _eq_paths_cache_guard = eq_paths_cache::activate();

        let mut result = EqualityPropagationResult::default();
        let mut prop_eq_section = std::time::Instant::now();
        let mut prop_eq_section_disc = 0usize;
        macro_rules! section_done {
            ($counter:ident, $disc:ident) => {
                prop_eq_stats::add(
                    &prop_eq_stats::$counter,
                    prop_eq_section.elapsed().as_nanos() as u64,
                );
                prop_eq_stats::add(
                    &prop_eq_stats::$disc,
                    (result.equalities.len() - prop_eq_section_disc) as u64,
                );
                prop_eq_section_disc = result.equalities.len();
                prop_eq_section = std::time::Instant::now();
            };
        }
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
                } else {
                    prop_eq_stats::add(&prop_eq_stats::suppressed_known, 1);
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

        section_done!(ns_select_scan, disc_select_scan);
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
        section_done!(ns_store_chain, disc_store_chain);

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
                            // A pair sent on an earlier scan is STILL the
                            // class representative: consume the slot exactly
                            // as pushing it would (see
                            // `note_index_class_covered`), or every re-scan
                            // of an unchanged state elects one more
                            // representative per class and the drain never
                            // reaches a fixpoint.
                            self.note_index_class_covered(
                                &mut propagated_index_classes,
                                idx_l,
                                idx_r,
                            );
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
                        if !self.note_index_class_covered(
                            &mut propagated_index_classes,
                            idx_l,
                            idx_r,
                        ) {
                            continue;
                        }
                        reasons.extend(idx_reasons);
                        push_equality!(array_congruence, sel_l, sel_r, reasons);
                    }
                }
            }
        }
        section_done!(ns_array_congruence, disc_array_congruence);
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
                    // One representative per index equality class (same
                    // reasoning as the #8785 dedup above). The slot is
                    // consumed BEFORE the already-sent test: a pair sent on an
                    // earlier scan is the representative this scan would have
                    // elected, and skipping it without marking the class made
                    // every re-scan of an unchanged state elect one more
                    // representative per class (the AX fixpoint-violation
                    // abort on the PDPAR'05 swap family; see
                    // `note_index_class_covered`).
                    if !propagated_index_classes.insert(self.equiv_class_representative(idx_l)) {
                        continue;
                    }
                    if Self::equality_already_discovered(&seen_equalities, sel_l, sel_r) {
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
        section_done!(ns_read_congruence, disc_read_congruence);

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
                                    // Already-sent pairs keep their class
                                    // slot (see `note_index_class_covered`).
                                    self.note_index_class_covered(
                                        &mut propagated_index_classes,
                                        idx_a,
                                        idx_o,
                                    );
                                    continue;
                                }
                                let Some(mut reasons) = proven_equal_reasons(arr, other_arr) else {
                                    continue;
                                };
                                let Some(idx_reasons) = proven_equal_reasons(idx_a, idx_o) else {
                                    continue;
                                };
                                if !self.note_index_class_covered(
                                    &mut propagated_index_classes,
                                    idx_a,
                                    idx_o,
                                ) {
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
        section_done!(ns_transitive, disc_transitive);

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
        section_done!(ns_injectivity, disc_injectivity);

        // Effective store map decomposition (#5086).
        //
        // Two passes: gather the effective maps of every true array equality
        // first (memoized per array for the window, so the store-permutation
        // section below re-uses them), partition every index term that
        // occurs with `index_conflict_partition` — the standing sound
        // over-approximation of `explain_equal_if_provable`, every provably
        // equal pair shares a block — and then pair only entries whose index
        // blocks agree: a pair with different blocks could never pass the
        // `proven_equal_reasons(idx_a, idx_b)` gate below. Pairs are visited
        // in the original (lhs entry, rhs entry) order, so the emission is
        // byte-identical.
        type SharedChain = Rc<store_chain::StoreChainCollection>;
        let effective_collect_t0 = std::time::Instant::now();
        let mut effective_pairs: Vec<(TermId, TermId, SharedChain, SharedChain)> = Vec::new();
        for (&_eq_term, &(lhs, rhs)) in &self.equality_cache {
            if self.assigns.get(&_eq_term) != Some(&true) {
                continue;
            }
            if !matches!(self.terms.sort(lhs), Sort::Array(_)) {
                continue;
            }
            let lhs_map = self.collect_effective_stores_shared(lhs);
            let rhs_map = self.collect_effective_stores_shared(rhs);
            if let (Some(chain_a), Some(chain_b)) = (lhs_map, rhs_map) {
                effective_pairs.push((lhs, rhs, chain_a, chain_b));
            }
        }
        prop_eq_stats::add(
            &prop_eq_stats::ns_effective_store_collect,
            effective_collect_t0.elapsed().as_nanos() as u64,
        );
        let effective_index_blocks: HashMap<TermId, TermId> = {
            let mut terms: Vec<TermId> = effective_pairs
                .iter()
                .flat_map(|(_, _, chain_a, chain_b)| {
                    chain_a
                        .2
                        .iter()
                        .map(|(idx, _, _)| *idx)
                        .chain(chain_b.2.iter().map(|(idx, _, _)| *idx))
                })
                .collect();
            terms.sort_unstable_by_key(|t| t.0);
            terms.dedup();
            self.index_conflict_partition(&terms)
        };
        for (lhs, rhs, chain_a, chain_b) in &effective_pairs {
            // #8615: Check interrupt in effective store map decomposition.
            if self.is_interrupted() {
                return result;
            }
            let (lhs, rhs) = (*lhs, *rhs);
            let (map_a, map_b) = (&chain_a.2, &chain_b.2);
            for (idx_a, val_a, store_reasons_a) in map_a {
                let block_a = effective_index_blocks[idx_a];
                for (idx_b, val_b, store_reasons_b) in map_b {
                    if effective_index_blocks[idx_b] != block_a {
                        debug_assert!(
                            proven_equal_reasons(*idx_a, *idx_b).is_none(),
                            "arrays: effective-store index block filter skipped a provable pair"
                        );
                        continue;
                    }
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
        section_done!(ns_effective_store, disc_effective_store);

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

            prop_eq_stats::add(&prop_eq_stats::cross_chain_eq_pairs, eq_pairs.len() as u64);
            prop_eq_stats::add(
                &prop_eq_stats::cross_chain_indices,
                select_indices.len() as u64,
            );
            let input = CrossChainInput {
                select_indices: &select_indices,
                index_to_selects: &index_to_selects,
                eq_pairs: &eq_pairs,
            };
            let cross_chain_cand_t0 = std::time::Instant::now();
            // Use the actual per-index resolutions and the emitter's exact
            // alias predicate. The standing unfiltered oracle stays active.
            let Some(candidates) = self.cross_chain_candidates(&input) else {
                return result;
            };
            prop_eq_stats::add(
                &prop_eq_stats::ns_cross_chain_candidates,
                cross_chain_cand_t0.elapsed().as_nanos() as u64,
            );
            #[cfg(debug_assertions)]
            let (seen_before, result_before_len) =
                (seen_equalities.clone(), result.equalities.len());
            if self.cross_chain_emit(&input, Some(&candidates), &mut seen_equalities, &mut result) {
                return result;
            }
            #[cfg(debug_assertions)]
            debug_assert!(
                self.debug_cross_chain_matches_unfiltered(
                    &input,
                    &seen_before,
                    result_before_len,
                    &result
                ),
                "arrays: cross-chain candidate filter changed what is propagated"
            );
        }
        section_done!(ns_cross_chain, disc_cross_chain);

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

            /// `(array, base, plain map)` plus the shared
            /// `(base, base reasons, reasoned map)` it was cut from.
            type ReasonedStoreChainEntry = (StoreChainEntry, Rc<store_chain::StoreChainCollection>);

            let store_perm_collect_t0 = std::time::Instant::now();
            let mut chain_maps: Vec<ReasonedStoreChainEntry> = Vec::new();
            for array_term in &chain_candidates {
                if let Some(chain) = self.collect_effective_stores_shared(*array_term) {
                    let (base, _, effective_map) = &*chain;
                    if !effective_map.is_empty() {
                        let plain_effective_map = effective_map
                            .iter()
                            .map(|(idx, val, _)| (*idx, *val))
                            .collect();
                        chain_maps.push(((*array_term, *base, plain_effective_map), chain));
                    }
                }
            }

            prop_eq_stats::add(
                &prop_eq_stats::store_perm_chain_maps,
                chain_maps.len() as u64,
            );
            prop_eq_stats::add(
                &prop_eq_stats::ns_store_perm_collect,
                store_perm_collect_t0.elapsed().as_nanos() as u64,
            );
            let mut store_perm_forest = StorePermutationForest::new(chain_maps.len());

            // Group by base array and compare effective maps
            chain_maps.sort_by_key(|((_, base, _), _)| base.0);
            // Exact pre-filter for `effective_stores_match_with_reasons`: a
            // match pairs every (index, value) of one map with an (index,
            // value) of the other whose index AND value
            // `explain_equal_if_provable` proves equal. `index_conflict_partition`
            // is the standing sound over-approximation of that relation (every
            // provably-equal pair shares a block), so two maps whose sorted
            // (index block, value block) multisets differ cannot match and the
            // matcher would return `None`. Only signature-equal pairs run it.
            // Measured on QF_AUFNIA s3_srvr.06 (--z3-mode -T:10): 49.8 M pair
            // visits per 10 s, 23.5 M of them with same-length maps handed to
            // the O(m^2) reason-cloning matcher, for 1 store-permutation
            // equality.
            let store_perm_signatures: Vec<Vec<(TermId, TermId)>> = {
                let mut terms: Vec<TermId> = chain_maps
                    .iter()
                    .flat_map(|entry| (entry.0).2.iter().flat_map(|&(idx, val)| [idx, val]))
                    .collect();
                terms.sort_unstable_by_key(|t| t.0);
                terms.dedup();
                let blocks = self.index_conflict_partition(&terms);
                chain_maps
                    .iter()
                    .map(|entry| {
                        let mut sig: Vec<(TermId, TermId)> = (entry.0)
                            .2
                            .iter()
                            .map(|&(idx, val)| (blocks[&idx], blocks[&val]))
                            .collect();
                        sig.sort_unstable();
                        sig
                    })
                    .collect()
            };
            // The two pair loops below used to enumerate every pair of chain
            // maps (O(n^2), 578 k visits per call on s3_srvr.06) to do three
            // things per pair: union the forest when the pair was already
            // sent, skip it when the forest already connects it, and run the
            // matcher. Only two kinds of pair can change anything: a pair in
            // `seen_equalities` (its union), and a pair with equal signatures
            // (the only ones the matcher can accept). Every other pair is a
            // no-op, so they are never visited; the two event kinds are
            // merged per `a` in ascending `b` order, exactly the order the
            // full enumeration visited them, and the "already sent" check
            // keeps priority over the matcher as before. `seen_equalities`
            // only grows by the pair being pushed, which is never revisited,
            // so the partner index built here is the section-long truth.
            let store_perm_pos: HashMap<TermId, usize> = chain_maps
                .iter()
                .enumerate()
                .map(|(pos, entry)| ((entry.0).0, pos))
                .collect();
            let mut store_perm_partners: Vec<Vec<usize>> = vec![Vec::new(); chain_maps.len()];
            for &(x, y) in seen_equalities.iter() {
                if let (Some(&p), Some(&q)) = (store_perm_pos.get(&x), store_perm_pos.get(&y)) {
                    let (p, q) = if p < q { (p, q) } else { (q, p) };
                    if p != q {
                        store_perm_partners[p].push(q);
                    }
                }
            }
            let mut store_perm_sig_groups: HashMap<&Vec<(TermId, TermId)>, Vec<usize>> =
                HashMap::default();
            for (pos, sig) in store_perm_signatures.iter().enumerate() {
                store_perm_sig_groups.entry(sig).or_default().push(pos);
            }
            // Events for `a`: ascending `b > a` within `[a + 1, upper)`, each
            // tagged already-sent (true) or signature candidate (false); a
            // pair that is both is already-sent.
            let store_perm_events = |a: usize, upper: usize| -> Vec<(usize, bool)> {
                let mut events: Vec<(usize, bool)> = store_perm_partners[a]
                    .iter()
                    .copied()
                    .filter(|&b| b < upper)
                    .map(|b| (b, true))
                    .collect();
                for &b in &store_perm_sig_groups[&store_perm_signatures[a]] {
                    if b > a && b < upper && !store_perm_partners[a].contains(&b) {
                        events.push((b, false));
                    }
                }
                events.sort_unstable();
                events.dedup();
                events
            };

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
                    for (b, already) in store_perm_events(a, j) {
                        let base_a = (chain_maps[a].0).1;
                        let base_b = (chain_maps[b].0).1;
                        if already {
                            debug_assert!(Self::equality_already_discovered(
                                &seen_equalities,
                                (chain_maps[a].0).0,
                                (chain_maps[b].0).0,
                            ));
                            store_perm_forest.union(a, b);
                            continue;
                        }
                        if store_perm_forest.connected(a, b) {
                            continue;
                        }
                        prop_eq_stats::add(&prop_eq_stats::store_perm_pairs, 1);
                        // The partial maps only nominate the pair; the
                        // equality itself is emitted from the COMPLETE maps
                        // (`complete_store_permutation_reasons`).
                        if self
                            .effective_stores_match_with_reasons(
                                &(chain_maps[a].1).2,
                                &(chain_maps[b].1).2,
                            )
                            .is_none()
                        {
                            continue;
                        }
                        if proven_equal_reasons(base_a, base_b).is_none() {
                            continue;
                        }
                        let indices_decided = self.store_map_indices_are_decided(
                            &(chain_maps[a].1).2,
                            &(chain_maps[b].1).2,
                        );
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
                        }
                        let Some(reasons) = self.complete_store_permutation_reasons(
                            (chain_maps[a].0).0,
                            (chain_maps[b].0).0,
                        ) else {
                            continue;
                        };
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
                for (b, already) in store_perm_events(a, chain_maps.len()) {
                    let base_a = (chain_maps[a].0).1;
                    let base_b = (chain_maps[b].0).1;
                    if base_a == base_b {
                        continue;
                    }
                    if already {
                        debug_assert!(Self::equality_already_discovered(
                            &seen_equalities,
                            (chain_maps[a].0).0,
                            (chain_maps[b].0).0,
                        ));
                        store_perm_forest.union(a, b);
                        continue;
                    }
                    if store_perm_forest.connected(a, b) {
                        continue;
                    }
                    prop_eq_stats::add(&prop_eq_stats::store_perm_pairs, 1);
                    if self
                        .effective_stores_match_with_reasons(
                            &(chain_maps[a].1).2,
                            &(chain_maps[b].1).2,
                        )
                        .is_none()
                    {
                        continue;
                    }
                    if proven_equal_reasons(base_a, base_b).is_none() {
                        continue;
                    }
                    let Some(reasons) = self.complete_store_permutation_reasons(
                        (chain_maps[a].0).0,
                        (chain_maps[b].0).0,
                    ) else {
                        continue;
                    };
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

        section_done!(ns_store_perm, disc_store_perm);
        let _ = (prop_eq_section, prop_eq_section_disc);
        prop_eq_stats::add(&prop_eq_stats::discovered, result.equalities.len() as u64);
        prop_eq_stats::add(
            &prop_eq_stats::ns_total,
            prop_eq_t0.elapsed().as_nanos() as u64,
        );

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
        self.prop_eq_last_scan_snapshot = Some(current_snapshot);
        result
    }
}
