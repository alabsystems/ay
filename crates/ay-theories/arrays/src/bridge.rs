// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-theory bridge helpers for `ArraySolver`.
//!
//! Extracted from `lib.rs` to reduce crate root size.
//! Contains: `SelectResolution`, `UndecidedIndexPair`, `undecided_index_pairs`,
//! external equality/disequality injection, `notify_equality`, and
//! `set_defer_expensive_checks`.

use super::*;

/// A pair of array index terms whose equality/disequality is undecided.
///
/// Result of relaxed store chain resolution for equality propagation (#5086).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SelectResolution {
    /// Resolved to a concrete value via ROW1 or const-array.
    Value(TermId),
    /// Reached a base array (not a store) — `select(base, index)` is the result.
    Base(TermId),
    /// Could not resolve (unknown index relationships or iteration limit).
    Unresolved,
}

/// When the array solver encounters `select(store(a, i, v), j)` and
/// cannot determine whether `i = j` or `i ≠ j`, it reports this pair
/// so the combined solver can consult arithmetic theories (#4665).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UndecidedIndexPair {
    /// First index (store index)
    pub idx1: TermId,
    /// Second index (select index)
    pub idx2: TermId,
    /// For READ-CONGRUENCE pairs on STORE-CARRYING problems: the two select
    /// terms `select(a, idx1)` / `select(a, idx2)` whose results witness the
    /// pair. The consumer only acts on such a pair when the arithmetic model
    /// assigns the two selects DISTINCT values (read congruence then genuinely
    /// forces `idx1 != idx2`); pairs whose select values coincide or are
    /// unknown are dropped, which keeps the split-loop atom count bounded on
    /// store-heavy unsat families (the pointer-safe-5 livelock guard).
    /// `None` for store-chain pairs and for store-free read-congruence pairs
    /// (both keep their pre-existing unconditional routing).
    pub sels: Option<(TermId, TermId)>,
}

impl ArraySolver<'_> {
    /// Return index pairs from `select(store(a, i, v), j)` patterns where
    /// neither `i = j` nor `i ≠ j` is known to this solver.
    ///
    /// The combined solver (e.g., AufLiaSolver) uses these to query LIA
    /// for arithmetic-derived disequalities and propagate them back (#4665).
    pub fn undecided_index_pairs(&mut self) -> Vec<UndecidedIndexPair> {
        self.populate_caches();
        let mut pairs = Vec::new();
        let mut seen = HashSet::default();

        for &(array, index) in self.select_cache.values() {
            // Walk through store chains looking for undecided index pairs.
            // Limit must accommodate the longest store chain in the formula
            // (storecomm benchmarks have 60+ stores) (#5086).
            let mut current = array;
            let mut iterations = 0;
            const MAX_ITERATIONS: usize = 200;

            loop {
                iterations += 1;
                if iterations > MAX_ITERATIONS {
                    break;
                }

                if let Some(&(base, store_idx, _)) = self.store_cache.get(&current) {
                    if !self.known_equal(index, store_idx) && !self.known_distinct(index, store_idx)
                    {
                        let key = if index.0 <= store_idx.0 {
                            (index, store_idx)
                        } else {
                            (store_idx, index)
                        };
                        if seen.insert(key) {
                            pairs.push(UndecidedIndexPair {
                                idx1: store_idx,
                                idx2: index,
                                sels: None,
                            });
                        }
                    }
                    current = base;
                    continue;
                }

                // Also check through equality-linked store terms
                if let Some(neighbors) = self.eq_adj.get(&current) {
                    let mut found_store = false;
                    for &(other, _) in neighbors {
                        if let Some(&(base, store_idx, _)) = self.store_cache.get(&other) {
                            if !self.known_equal(index, store_idx)
                                && !self.known_distinct(index, store_idx)
                            {
                                let key = if index.0 <= store_idx.0 {
                                    (index, store_idx)
                                } else {
                                    (store_idx, index)
                                };
                                if seen.insert(key) {
                                    pairs.push(UndecidedIndexPair {
                                        idx1: store_idx,
                                        idx2: index,
                                        sels: None,
                                    });
                                }
                            }
                            current = base;
                            found_store = true;
                            break;
                        }
                    }
                    if !found_store {
                        break;
                    }
                } else {
                    break;
                }
            }
        }

        // Read-congruence pairs (arrays wrong-model bug, QF_ALIA seed-1212
        // cases 202/262): two selects over the SAME array equivalence class
        // whose RESULTS are known distinct and whose index equality is
        // undecided. Read congruence (`i = j => select(a,i) = select(a,j)`)
        // then REQUIRES `i != j`, but nothing above reports the pair — the
        // store-chain walk only covers select-vs-STORE indices, so a FREE
        // array with plain selects (no stores at all) produced no pair, and
        // arithmetic was free to assign both indices the same value (the
        // trivial all-zero model) while EUF kept the select results apart:
        // `(distinct -3 (select arr1 z) (select arr1 x))` shipped `sat` with
        // `z = x = 0`. Reporting the pair here routes it through
        // `propagate_array_index_info`'s value-aware path: distinct arithmetic
        // values become a reason-carrying external disequality (no search
        // impact), and only value-coincident pairs fall through to a model
        // equality split.
        //
        // SCOPE (QF_ALIA seed-1213 case 187): STORE-FREE problems report every
        // read-congruence pair unconditionally (`sels: None`, the original
        // #seed-1212 routing). STORE-CARRYING problems also report the pairs —
        // the store-chain walk above only covers select-vs-STORE indices, so a
        // plain `(< (select a x) (select a (+ y -1)))` in a formula that
        // happens to contain stores ELSEWHERE was invisible and shipped a
        // wrong model (`x = 0, y = 1`: both reads hit index 0) — but each pair
        // carries its two select terms (`sels: Some(..)`) so the consumer
        // (`propagate_array_index_info`) only acts when the arithmetic model
        // gives the two selects DISTINCT values. Unconditional O(selects^2)
        // pairs on store-carrying problems multiply the split-loop atom count
        // ~3-4x on the unsat QF_ALIA family (pointer-safe-5: 53 -> 154+ model
        // eqs, 344 -> 1999+ round trips, converged 7.8s -> livelock); the
        // select-value filter keeps only pairs that witness a GENUINE read-
        // congruence violation of the current model, which each round must
        // repair anyway. Residual gaps (selects the arithmetic solver has no
        // value for) are fail-closed by the independent model gate, which now
        // checks the PRINTED array witness (see independent_gate.rs
        // `array_from_printed_witness`).
        let store_carrying = !self.store_cache.is_empty();
        let mut by_array: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
        for (&select_term, &(array, index)) in &self.select_cache {
            let rep = self.equiv_class_representative(array);
            by_array.entry(rep).or_default().push((index, select_term));
        }
        let mut groups: Vec<(TermId, Vec<(TermId, TermId)>)> = by_array.into_iter().collect();
        groups.sort_unstable_by_key(|(rep, _)| rep.0);
        for (_rep, mut members) in groups {
            if members.len() < 2 {
                continue;
            }
            // Store-carrying problems: bound the per-class pair generation.
            // The wrong-model class this exists for (free-array reads whose
            // index terms alias arithmetically, seed-1213/187) lives in SMALL
            // formulas; the big unsat families (pointer-safe-5: 50+ reads per
            // array, pp-dmem2, read2) pay O(reads^2) `known_distinct` path
            // searches EVERY round for pairs their split loop cannot use
            // productively (measured: pointer-safe-5 16.7s -> 42s+ unknown,
            // pp-dmem2 2.2s -> timeout). Beyond the bound, skip the class —
            // any residual read-congruence violation is fail-closed to
            // `unknown` by the independent gate's printed-witness check.
            const READ_CONGRUENCE_CLASS_BOUND: usize = 16;
            if store_carrying && members.len() > READ_CONGRUENCE_CLASS_BOUND {
                continue;
            }
            members.sort_unstable_by_key(|&(idx, sel)| (idx.0, sel.0));
            for i in 0..members.len() {
                for j in (i + 1)..members.len() {
                    let (idx1, sel1) = members[i];
                    let (idx2, sel2) = members[j];
                    if idx1 == idx2 || sel1 == sel2 {
                        continue;
                    }
                    if self.terms.sort(idx1) != self.terms.sort(idx2) {
                        continue;
                    }
                    // Pairs whose results are already MERGED are consistent
                    // under any index arrangement. Everything else needs one:
                    // result distinctness is often ARITHMETIC (e.g.
                    // `(select a x) < 0` vs `(select a (+ x y)) = 0` — the
                    // seed-1212 case-262 witness), which EUF `known_distinct`
                    // cannot see, so requiring known-distinct results here
                    // would silently skip exactly the wrong-model class.
                    if self.known_equal(sel1, sel2) {
                        continue;
                    }
                    if self.known_equal(idx1, idx2) || self.known_distinct(idx1, idx2) {
                        continue;
                    }
                    let key = if idx1.0 <= idx2.0 {
                        (idx1, idx2)
                    } else {
                        (idx2, idx1)
                    };
                    if seen.insert(key) {
                        pairs.push(UndecidedIndexPair {
                            idx1: key.0,
                            idx2: key.1,
                            sels: store_carrying.then_some((sel1, sel2)),
                        });
                    }
                }
            }
        }

        pairs
    }

    /// Inject an external disequality `t1 ≠ t2` learned from another theory.
    ///
    /// This is used by the combined solver when LIA determines that two
    /// array indices are distinct (e.g., from `y = x + 1`). The disequality
    /// is persisted across `rebuild_assign_indices()` calls (#4665).
    ///
    /// Returns `true` if the disequality was new (not already known).
    pub fn assert_external_disequality(&mut self, t1: TermId, t2: TermId) -> bool {
        let key = Self::ordered_pair(t1, t2);
        let is_new = self.external_diseqs.insert(key);
        self.diseq_set.insert(key);
        if is_new {
            self.bump_propagate_state_version();
        }
        is_new
    }

    /// Inject a reason-carrying external disequality `t1 ≠ t2` (#6546).
    ///
    /// Unlike `assert_external_disequality`, this stores the `TheoryLit` reasons
    /// from the arithmetic solver's tight bounds. `explain_distinct_if_provable()`
    /// can then use these reasons to justify ROW2 store-chain skips and conflict
    /// clauses, which is required for lazy ROW on AUFLIA paths.
    ///
    /// Returns `true` if the disequality was new (not already known).
    pub fn assert_external_disequality_with_reasons(
        &mut self,
        t1: TermId,
        t2: TermId,
        mut reasons: Vec<TheoryLit>,
    ) -> bool {
        if self.explain_equal_if_provable(t1, t2).is_some() {
            return false;
        }

        let key = Self::ordered_pair(t1, t2);
        reasons.sort_by_key(|lit| (lit.term.0, lit.value));
        reasons.dedup_by_key(|lit| (lit.term, lit.value));
        if reasons.iter().any(|lit| {
            lit.value
                && self
                    .equality_cache
                    .get(&lit.term)
                    .is_some_and(|&(lhs, rhs)| Self::ordered_pair(lhs, rhs) == key)
        }) {
            return false;
        }

        let is_new = self.external_diseqs.insert(key);
        self.diseq_set.insert(key);
        let reasons_changed = if reasons.is_empty() {
            false
        } else {
            let stored = self.external_diseq_reasons.entry(key).or_default();
            let old_len = stored.len();
            stored.extend_from_slice(&reasons);
            stored.sort_by_key(|lit| (lit.term.0, lit.value));
            stored.dedup_by_key(|lit| (lit.term, lit.value));
            stored.len() != old_len
        };
        if is_new || reasons_changed {
            self.bump_propagate_state_version();
            self.wake_blocked_row2_down_axioms();
            self.prop_eq_snapshot = None;
            self.final_check_snapshot = None;
        }
        is_new
    }

    /// Check if a model equality for this index pair was already requested
    /// by `propagate_array_index_info` (#6546 Packet 4).
    ///
    /// Used to prevent the N-O fixpoint from re-requesting the same
    /// unresolved pairs when the LIA trivial model assigns all indices
    /// to the same value.
    pub fn model_equality_already_requested(&self, t1: TermId, t2: TermId) -> bool {
        let key = Self::ordered_pair(t1, t2);
        self.requested_model_eqs.contains(&key)
    }

    /// Mark a model equality for this index pair as requested (#6546 Packet 4).
    pub fn mark_model_equality_requested(&mut self, t1: TermId, t2: TermId) {
        let key = Self::ordered_pair(t1, t2);
        self.requested_model_eqs.insert(key);
    }

    pub(crate) fn rollback_unreturned_model_equality_requests(
        &mut self,
        requests: &[ModelEqualityRequest],
    ) {
        for request in requests {
            let key = Self::ordered_pair(request.lhs, request.rhs);
            self.requested_model_eqs.remove(&key);
            self.exact_select_model_eq_obligations
                .retain(|obligation| obligation.request != key);
            self.exact_select_model_eq_keys
                .retain(|obligation_key| obligation_key.request != key);
        }
    }

    pub(crate) fn exact_select_model_eq_request(
        &mut self,
        mut obligation: ExactSelectModelEqObligation,
        lhs: TermId,
        rhs: TermId,
        mut reason: Vec<TheoryLit>,
    ) -> Option<ModelEqualityRequest> {
        let request_key = Self::ordered_pair(lhs, rhs);
        if self.requested_model_eqs.contains(&request_key) {
            return None;
        }
        obligation.request = request_key;
        obligation
            .reasons
            .sort_by_key(|lit| (lit.term.0, lit.value));
        obligation.reasons.dedup_by_key(|lit| (lit.term, lit.value));
        let obligation_key = obligation.stable_key();
        if self.exact_select_model_eq_keys.contains(&obligation_key)
            || self.exact_select_model_eq_obligations.contains(&obligation)
        {
            // The identical reason-carrying obligation was already emitted in
            // this array solver instance.
            return None;
        }
        self.exact_select_model_eq_keys.insert(obligation_key);
        self.exact_select_model_eq_obligations.insert(obligation);
        self.requested_model_eqs.insert(request_key);

        reason.sort_by_key(|lit| (lit.term.0, lit.value));
        reason.dedup_by_key(|lit| (lit.term, lit.value));
        Some(ModelEqualityRequest {
            lhs,
            rhs,
            reason,
            implied: false,
        })
    }

    fn record_external_equality(&mut self, t1: TermId, t2: TermId, reasons: &[TheoryLit]) {
        let key = Self::ordered_pair(t1, t2);

        // Persist so it survives rebuild_assign_indices() calls.
        let edge_is_new = !self
            .external_eqs
            .iter()
            .any(|&(lhs, rhs)| Self::ordered_pair(lhs, rhs) == key);
        if edge_is_new {
            self.external_eqs.push((t1, t2));
        }

        let mut reasons_changed = false;
        if !reasons.is_empty() {
            let mut reasons = reasons.to_vec();
            reasons.sort_by_key(|lit| (lit.term.0, lit.value));
            reasons.dedup_by_key(|lit| (lit.term, lit.value));
            let stored = self.external_eq_reasons.entry(key).or_default();
            let old_len = stored.len();
            stored.extend_from_slice(&reasons);
            stored.sort_by_key(|lit| (lit.term.0, lit.value));
            stored.dedup_by_key(|lit| (lit.term, lit.value));
            reasons_changed = stored.len() != old_len;
        }

        if edge_is_new {
            // ROW2 dirty-entry scan: a sentinel eq-graph edge appears at
            // (t1, t2) — wake entries whose views consult either endpoint.
            self.row2_wake_edge_term(t1);
            self.row2_wake_edge_term(t2);
            let sentinel = TermId::SENTINEL;
            self.eq_adj.entry(t1).or_default().push((t2, sentinel));
            self.eq_adj.entry(t2).or_default().push((t1, sentinel));
            // M1 shadow union-find: mirror the sentinel edge insertion.
            self.shadow_uf.union(
                t1,
                t2,
                union_find::EqJustification::External {
                    key,
                    has_reasons: self.external_eq_reasons.contains_key(&key),
                },
            );
            self.note_eq_graph_changed();
        } else if reasons_changed {
            self.bump_propagate_state_version();
            self.prop_eq_snapshot = None;
            self.final_check_snapshot = None;
        }
    }

    /// Inject an external equality `t1 = t2` learned from another theory.
    ///
    /// This is used by the combined solver when LIA or EUF determines that
    /// two array-relevant terms are equal. The equality is added to the
    /// internal adjacency list so that `known_equal()` returns true (#4665).
    pub fn assert_external_equality(&mut self, t1: TermId, t2: TermId) {
        self.record_external_equality(t1, t2, &[]);
    }

    /// Inject a reason-carrying external equality `t1 = t2`.
    ///
    /// The equality is represented as a sentinel edge in the equality graph, but
    /// the supplied SAT-visible reasons are preserved so store-chain conflict
    /// lemmas can guard any reasoning that traverses the edge.
    pub fn assert_external_equality_with_reasons(
        &mut self,
        t1: TermId,
        t2: TermId,
        reasons: &[TheoryLit],
    ) {
        self.record_external_equality(t1, t2, reasons);
    }

    /// Notify the array solver that two terms have become equal.
    ///
    /// If both terms have associated `ArrayVarData`, cross-products their
    /// stores × selects and queues ROW2 axioms into `pending_axioms` (with
    /// fingerprint dedup). This is AY's equivalent of Z3's `merge_eh` →
    /// `add_parent_select` / `add_store` pipeline (#6546 Approach B).
    ///
    /// The queued axioms are returned as `NeedLemmas` from the next `check()`.
    pub fn notify_equality(&mut self, a: TermId, b: TermId) {
        // Ensure term caches are populated so array_vars are current.
        self.populate_caches();

        if a == b {
            return;
        }

        self.queue_array_equality_events(a, b);
        self.record_array_var_merge(a, b);
    }

    /// Re-derive the event work implied by one active array equality without
    /// recording or applying another `array_vars` merge.
    ///
    /// Structural term registration can happen after `notify_equality()`. The
    /// incremental cache layer replays this half for the existing merge log so
    /// newly registered selects/stores receive the same cross-equality work as
    /// structure that existed at notification time.
    pub(crate) fn queue_array_equality_events(&mut self, a: TermId, b: TermId) {
        let a_data = self.array_vars.get(&a).cloned();
        let b_data = self.array_vars.get(&b).cloned();

        // Cross-product: stores from a × selects from b, and vice versa.
        // Enqueue both ROW2 down axioms and ROW1 candidates (#6546 event-driven).
        // ROW1 is queued on stores_as_result × parent_selects only (not
        // parent_stores), because ROW1 requires the select to read from the
        // store result, not from the store's base array.
        if let (Some(ref ad), Some(ref bd)) = (&a_data, &b_data) {
            for &store in &ad.stores_as_result {
                for &select in &bd.parent_selects {
                    self.queue_row2_down_axiom(store, select);
                    self.pending_row1.push((select, store));
                }
            }
            for &store in &bd.stores_as_result {
                for &select in &ad.parent_selects {
                    self.queue_row2_down_axiom(store, select);
                    self.pending_row1.push((select, store));
                }
            }
            // Also cross parent_stores (upward direction): stores whose base
            // is a × selects from b, and vice versa. ROW2 only — NOT ROW1.
            // parent_stores are stores whose BASE is this array. The select reads
            // from the base, not from the store result.
            for &store in &ad.parent_stores {
                for &select in &bd.parent_selects {
                    self.queue_row2_down_axiom(store, select);
                    // ROW2 upward: select on base, store on base (#6820).
                    self.pending_row2_upward.push((select, store));
                }
            }
            for &store in &bd.parent_stores {
                for &select in &ad.parent_selects {
                    self.queue_row2_down_axiom(store, select);
                    // ROW2 upward: select on base, store on base (#6820).
                    self.pending_row2_upward.push((select, store));
                }
            }
        }

        // Event-driven const-array reads: if a or b is a const-array,
        // selects on the other now see it through the equality.
        if self.const_array_cache.contains_key(&a) {
            if let Some(ref bd) = b_data {
                for &select in &bd.parent_selects {
                    self.pending_const_reads.push((select, a));
                }
            }
        }
        if self.const_array_cache.contains_key(&b) {
            if let Some(ref ad) = a_data {
                for &select in &ad.parent_selects {
                    self.pending_const_reads.push((select, b));
                }
            }
        }

        // Event-driven select-map axioms (#8533): if a or b is a map[f](...)
        // term, selects on the other now may need select-map axiom instantiation.
        if self.map_cache.contains_key(&a) {
            if let Some(ref bd) = b_data {
                for &select in &bd.parent_selects {
                    self.pending_select_map.push((select, a));
                }
            }
        }
        if self.map_cache.contains_key(&b) {
            if let Some(ref ad) = a_data {
                for &select in &ad.parent_selects {
                    self.pending_select_map.push((select, b));
                }
            }
        }

        // Event-driven select-as-array axioms (#8598): if a or b is an
        // as-array[f] term, selects on the other now may need the
        // select(as-array[f], i) = f(i) axiom instantiation.
        if self.as_array_cache.contains_key(&a) {
            if let Some(ref bd) = b_data {
                for &select in &bd.parent_selects {
                    self.pending_select_as_array.push((select, a));
                }
            }
        }
        if self.as_array_cache.contains_key(&b) {
            if let Some(ref ad) = a_data {
                for &select in &ad.parent_selects {
                    self.pending_select_as_array.push((select, b));
                }
            }
        }

        // Event-driven default-const axioms (#8598): when a and b merge,
        // check if either's equivalence class contains a const-array, and if
        // the other's class contains an array with a default term. Must check
        // equivalence classes (not just a/b directly) because the transitive
        // chain a =_E b =_E const-array(v) may only be complete after this merge.
        if !self.default_cache.is_empty() && !self.const_array_cache.is_empty() {
            let a_class = self.equiv_class_shared(a);
            let b_class = self.equiv_class_shared(b);

            // Find const-arrays in a's class, default terms in b's class
            for &a_member in a_class.iter() {
                if self.const_array_cache.contains_key(&a_member) {
                    for &b_member in b_class.iter() {
                        if let Some(&default_term) = self.default_cache.get(&b_member) {
                            self.pending_default_const.push((default_term, a_member));
                        }
                    }
                }
            }
            // Find const-arrays in b's class, default terms in a's class
            for &b_member in b_class.iter() {
                if self.const_array_cache.contains_key(&b_member) {
                    for &a_member in a_class.iter() {
                        if let Some(&default_term) = self.default_cache.get(&a_member) {
                            self.pending_default_const.push((default_term, b_member));
                        }
                    }
                }
            }
        }

        // Event-driven store chain resolution (#6820 Step 4): when arrays
        // merge, selects from one class may now resolve through stores from
        // the other.
        if let (Some(ref ad), Some(ref bd)) = (&a_data, &b_data) {
            // Selects from b can now resolve through a's store chains
            for &select in &bd.parent_selects {
                if !ad.stores_as_result.is_empty()
                    || self.store_cache.contains_key(&a)
                    || ad
                        .parent_stores
                        .iter()
                        .any(|s| self.store_cache.contains_key(s))
                {
                    self.pending_store_chain.push(select);
                }
            }
            // Selects from a can now resolve through b's store chains
            for &select in &ad.parent_selects {
                if !bd.stores_as_result.is_empty()
                    || self.store_cache.contains_key(&b)
                    || bd
                        .parent_stores
                        .iter()
                        .any(|s| self.store_cache.contains_key(s))
                {
                    self.pending_store_chain.push(select);
                }
            }
            // Conflicting stores: stores from a's equiv class × stores from b's equiv class
            for &store_a in &ad.stores_as_result {
                for &store_b in &bd.stores_as_result {
                    if store_a != store_b {
                        self.pending_conflicting_stores
                            .push(Self::ordered_pair(store_a, store_b));
                    }
                }
            }
        }
    }

    /// Record and apply the append-only `array_vars` merge for an active array
    /// equality. Array-sorted sources are logged even before they acquire
    /// structural data: later term growth must be able to replay the equality
    /// when a select or store first makes that source visible to the theory.
    fn record_array_var_merge(&mut self, a: TermId, b: TermId) {
        debug_assert_eq!(
            self.terms.sort(a),
            self.terms.sort(b),
            "arrays: equality merge endpoints must have the same sort"
        );
        if !matches!(self.terms.sort(a), Sort::Array(_))
            || !matches!(self.terms.sort(b), Sort::Array(_))
        {
            return;
        }
        self.array_var_merge_log.push((a, b));
        self.apply_array_var_merge(a, b);
    }

    /// Enable deferred expensive checks mode (#6282 Packet 2).
    ///
    /// When enabled, `check()` skips O(n²) checks (ROW2 upward, ROW2 extended,
    /// nested select conflicts). The combined solver must call `final_check()`
    /// after the N-O fixpoint converges to run these deferred checks.
    pub fn set_defer_expensive_checks(&mut self, defer: bool) {
        self.defer_expensive_checks = defer;
    }

    /// Export the `requested_interface_eqs` dedup set for persistence across
    /// theory instances in the non-persistent eager arm (#8594).
    ///
    /// In the non-persistent eager split loop, a fresh `ArraySolver` is created
    /// each iteration. Without persisting this set, `check_interface_equalities()`
    /// re-requests the same array pairs every iteration, exhausting the model
    /// equality round budget without making progress.
    pub fn export_requested_interface_eqs(&self) -> HashSet<(TermId, TermId)> {
        self.requested_interface_eqs.clone()
    }

    /// Import previously persisted `requested_interface_eqs` into this
    /// fresh theory instance (#8594).
    pub fn import_requested_interface_eqs(&mut self, eqs: &HashSet<(TermId, TermId)>) {
        self.requested_interface_eqs.extend(eqs.iter().copied());
    }

    /// Export the `requested_model_eqs` dedup set for persistence across
    /// theory instances in the non-persistent eager arm (#8594).
    ///
    /// Same rationale as `export_requested_interface_eqs`: prevents repeated
    /// NeedModelEquality requests for the same index pairs.
    pub fn export_requested_model_eqs(&self) -> HashSet<(TermId, TermId)> {
        self.requested_model_eqs.clone()
    }

    /// Import previously persisted `requested_model_eqs` into this
    /// fresh theory instance (#8594).
    pub fn import_requested_model_eqs(&mut self, eqs: &HashSet<(TermId, TermId)>) {
        self.requested_model_eqs.extend(eqs.iter().copied());
    }

    /// Export exact-select obligation keys for persistence across solver instances.
    pub fn export_exact_select_model_eq_keys(&self) -> HashSet<ExactSelectModelEqKey> {
        self.exact_select_model_eq_keys.clone()
    }

    /// Import exact-select obligation keys into a fresh solver instance.
    pub fn import_exact_select_model_eq_keys(&mut self, keys: &HashSet<ExactSelectModelEqKey>) {
        self.exact_select_model_eq_keys.extend(keys.iter().copied());
    }

    /// Export reason-carrying equality propagations already sent to EUF.
    pub fn export_sent_equality_replays(&self) -> HashSet<ArrayPropagatedEqualityReplay> {
        self.sent_equality_replays.clone()
    }

    /// Append-only discovery-order log of the sent-replay set
    /// (#no-replay-quadratic): the combined solver exports exact deltas via a
    /// cursor into this log instead of cloning/rescanning the whole set every
    /// Nelson-Oppen iteration.
    pub fn sent_equality_replay_log(&self) -> &[ArrayPropagatedEqualityReplay] {
        &self.sent_equality_replay_log
    }

    /// Import reason-carrying equality propagations into a fresh solver.
    pub fn import_sent_equality_replays(
        &mut self,
        replays: &HashSet<ArrayPropagatedEqualityReplay>,
    ) {
        for replay in replays {
            self.sent_equalities.insert(replay.key());
            if self.sent_equality_replays.insert(replay.clone()) {
                self.sent_equality_replay_log.push(replay.clone());
            }
        }
        self.prop_eq_snapshot = None;
    }
}
