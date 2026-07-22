// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental cache registration and queue maintenance for `ArraySolver`.
//!
//! Extracted from `lib.rs` to reduce crate root size.
//! Contains: `clear_term_caches`, `row2_fingerprint_seen`, `queue_row2_down_axiom`,
//! `register_select`, `register_store`, `merge_array_var_data`, `register_term`,
//! `debug_array_var_data_matches_caches`, and `populate_caches`.

use super::*;

const FINGERPRINT_SOFT_CAP: usize = 16_384;

impl ArraySolver<'_> {
    /// Restrict cache population to terms reachable from registered atoms.
    ///
    /// Combined incremental routes can enable this to ignore dead terms that
    /// remain in the append-only `TermStore` after earlier assumption checks.
    pub fn enable_registered_atom_scope(&mut self, enabled: bool) {
        self.registered_term_scope = enabled.then(HashSet::default);
        self.dirty = true;
    }

    pub(crate) fn register_scope_atom(&mut self, atom: TermId) {
        let Some(scope) = self.registered_term_scope.as_mut() else {
            return;
        };

        let mut stack = vec![atom];
        let mut grew = false;
        while let Some(term) = stack.pop() {
            if !scope.insert(term) {
                continue;
            }
            grew = true;
            for child in self.terms.children(term) {
                stack.push(child);
            }
        }

        if grew && self.populated_terms != 0 {
            self.dirty = true;
        }
    }

    #[inline]
    pub(crate) fn term_in_scope(&self, term_id: TermId) -> bool {
        self.registered_term_scope
            .as_ref()
            .is_none_or(|scope| scope.contains(&term_id))
    }

    pub(crate) fn clear_term_caches(&mut self) {
        self.select_cache.clear();
        self.select_pair_index.clear();
        self.store_cache.clear();
        self.const_array_cache.clear();
        self.map_cache.clear();
        self.as_array_cache.clear();
        self.default_cache.clear();
        self.pending_select_map.clear();
        self.pending_select_as_array.clear();
        self.pending_default_const.clear();
        self.equality_cache.clear();
        self.term_to_equalities.clear();
        self.eq_pair_index.clear();
        self.array_vars.clear();
        self.array_var_merge_log.clear();
        self.array_var_merge_undo.clear();
        // The merge trail is emptied, but the theory scope stack (`self.scopes`)
        // is not touched by a structural rebuild. Keep the two stacks the same
        // depth so later `pop()`s stay aligned: every currently-open scope now
        // marks position 0 in the freshly-emptied log.
        self.array_var_merge_scopes = vec![0; self.scopes.len()];
        // The affine normal-form / interning memo (`affine_cache`) is a pure
        // function of the immutable `TermStore` term DAG — it carries no
        // structural-cache lengths, assignments, or lemma reasons — so a
        // structural rebuild must NOT wipe it. `TermId`s are stable and
        // append-only, so every retained entry stays byte-identical-correct;
        // dropping it here would only force redundant re-parsing/re-interning.
        // The shadow weak-equivalence graph is keyed by cache LENGTHS; a full
        // clear + repopulation could reach the same lengths with different
        // content, so drop it explicitly (M1 weak-equivalence campaign).
        *self.weak_equiv_cache.borrow_mut() = None;
        // axiom_fingerprints / row2_fingerprint_indices are NOT cleared here.
        // They track which exact `(store, select_index)` pairs have already had
        // ROW2 work queued. Since the resulting SAT clauses are permanent
        // (survive push/pop), re-queuing the same exact axiom after a dirty
        // rebuild causes infinite NeedLemmas cycling in the DPLL(T) refinement
        // loop (#6703). Cleared indirectly via reset().
        self.pending_axioms.clear();
        self.blocked_axioms.clear();
        self.blocked_axiom_term_gen = 0;
        self.pending_const_reads.clear();
        self.pending_row1.clear();
        self.pending_row2_upward.clear();
        self.pending_self_store.clear();
        self.pending_store_chain.clear();
        self.pending_conflicting_stores.clear();
        self.pending_array_eqs.clear();
        self.pending_registered_equalities.clear();
        self.var_layer_terms.clear();
        // A full structural rebuild subsumes any pending var-layer replay.
        self.var_layer_dirty = false;
        self.populated_terms = 0;
    }

    /// Reset the assignment/merge-derived array-var layer to its structural
    /// base (undoing `notify_equality` merges and event-driven queue entries),
    /// keeping every pop-invariant structural cache intact, then replay the
    /// var-layer registration for each recorded `var_layer_terms` entry.
    ///
    /// This is the M1 backtrack path: `pop()` sets `var_layer_dirty` and this
    /// runs on the next `populate_caches()`. Because `select_cache`,
    /// `store_cache`, `equality_cache`, `term_to_equalities`, `eq_pair_index`
    /// and the const/map/as-array/default caches are pure functions of the
    /// immutable `TermStore`, they are NOT touched — only `array_vars`, the
    /// `array_var_merge_log`, and the event-driven `pending_*` queues are
    /// rebuilt. The equality graph (`eq_adj`, `shadow_uf`, `diseq_set`) is
    /// rebuilt separately by `rebuild_assign_indices()` off `assign_dirty`.
    pub(crate) fn replay_var_layer(&mut self) {
        // `array_vars` and `array_var_merge_log` are NOT cleared here: they are
        // kept live across pop, with the popped scope's merges already undone by
        // truncation in `pop()`. Only the event-driven `pending_*` work queues
        // (which are wholesale-cleared on pop, per blueprint R1) are rebuilt —
        // by replaying the queue-population half of registration with
        // `structural == false`, so `array_vars` is read but not re-mutated.
        self.pending_axioms.clear();
        self.blocked_axioms.clear();
        self.blocked_axiom_term_gen = 0;
        self.pending_const_reads.clear();
        self.pending_row1.clear();
        self.pending_row2_upward.clear();
        self.pending_self_store.clear();
        self.pending_store_chain.clear();
        self.pending_conflicting_stores.clear();
        self.pending_array_eqs.clear();
        self.pending_select_map.clear();
        self.pending_select_as_array.clear();
        self.pending_default_const.clear();
        self.pending_registered_equalities.clear();

        // Re-run the var-layer half of registration in term-id order (the same
        // order the original full rebuild used), skipping all structural
        // inserts. `std::mem::take` avoids borrowing `self` across the loop;
        // the recorded terms are structural and never change on replay.
        let terms = std::mem::take(&mut self.var_layer_terms);
        for &term_id in &terms {
            self.register_term_inner(term_id, false);
        }
        self.var_layer_terms = terms;
    }

    /// Check if a ROW2 axiom has already been generated for this (store, select_index) pair.
    ///
    /// Uses exact fingerprint match first, then equivalence-aware check on indices.
    /// Also checks store terms in the same equivalence class (#6820 Step 2:
    /// root-normalize fingerprints) to avoid duplicate ROW2 axioms when two
    /// store terms are merged in the equality graph.
    pub(crate) fn row2_fingerprint_seen(&self, store: TermId, select_index: TermId) -> bool {
        if self.axiom_fingerprints.contains(&(store, select_index)) {
            return true;
        }
        // Check the store's own fingerprint index for equivalent indices.
        if self
            .row2_fingerprint_indices
            .get(&store)
            .is_some_and(|indices| {
                indices
                    .iter()
                    .copied()
                    .any(|existing_index| self.known_equal(existing_index, select_index))
            })
        {
            return true;
        }
        // Check equivalent stores (#6820): if store =_E store2 and we already
        // generated ROW2 for (store2, idx) where idx =_E select_index, skip.
        let equiv = self.equiv_class_shared(store);
        if equiv.len() > 1 {
            for &equiv_store in equiv.iter() {
                if equiv_store == store {
                    continue;
                }
                if self
                    .axiom_fingerprints
                    .contains(&(equiv_store, select_index))
                {
                    return true;
                }
                if let Some(indices) = self.row2_fingerprint_indices.get(&equiv_store) {
                    if indices
                        .iter()
                        .copied()
                        .any(|existing_index| self.known_equal(existing_index, select_index))
                    {
                        return true;
                    }
                }
            }
        }
        false
    }

    pub(crate) fn queue_row2_down_axiom(&mut self, store: TermId, select: TermId) {
        let Some(&(_, select_index)) = self.select_cache.get(&select) else {
            return;
        };
        if self.row2_fingerprint_seen(store, select_index) {
            return;
        }

        self.axiom_fingerprints.insert((store, select_index));
        self.row2_fingerprint_indices
            .entry(store)
            .or_default()
            .push(select_index);
        self.pending_axioms
            .push(PendingAxiom::Row2Down { store, select });
    }

    pub(crate) fn wake_blocked_row2_down_axioms(&mut self) {
        if self.blocked_axioms.is_empty() {
            return;
        }

        self.pending_axioms.append(&mut self.blocked_axioms);
        self.blocked_axiom_term_gen = self.populated_terms;
    }

    pub(crate) fn forget_row2_down_fingerprint(&mut self, store: TermId, select_index: TermId) {
        self.axiom_fingerprints.remove(&(store, select_index));
        if let Some(indices) = self.row2_fingerprint_indices.get_mut(&store) {
            if let Some(pos) = indices.iter().position(|&idx| idx == select_index) {
                let _ = indices.swap_remove(pos);
            }
            if indices.is_empty() {
                self.row2_fingerprint_indices.remove(&store);
            }
        }
    }

    pub(crate) fn register_select(&mut self, select_term: TermId, array: TermId, structural: bool) {
        let (stores_as_result, parent_stores) = {
            let data = self.array_vars.entry(array).or_default();
            // Structural array-var mutations (append the select, refresh
            // prop_upward) run once at first registration and are pop-invariant.
            // On a var-layer replay (structural == false) `array_vars` already
            // holds them, so only the event-queue re-derivation below runs.
            if structural {
                data.parent_selects.push(select_term);
                data.prop_upward |= !data.parent_stores.is_empty();
            }
            (data.stores_as_result.clone(), data.parent_stores.clone())
        };

        for store in &stores_as_result {
            // #8141: Lazy axiom generation — do NOT eagerly queue ROW2 down axioms
            // for all store-select pairs at registration time. For benchmarks with
            // hundreds of stores on one array (bubble_sort22, wchains400se), eager
            // cross-product creates massive pending_axioms queues that overwhelm
            // the SAT solver. Instead, mark the select as needing lazy ROW2 scanning
            // and let check_impl() generate axioms on demand.
            //
            // ROW1 is still queued eagerly: it's cheap (only fires when indices
            // match) and is needed for correctness on simple patterns.
            self.pending_row1.push((select_term, *store));
        }

        // ROW2 upward: select on base array A, stores whose base is A.
        // Queue (select, store) for event-driven check_row2_upward (#6820).
        for &store in &parent_stores {
            self.pending_row2_upward.push((select_term, store));
        }

        // Event-driven const-array reads (#6546 Step 1): if the select's
        // array is a const-array, enqueue for check_const_array_read().
        if self.const_array_cache.contains_key(&array) {
            self.pending_const_reads.push((select_term, array));
        } else if !self.const_array_cache.is_empty() {
            // #8598: Also check equality-class members. If b = const-array(v)
            // was established before select(b, i) was registered, the syntactic
            // check above misses it because `array` is `b`, not the const-array term.
            //
            // Skip the (per-select) equivalence-class BFS entirely when there is
            // NO const-array term anywhere in the problem: no class member can
            // then be in `const_array_cache`, so the loop body never fires. This
            // is byte-identical to running the scan (which would find nothing)
            // and removes an O(class-size) walk per select on const-array-free
            // benchmarks (QF_ALIA cs_lazy.i_*, 2026-07-13 profile).
            let equiv = self.get_equiv_class(array);
            for &equiv_term in &equiv {
                if equiv_term != array && self.const_array_cache.contains_key(&equiv_term) {
                    self.pending_const_reads.push((select_term, equiv_term));
                }
            }
        }

        // Event-driven select-map axioms (#8533): if the select's array
        // is a map[f](...) term, enqueue for check_select_map().
        if self.map_cache.contains_key(&array) {
            self.pending_select_map.push((select_term, array));
        } else if !self.map_cache.is_empty() {
            // #8598: Also check equality-class members. If b = map[f](a)
            // was established before select(b, i) was registered, the syntactic
            // check above misses it because `array` is `b`, not the map term.
            // Skipped when no map term exists at all (see const-array note above).
            let equiv = self.get_equiv_class(array);
            for &equiv_term in &equiv {
                if equiv_term != array && self.map_cache.contains_key(&equiv_term) {
                    self.pending_select_map.push((select_term, equiv_term));
                }
            }
        }

        // Event-driven select-as-array axioms (#8598): if the select's array
        // is an as-array[f] term, enqueue for check_select_as_array().
        if self.as_array_cache.contains_key(&array) {
            self.pending_select_as_array.push((select_term, array));
        } else if !self.as_array_cache.is_empty() {
            // #8598: Also check equality-class members. If b = as-array[f]
            // was established before select(b, i) was registered, the syntactic
            // check above misses it because `array` is `b`, not the as-array term.
            // Skipped when no as-array term exists at all (see const-array note).
            let equiv = self.get_equiv_class(array);
            for &equiv_term in &equiv {
                if equiv_term != array && self.as_array_cache.contains_key(&equiv_term) {
                    self.pending_select_as_array.push((select_term, equiv_term));
                }
            }
        }

        // Event-driven store chain resolution (#6820 Step 4): a new select
        // on a store chain is a candidate for resolve_select_through_stores.
        if self.store_cache.contains_key(&array) || !stores_as_result.is_empty() {
            self.pending_store_chain.push(select_term);
        }
    }

    pub(crate) fn register_store(
        &mut self,
        store_term: TermId,
        base_array: TermId,
        structural: bool,
    ) {
        let base_parent_selects = {
            let base_data = self.array_vars.entry(base_array).or_default();
            // Structural mutations run once; a replay only re-derives queues.
            if structural {
                base_data.parent_stores.push(store_term);
                base_data.prop_upward |= !base_data.parent_selects.is_empty();
            }
            base_data.parent_selects.clone()
        };

        let result_parent_selects = {
            let result_data = self.array_vars.entry(store_term).or_default();
            if structural {
                result_data.stores_as_result.push(store_term);
            }
            result_data.parent_selects.clone()
        };

        for &select in &result_parent_selects {
            // #8141: Lazy axiom generation — do NOT eagerly queue ROW2 down axioms.
            // See register_select() comment for rationale.
            // ROW1 is still queued eagerly for correctness.
            self.pending_row1.push((select, store_term));
        }

        // ROW2 upward: new store on base array A, existing selects on A.
        // Queue (select, store) for event-driven check_row2_upward (#6820).
        for &select in &base_parent_selects {
            self.pending_row2_upward.push((select, store_term));
        }

        // Event-driven self-store (#6820): check if any existing equality
        // involving this store term is already assigned true.
        // Uses the reverse index for O(eq_count) lookup instead of O(|equality_cache|).
        if let Some(eq_terms) = self.term_to_equalities.get(&store_term) {
            for &eq_term in eq_terms {
                if self.assigns.get(&eq_term) == Some(&true) {
                    self.pending_self_store.push((eq_term, store_term));
                }
            }
        }

        // Event-driven store chain resolution (#6820 Step 4): existing selects
        // on the result array (store_term) now have a store chain to resolve through.
        for select in &result_parent_selects {
            self.pending_store_chain.push(*select);
        }

        // Event-driven conflicting store (#6820 Step 4): if the store's result
        // (store_term) already has other stores_as_result, they are candidates for
        // conflicting store checks when they become equal.
        let result_stores = self
            .array_vars
            .get(&store_term)
            .map(|d| d.stores_as_result.clone())
            .unwrap_or_default();
        for &other_store in &result_stores {
            if other_store != store_term {
                self.pending_conflicting_stores
                    .push((store_term, other_store));
            }
        }
    }

    pub(crate) fn merge_array_var_data(
        array_vars: &mut HashMap<TermId, ArrayVarData>,
        target: TermId,
        source: TermId,
    ) {
        let Some(source_data) = array_vars.get(&source).cloned() else {
            return;
        };

        let target_data = array_vars.entry(target).or_default();
        for store in source_data.stores_as_result {
            if !target_data.stores_as_result.contains(&store) {
                target_data.stores_as_result.push(store);
            }
        }
        for select in source_data.parent_selects {
            if !target_data.parent_selects.contains(&select) {
                target_data.parent_selects.push(select);
            }
        }
        for store in source_data.parent_stores {
            if !target_data.parent_stores.contains(&store) {
                target_data.parent_stores.push(store);
            }
        }
        target_data.prop_upward =
            !target_data.parent_selects.is_empty() && !target_data.parent_stores.is_empty();
    }

    /// Register a term into the caches.
    ///
    /// When `insert_structural` is true (the normal incremental-growth path),
    /// this inserts into the pop-invariant STRUCTURAL caches (`select_cache`,
    /// `store_cache`, `equality_cache`, `term_to_equalities`, `eq_pair_index`,
    /// `const_array_cache`, `map_cache`, `as_array_cache`, `default_cache`) and
    /// records the term in `var_layer_terms` if it has array-var / event-queue
    /// effects.
    ///
    /// When `insert_structural` is false (the `replay_var_layer()` path after a
    /// `pop()`), it SKIPS every structural insert — those caches are preserved
    /// across pop — and re-runs only the assignment/merge-derived array-var and
    /// `pending_*` queue population. This is what lets a backtrack rebuild the
    /// assignment layer without wiping and rehashing the structural caches.
    pub(crate) fn register_term(&mut self, term_id: TermId) {
        self.register_term_inner(term_id, true);
    }

    /// Whether an equality `(= lhs rhs)` can produce a var-layer effect (a
    /// `pending_self_store` or `pending_array_eqs` entry). Mirrors the guard in
    /// the `"="` arm of `register_term_inner`. Structural: `store_cache`
    /// membership is pop-invariant and the sort is fixed, so this is stable
    /// across pops and can gate `var_layer_terms` membership.
    #[inline]
    pub(crate) fn equality_has_var_layer_effect(&self, lhs: TermId, rhs: TermId) -> bool {
        self.store_cache.contains_key(&lhs)
            || self.store_cache.contains_key(&rhs)
            || matches!(self.terms.sort(lhs), Sort::Array(_))
    }

    pub(crate) fn register_term_inner(&mut self, term_id: TermId, insert_structural: bool) {
        if let TermData::App(sym, args) = self.terms.get(term_id) {
            match sym.name() {
                "select" if args.len() == 2 => {
                    if insert_structural {
                        self.select_cache.insert(term_id, (args[0], args[1]));
                        let previous = self.select_pair_index.insert((args[0], args[1]), term_id);
                        debug_assert!(
                            previous.is_none() || previous == Some(term_id),
                            "arrays: duplicate exact select lookup for ({}, {})",
                            args[0],
                            args[1]
                        );
                        self.var_layer_terms.push(term_id);
                    }
                    self.register_select(term_id, args[0], insert_structural);
                }
                "store" if args.len() == 3 => {
                    if insert_structural {
                        self.store_cache
                            .insert(term_id, (args[0], args[1], args[2]));
                        self.var_layer_terms.push(term_id);
                    }
                    self.register_store(term_id, args[0], insert_structural);
                }
                "const-array" if args.len() == 1 && insert_structural => {
                    // Purely structural: no array-var / queue effect, so this
                    // term is not recorded in `var_layer_terms`.
                    self.const_array_cache.insert(term_id, args[0]);
                }
                // lambda-array terms: register as array vars for extensionality.
                // Beta reduction is handled eagerly in mk_select, so the theory
                // solver rarely sees select(lambda-array(...), i) directly.
                "lambda-array" if args.len() == 2 => {
                    if insert_structural {
                        self.var_layer_terms.push(term_id);
                    }
                    self.array_vars.entry(term_id).or_default();
                }
                // as-array[f] terms: cache for event-driven select-as-array axiom
                // generation through equality aliases (#8598).
                name if name.starts_with("as-array[") && name.ends_with(']') && args.is_empty() => {
                    if insert_structural {
                        let func_name = name[9..name.len() - 1].to_string();
                        self.as_array_cache.insert(term_id, func_name);
                        self.var_layer_terms.push(term_id);
                    }
                    // Register as an array var so it participates in
                    // extensionality and interface equality checks.
                    self.array_vars.entry(term_id).or_default();

                    // Queue select-as-array axioms for any existing selects on this term.
                    let parent_selects = self
                        .array_vars
                        .get(&term_id)
                        .map(|d| d.parent_selects.clone())
                        .unwrap_or_default();
                    for &select in &parent_selects {
                        self.pending_select_as_array.push((select, term_id));
                    }
                }
                // default(a): register for event-driven default-const axiom.
                "default" if args.len() == 1 => {
                    // Track the default term so that when a =_E const-array(v),
                    // we can fire default(a) = v (#8598).
                    if insert_structural {
                        self.default_cache.insert(args[0], term_id);
                        self.var_layer_terms.push(term_id);
                    }
                    // If the array argument is already a const-array, queue
                    // the axiom immediately.
                    if self.const_array_cache.contains_key(&args[0]) {
                        self.pending_default_const.push((term_id, args[0]));
                    }
                }
                // Detect map[f](...) terms by the "map[" prefix convention.
                name if name.starts_with("map[") && name.ends_with(']') && !args.is_empty() => {
                    if insert_structural {
                        let func_name = name[4..name.len() - 1].to_string();
                        self.map_cache.insert(term_id, (func_name, args.clone()));
                        self.var_layer_terms.push(term_id);
                    }
                    // Register the map term as an array term in array_vars
                    // so that parent_selects are tracked for select-map axiom generation.
                    self.array_vars.entry(term_id).or_default();

                    // Queue select-map axioms for any existing selects on this map term.
                    let parent_selects = self
                        .array_vars
                        .get(&term_id)
                        .map(|d| d.parent_selects.clone())
                        .unwrap_or_default();
                    for &select in &parent_selects {
                        self.pending_select_map.push((select, term_id));
                    }
                }
                "=" if args.len() == 2 => {
                    if insert_structural {
                        self.equality_cache.insert(term_id, (args[0], args[1]));
                        self.term_to_equalities
                            .entry(args[0])
                            .or_default()
                            .push(term_id);
                        self.term_to_equalities
                            .entry(args[1])
                            .or_default()
                            .push(term_id);
                        let key = Self::ordered_pair(args[0], args[1]);
                        self.eq_pair_index.insert(key, term_id);
                        // Only record this equality for var-layer REPLAY if it can
                        // actually produce a var-layer effect below — i.e. an arg
                        // is a store term or the equality is over arrays. All three
                        // conditions are structural (store_cache membership is
                        // pop-invariant; the store operand of a `=` is a subterm and
                        // thus already registered with a lower id; the sort is
                        // fixed), so the decision is stable across pops. This keeps
                        // the (typically numerous) plain scalar equalities out of
                        // the per-pop replay loop, which is the dominant array-solve
                        // cost on QF_ALIA (cs_lazy family).
                        if self.equality_has_var_layer_effect(args[0], args[1]) {
                            self.var_layer_terms.push(term_id);
                        }
                    }
                    if self.assigns.get(&term_id) == Some(&true) {
                        if self.store_cache.contains_key(&args[0]) {
                            self.pending_self_store.push((term_id, args[0]));
                        }
                        if self.store_cache.contains_key(&args[1]) {
                            self.pending_self_store.push((term_id, args[1]));
                        }
                        // Event-driven array equality (#6820 Step 4):
                        // queue when equality is already assigned at registration time.
                        if matches!(self.terms.sort(args[0]), Sort::Array(_)) {
                            self.pending_array_eqs.push((term_id, args[0], args[1]));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    #[cfg(debug_assertions)]
    pub(crate) fn debug_array_var_data_matches_caches(&self) -> bool {
        let mut expected: HashMap<TermId, ArrayVarData> = HashMap::default();

        for (&store_term, &(base_array, _, _)) in &self.store_cache {
            expected
                .entry(base_array)
                .or_default()
                .parent_stores
                .push(store_term);
            expected
                .entry(store_term)
                .or_default()
                .stores_as_result
                .push(store_term);
        }

        for (&select_term, &(array, _)) in &self.select_cache {
            expected
                .entry(array)
                .or_default()
                .parent_selects
                .push(select_term);
        }

        // map[f](...) and as-array[f] terms register as array vars
        // with empty ArrayVarData (#8533, #8534, #8598).
        for &map_term in self.map_cache.keys() {
            expected.entry(map_term).or_default();
        }
        for &aa_term in self.as_array_cache.keys() {
            expected.entry(aa_term).or_default();
        }
        // lambda-array terms are detected by their symbol in register_term.
        for idx in 0..self.terms.len() {
            let term_id = TermId(idx as u32);
            if !self.term_in_scope(term_id) {
                continue;
            }
            if let TermData::App(sym, args) = self.terms.get(term_id) {
                if sym.name() == "lambda-array" && args.len() == 2 {
                    expected.entry(term_id).or_default();
                }
            }
        }

        for data in expected.values_mut() {
            data.stores_as_result.sort_unstable_by_key(|term| term.0);
            data.parent_selects.sort_unstable_by_key(|term| term.0);
            data.parent_stores.sort_unstable_by_key(|term| term.0);
            data.prop_upward = !data.parent_selects.is_empty() && !data.parent_stores.is_empty();
        }

        for &(target, source) in &self.array_var_merge_log {
            Self::merge_array_var_data(&mut expected, target, source);
        }

        // Re-sort after merge replay (merge appends items that break sort order).
        for data in expected.values_mut() {
            data.stores_as_result.sort_unstable_by_key(|term| term.0);
            data.parent_selects.sort_unstable_by_key(|term| term.0);
            data.parent_stores.sort_unstable_by_key(|term| term.0);
        }

        let mut actual = self.array_vars.clone();
        for data in actual.values_mut() {
            data.stores_as_result.sort_unstable_by_key(|term| term.0);
            data.parent_selects.sort_unstable_by_key(|term| term.0);
            data.parent_stores.sort_unstable_by_key(|term| term.0);
        }

        expected == actual
    }

    #[cfg(not(debug_assertions))]
    pub(crate) fn debug_array_var_data_matches_caches(&self) -> bool {
        true
    }

    /// M1 reference oracle: recompute every pop-invariant STRUCTURAL cache from
    /// scratch over the term store and assert it is byte-identical to the
    /// persisted one. This proves the central M1 claim — that these caches are
    /// pure functions of the immutable, monotonic `TermStore` and may safely be
    /// retained across `pop()` rather than wiped and rebuilt. A divergence here
    /// (a structural entry wrongly kept, missing, or corrupted after a
    /// var-layer replay) is a hard soundness bug, so this fires on every
    /// mutating `populate_caches()` under `cfg(debug_assertions)`.
    #[cfg(debug_assertions)]
    pub(crate) fn debug_structural_caches_match_full_rebuild(&self) -> bool {
        let mut select_cache: HashMap<TermId, (TermId, TermId)> = HashMap::default();
        let mut select_pair_index: HashMap<(TermId, TermId), TermId> = HashMap::default();
        let mut store_cache: HashMap<TermId, (TermId, TermId, TermId)> = HashMap::default();
        let mut const_array_cache: HashMap<TermId, TermId> = HashMap::default();
        let mut map_cache: HashMap<TermId, (String, Vec<TermId>)> = HashMap::default();
        let mut as_array_cache: HashMap<TermId, String> = HashMap::default();
        let mut default_cache: HashMap<TermId, TermId> = HashMap::default();
        let mut equality_cache: HashMap<TermId, (TermId, TermId)> = HashMap::default();
        let mut term_to_equalities: HashMap<TermId, Vec<TermId>> = HashMap::default();
        let mut eq_pair_index: HashMap<(TermId, TermId), TermId> = HashMap::default();
        let mut var_layer_terms: Vec<TermId> = Vec::new();

        for idx in 0..self.populated_terms {
            let term_id = TermId(idx as u32);
            if !self.term_in_scope(term_id) {
                continue;
            }
            let TermData::App(sym, args) = self.terms.get(term_id) else {
                continue;
            };
            let name = sym.name();
            match name {
                "select" if args.len() == 2 => {
                    select_cache.insert(term_id, (args[0], args[1]));
                    select_pair_index.insert((args[0], args[1]), term_id);
                    var_layer_terms.push(term_id);
                }
                "store" if args.len() == 3 => {
                    store_cache.insert(term_id, (args[0], args[1], args[2]));
                    var_layer_terms.push(term_id);
                }
                "const-array" if args.len() == 1 => {
                    const_array_cache.insert(term_id, args[0]);
                }
                "lambda-array" if args.len() == 2 => {
                    var_layer_terms.push(term_id);
                }
                n if n.starts_with("as-array[") && n.ends_with(']') && args.is_empty() => {
                    as_array_cache.insert(term_id, n[9..n.len() - 1].to_string());
                    var_layer_terms.push(term_id);
                }
                "default" if args.len() == 1 => {
                    default_cache.insert(args[0], term_id);
                    var_layer_terms.push(term_id);
                }
                n if n.starts_with("map[") && n.ends_with(']') && !args.is_empty() => {
                    map_cache.insert(term_id, (n[4..n.len() - 1].to_string(), args.clone()));
                    var_layer_terms.push(term_id);
                }
                "=" if args.len() == 2 => {
                    equality_cache.insert(term_id, (args[0], args[1]));
                    term_to_equalities.entry(args[0]).or_default().push(term_id);
                    term_to_equalities.entry(args[1]).or_default().push(term_id);
                    eq_pair_index.insert(Self::ordered_pair(args[0], args[1]), term_id);
                    // Mirror the same var-layer-relevance filter as registration.
                    if store_cache.contains_key(&args[0])
                        || store_cache.contains_key(&args[1])
                        || matches!(self.terms.sort(args[0]), Sort::Array(_))
                    {
                        var_layer_terms.push(term_id);
                    }
                }
                _ => {}
            }
        }

        assert_eq!(self.select_cache, select_cache, "select_cache diverged");
        assert_eq!(
            self.select_pair_index, select_pair_index,
            "select_pair_index diverged"
        );
        assert_eq!(self.store_cache, store_cache, "store_cache diverged");
        assert_eq!(
            self.const_array_cache, const_array_cache,
            "const_array_cache diverged"
        );
        assert_eq!(self.map_cache, map_cache, "map_cache diverged");
        assert_eq!(
            self.as_array_cache, as_array_cache,
            "as_array_cache diverged"
        );
        assert_eq!(self.default_cache, default_cache, "default_cache diverged");
        assert_eq!(
            self.equality_cache, equality_cache,
            "equality_cache diverged"
        );
        assert_eq!(
            self.term_to_equalities, term_to_equalities,
            "term_to_equalities diverged"
        );
        assert_eq!(self.eq_pair_index, eq_pair_index, "eq_pair_index diverged");
        assert_eq!(
            self.var_layer_terms, var_layer_terms,
            "var_layer_terms diverged"
        );
        true
    }

    #[cfg(not(debug_assertions))]
    #[inline]
    pub(crate) fn debug_structural_caches_match_full_rebuild(&self) -> bool {
        true
    }

    /// Delta reference oracle for the assignment/equality layer.
    ///
    /// The warm incremental path (`update_assignment_indices_incrementally`,
    /// reachable per-assignment once `warm_assignment_indices_ready` no longer
    /// demands `populated_terms == terms.len()`) mutates `eq_adj` / `shadow_uf`
    /// / `diseq_set` in place instead of falling to a full
    /// `rebuild_assign_indices()`. This recomputes the observable equality-layer
    /// state from scratch — the disequality set, the connected components of the
    /// true-equality graph, and the sorted select-relevant equality entries —
    /// exactly as `rebuild_assign_indices()` + the `eq_select` block would, and
    /// asserts the incrementally-maintained state matches it. A divergence is a
    /// missed/spurious (dis)equality = a wrong verdict, so this fires on every
    /// `populate_caches()` that saw an incremental equality-layer mutation.
    #[cfg(debug_assertions)]
    fn debug_components(adj: &HashMap<TermId, HashSet<TermId>>) -> Vec<Vec<TermId>> {
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut comps: Vec<Vec<TermId>> = Vec::new();
        let mut verts: Vec<TermId> = adj.keys().copied().collect();
        verts.sort_unstable_by_key(|t| t.0);
        for &start in &verts {
            if seen.contains(&start) {
                continue;
            }
            let mut comp = Vec::new();
            let mut stack = vec![start];
            seen.insert(start);
            while let Some(t) = stack.pop() {
                comp.push(t);
                if let Some(ns) = adj.get(&t) {
                    for &n in ns {
                        if seen.insert(n) {
                            stack.push(n);
                        }
                    }
                }
            }
            comp.sort_unstable_by_key(|t| t.0);
            comps.push(comp);
        }
        comps.sort_unstable_by_key(|c| c[0].0);
        comps
    }

    #[cfg(debug_assertions)]
    pub(crate) fn debug_assignment_layer_matches_full_rebuild(&self) -> bool {
        // (1) diseq_set: false-assigned equality atoms + external disequalities.
        let mut ref_diseq: HashSet<(TermId, TermId)> = HashSet::default();
        for (&eq_term, &(lhs, rhs)) in &self.equality_cache {
            if self.assigns.get(&eq_term) == Some(&false) {
                ref_diseq.insert(Self::ordered_pair(lhs, rhs));
            }
        }
        for &key in &self.external_diseqs {
            ref_diseq.insert(key);
        }
        assert_eq!(
            self.diseq_set, ref_diseq,
            "arrays delta: diseq_set diverged from full rebuild"
        );

        // (2) True-equality connectivity: reference adjacency from true-assigned
        // atoms + external equalities, compared component-for-component to the
        // incrementally maintained `eq_adj`. Duplicate parallel edges and the
        // per-atom vs per-pair edge-count difference are intentionally collapsed
        // (both graphs are consulted only for connected components).
        let mut ref_adj: HashMap<TermId, HashSet<TermId>> = HashMap::default();
        for (&eq_term, &(lhs, rhs)) in &self.equality_cache {
            if self.assigns.get(&eq_term) == Some(&true) {
                ref_adj.entry(lhs).or_default().insert(rhs);
                ref_adj.entry(rhs).or_default().insert(lhs);
            }
        }
        for &(t1, t2) in &self.external_eqs {
            ref_adj.entry(t1).or_default().insert(t2);
            ref_adj.entry(t2).or_default().insert(t1);
        }
        let mut inc_adj: HashMap<TermId, HashSet<TermId>> = HashMap::default();
        for (&from, neighbors) in &self.eq_adj {
            let e = inc_adj.entry(from).or_default();
            for &(to, _) in neighbors {
                e.insert(to);
            }
        }
        assert_eq!(
            Self::debug_components(&ref_adj),
            Self::debug_components(&inc_adj),
            "arrays delta: true-equality connectivity diverged from full rebuild"
        );

        // (3) eq_select_entries_sorted: a pure function of the structural
        // equality_cache/select_cache, revalidated here for completeness.
        let select_sorts: std::collections::HashSet<&Sort> = self
            .select_cache
            .keys()
            .map(|&sel| self.terms.sort(sel))
            .collect();
        let mut ref_entries: Vec<(TermId, TermId, TermId)> = self
            .equality_cache
            .iter()
            .filter(|&(_, &(lhs, _))| select_sorts.contains(self.terms.sort(lhs)))
            .map(|(&term, &(lhs, rhs))| (term, lhs, rhs))
            .collect();
        ref_entries.sort_unstable_by_key(|&(term, _, _)| term.0);
        assert_eq!(
            self.eq_select_entries_sorted, ref_entries,
            "arrays delta: eq_select_entries_sorted diverged from full rebuild"
        );
        true
    }

    /// Populate caches by incrementally scanning new terms.
    pub(crate) fn populate_caches(&mut self) {
        let was_dirty = self.dirty;
        if self.dirty {
            self.clear_term_caches();
            self.dirty = false;
        }

        let registered_new_terms = self.populated_terms < self.terms.len();
        if registered_new_terms {
            for idx in self.populated_terms..self.terms.len() {
                let term_id = TermId(idx as u32);
                if self.term_in_scope(term_id) {
                    self.register_term(term_id);
                }
            }
            self.populated_terms = self.terms.len();
            self.apply_pending_registered_equalities();
        }

        // M1: rebuild the assignment/merge-derived array-var layer after a
        // pop() without wiping the pop-invariant structural caches. `pop()`
        // sets `var_layer_dirty` (never `dirty`); the structural caches survive
        // and only `array_vars` / the `pending_*` queues are replayed here.
        let did_replay = self.var_layer_dirty;
        if self.var_layer_dirty {
            self.replay_var_layer();
            self.var_layer_dirty = false;
        }

        // Debug reference oracle (mandatory M1 discipline, cfg(debug_assertions)
        // only): the persisted structural caches must be byte-identical to a
        // from-scratch full rebuild. This is the load-bearing safety net — a
        // structural cache wrongly kept across a pop would be a soundness bug.
        // Run whenever this call mutated the caches (full rebuild, new-term
        // registration, or a var-layer replay).
        debug_assert!(
            !(was_dirty || registered_new_terms || did_replay)
                || self.debug_structural_caches_match_full_rebuild(),
            "arrays: persisted structural caches diverged from a full rebuild"
        );

        // GC dead fingerprints after a dirty rebuild. When caches are rebuilt
        // from scratch after pop(), fingerprints referencing store terms or
        // select indices that no longer exist in the live caches are dead
        // weight. Removing them bounds fingerprint growth to O(live_stores *
        // live_indices) instead of accumulating across all historical scopes.
        // This is safe because the corresponding SAT clauses reference terms
        // that the solver no longer tracks — re-queuing cannot happen since
        // queue_row2_down_axiom() only fires for terms in store_cache/select_cache.
        if was_dirty {
            self.gc_dead_fingerprints();
        }

        // #8605: Proactive fingerprint GC when size exceeds soft cap.
        // Even without a dirty rebuild, fingerprints can grow monotonically
        // between pop() calls on array-heavy benchmarks. Running GC based
        // on size bounds growth to O(live_stores * live_indices + SOFT_CAP).
        if self.axiom_fingerprints.len() > FINGERPRINT_SOFT_CAP {
            self.gc_dead_fingerprints();
            // If still over cap after removing dead entries, the live set is
            // genuinely large. Accept it — re-queuing protection is more
            // important than memory for moderate sizes.
        }

        // Keep the sorted+filtered equality-entry vector in sync with
        // equality_cache/select_cache. Both caches are only mutated here
        // (clear_term_caches on a dirty rebuild, register_term on new
        // terms), so rebuilding on those two triggers is exhaustive. Only
        // eq atoms whose side sort has at least one select term of the same
        // sort survive — every other atom provably yields zero select views
        // in the ROW2 scan (see `eq_select_entries_sorted`). Sorted
        // ascending by eq term id — the exact order propagate_impl's
        // per-call sort used (#3060 determinism).
        if was_dirty || registered_new_terms {
            let select_sorts: std::collections::HashSet<&Sort> = self
                .select_cache
                .keys()
                .map(|&sel| self.terms.sort(sel))
                .collect();
            let mut entries: Vec<(TermId, TermId, TermId)> = self
                .equality_cache
                .iter()
                .filter(|&(_, &(lhs, _))| select_sorts.contains(self.terms.sort(lhs)))
                .map(|(&term, &(lhs, rhs))| (term, lhs, rhs))
                .collect();
            entries.sort_unstable_by_key(|&(term, _, _)| term.0);
            self.eq_select_entries_sorted = entries;
            // Any rebuild invalidates the propagate no-change fast path.
            self.bump_propagate_state_version();
            // ROW2 dirty-entry scan: entry indices changed shape and the
            // structural probe universe (eq_pair_index/select/store caches)
            // may have grown — watch state is index-based and now stale.
            self.row2_invalidate_entries();
        }

        // Debug-build cache-consistency validation. Run it only when this call
        // actually MUTATED the caches (dirty rebuild or newly registered
        // terms): `populate_caches()` is invoked on every `notify_equality()`
        // — i.e. per replayed cross-theory equality, per Nelson-Oppen
        // iteration — and the validator is O(term-store) with a full
        // merge-log replay + clone + sort. Re-validating an UNCHANGED cache
        // on each of those calls made debug-build AUFLIA solves on large term
        // stores (verification-consumer's UF-encoded Seq queries) burn their entire solve
        // deadline inside this assert (~60% of samples, 2026-07-05 profile).
        // Any divergence introduced by a later merge is still caught at the
        // next mutating call, which replays the full merge log.
        debug_assert!(
            !(was_dirty || registered_new_terms || did_replay)
                || self.debug_array_var_data_matches_caches(),
            "arrays: incremental array_vars tracking diverged from caches"
        );
        self.rebuild_assign_indices();

        // Delta soundness oracle (mandatory, cfg(debug_assertions)): whenever an
        // incremental warm-path equality-layer mutation happened since the last
        // populate — the exact surface the relaxed `warm_assignment_indices_
        // ready` opened up — recompute diseq_set / true-eq connectivity /
        // eq_select entries from scratch and assert byte-for-byte equivalence.
        // `rebuild_assign_indices()` above is self-consistent, so this only has
        // teeth when it early-returned (no `assign_dirty`) yet the layer was
        // mutated incrementally. Runs on unchanged populate (`eq_layer_touched`
        // false and non-mutating) are skipped to preserve debug-build solve
        // deadlines.
        #[cfg(debug_assertions)]
        {
            if was_dirty
                || registered_new_terms
                || did_replay
                || self.eq_layer_touched_since_populate
            {
                debug_assert!(
                    self.debug_assignment_layer_matches_full_rebuild(),
                    "arrays delta: incremental assignment layer diverged from full rebuild"
                );
            }
            self.eq_layer_touched_since_populate = false;
        }

        // Post-populate: check for alias opportunities through the equality
        // graph (#8598). At this point eq_adj is ready, so we can find
        // transitive equality chains for all three alias patterns.
        self.scan_default_const_aliases();
        self.scan_select_map_aliases();
        self.scan_select_as_array_aliases();
    }

    /// Scan for default(X) terms where X is transitively equal to a const-array
    /// through the equality graph. Queues pending_default_const pairs for any
    /// newly discovered aliases.
    ///
    /// This handles the case where `default(a)`, `a = b`, and `b = const-array(v)`
    /// are all present but `notify_equality()` was called pairwise and didn't see
    /// the transitive connection at the time.
    fn scan_default_const_aliases(&mut self) {
        if self.default_cache.is_empty() || self.const_array_cache.is_empty() {
            return;
        }

        // For each default(array_arg), check if array_arg is equal to any const-array.
        let default_entries: Vec<(TermId, TermId)> = self
            .default_cache
            .iter()
            .map(|(&arr, &def)| (arr, def))
            .collect();

        for (array_arg, default_term) in default_entries {
            // Already directly queued?
            if self.const_array_cache.contains_key(&array_arg) {
                // Already handled in register_term.
                continue;
            }

            // Check equivalence class of array_arg for const-array members.
            let equiv = self.get_equiv_class(array_arg);
            for &member in &equiv {
                if self.const_array_cache.contains_key(&member) {
                    self.pending_default_const.push((default_term, member));
                    break; // One const-array alias is enough.
                }
            }
        }
    }

    /// Scan for select(X, i) terms where X is transitively equal to a map[f](...)
    /// through the equality graph. Queues pending_select_map pairs for any
    /// newly discovered aliases.
    ///
    /// This handles the case where `select(a, i)`, `a = b`, and `b = map[f](c)`
    /// are all present but `notify_equality()` was called pairwise and didn't see
    /// the transitive connection at the time.
    fn scan_select_map_aliases(&mut self) {
        if self.select_cache.is_empty() || self.map_cache.is_empty() {
            return;
        }

        // Collect select entries to avoid borrow conflict.
        let select_entries: Vec<(TermId, TermId)> = self
            .select_cache
            .iter()
            .map(|(&sel, &(arr, _))| (sel, arr))
            .collect();

        for (select_term, array) in select_entries {
            // Already directly queued?
            if self.map_cache.contains_key(&array) {
                continue;
            }

            // Check equivalence class of array for map term members.
            let equiv = self.get_equiv_class(array);
            for &member in &equiv {
                if self.map_cache.contains_key(&member) {
                    self.pending_select_map.push((select_term, member));
                    break; // One map alias is enough.
                }
            }
        }
    }

    /// Scan for select(X, i) terms where X is transitively equal to an as-array[f]
    /// through the equality graph. Queues pending_select_as_array pairs for any
    /// newly discovered aliases.
    ///
    /// This handles the case where `select(a, i)`, `a = b`, and `b = as-array[f]`
    /// are all present but `notify_equality()` was called pairwise and didn't see
    /// the transitive connection at the time.
    fn scan_select_as_array_aliases(&mut self) {
        if self.select_cache.is_empty() || self.as_array_cache.is_empty() {
            return;
        }

        // Collect select entries to avoid borrow conflict.
        let select_entries: Vec<(TermId, TermId)> = self
            .select_cache
            .iter()
            .map(|(&sel, &(arr, _))| (sel, arr))
            .collect();

        for (select_term, array) in select_entries {
            // Already directly queued?
            if self.as_array_cache.contains_key(&array) {
                continue;
            }

            // Check equivalence class of array for as-array term members.
            let equiv = self.get_equiv_class(array);
            for &member in &equiv {
                if self.as_array_cache.contains_key(&member) {
                    self.pending_select_as_array.push((select_term, member));
                    break; // One as-array alias is enough.
                }
            }
        }
    }

    /// Remove fingerprint entries for store terms no longer in `store_cache`.
    ///
    /// After a dirty cache rebuild (triggered by `pop()`), the term caches are
    /// repopulated from the current term store. Any `(store, select_index)` pair
    /// in `axiom_fingerprints` where `store` is not in `store_cache` is dead —
    /// no ROW2 axiom can reference that store, and the fingerprint just wastes
    /// memory. Similarly, entries in `row2_fingerprint_indices` keyed by dead
    /// stores are removed.
    ///
    /// We also remove fingerprint entries where all referenced select indices
    /// are dead (no longer appear as indices in any live select). This handles
    /// the case where the store survives but the index terms were temporary.
    fn gc_dead_fingerprints(&mut self) {
        let pre_fp = self.axiom_fingerprints.len();
        let pre_idx = self.row2_fingerprint_indices.len();

        if pre_fp == 0 && pre_idx == 0 {
            return;
        }

        // Build set of live select indices for secondary GC pass.
        let live_select_indices: HashSet<TermId> =
            self.select_cache.values().map(|&(_, idx)| idx).collect();

        // GC axiom_fingerprints: remove entries where store is dead OR
        // the select_index is dead (not in any live select).
        self.axiom_fingerprints.retain(|&(store, select_index)| {
            self.store_cache.contains_key(&store) && live_select_indices.contains(&select_index)
        });

        // GC row2_fingerprint_indices: remove dead store keys entirely,
        // and for live stores, remove dead select indices.
        self.row2_fingerprint_indices.retain(|store, indices| {
            if !self.store_cache.contains_key(store) {
                return false;
            }
            indices.retain(|idx| live_select_indices.contains(idx));
            !indices.is_empty()
        });

        // Shrink allocations if GC removed significant entries.
        let removed_fp = pre_fp.saturating_sub(self.axiom_fingerprints.len());
        let removed_idx = pre_idx.saturating_sub(self.row2_fingerprint_indices.len());
        if removed_fp > 64 || removed_idx > 16 {
            self.axiom_fingerprints.shrink_to_fit();
            self.row2_fingerprint_indices.shrink_to_fit();
        }

        self.fingerprint_gc_removed += (removed_fp + removed_idx) as u64;
    }
}
