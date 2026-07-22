// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ROW1 and ROW2 axiom conflict checkers for the array theory solver.
//!
//! Implements detection of array axiom violations:
//! - ROW1 (read-over-write same index)
//! - ROW2 (read-over-write different index) — downward, upward, extended
//!
//! Store chain resolution, const-array reads, self-store, array equality,
//! and extensionality checks are in `axiom_store_checks`.

use super::*;

impl ArraySolver<'_> {
    /// Check read-over-write axiom 1 (same index):
    /// If we have select(store(a, i, v), i), it must equal v.
    /// Returns conflict if select(store(a, i, v), i) ≠ v is asserted.
    ///
    /// Event-driven (#6546 revised design): instead of scanning ALL selects
    /// and doing BFS per select (O(S × D) per check), drains only
    /// `pending_row1` pairs queued by `register_select`, `register_store`,
    /// and `notify_equality`. Most `check()` calls have 0-1 new pairs.
    ///
    /// Drain semantics: pairs where indices match but no conflict is detected
    /// yet are RETAINED for future re-checking (the disequality on values
    /// may be propagated later). Pairs with non-matching indices are
    /// discarded (handled by ROW2).
    pub(crate) fn check_row1(&mut self) -> Option<TheoryResult> {
        let mut pairs = self.pending_row1.take();
        // Sort/dedup for deterministic conflict detection and bounded replay.
        pairs.sort_unstable_by_key(|&(sel, st)| (sel.0, st.0));
        pairs.dedup();

        let mut retained = Vec::new();
        let mut iter = pairs.into_iter();
        while let Some((select_term, store_term)) = iter.next() {
            // Validate that both terms are still in caches (backtrack may
            // have removed them via a dirty rebuild).
            let Some(&(select_array, select_idx)) = self.select_cache.get(&select_term) else {
                continue;
            };
            let Some(&(_base, store_idx, store_val)) = self.store_cache.get(&store_term) else {
                continue;
            };

            // ROW1: select(store(a, i, v), j) where i = j → result = v.
            let Some(index_eq_reasons) = self.explain_equal_if_provable(select_idx, store_idx)
            else {
                // Indices not equal — not a ROW1 candidate. Discard.
                // (ROW2 handles the i ≠ j case separately.)
                continue;
            };

            // Check if select_term ≠ store_val is provably asserted (conflict).
            let Some(val_diseq_reasons) = self.explain_distinct_if_provable(select_term, store_val)
            else {
                // Indices match but no conflict yet — RETAIN for re-checking.
                // The disequality may be propagated on a future check() call.
                retained.push((select_term, store_term));
                continue;
            };

            // Conflict! select(store(a, i, v), i) ≠ v contradicts ROW1.
            let mut reasons = val_diseq_reasons;

            // Justify select_array = store_term via SAT-visible equality
            // reasons. A sentinel/model edge in this premise must not let
            // ROW1 emit a clause that SAT cannot backtrack (#8785).
            if select_array != store_term {
                let Some(array_eq_reasons) =
                    self.explain_equal_if_provable(select_array, store_term)
                else {
                    retained.push((select_term, store_term));
                    continue;
                };
                reasons.extend(array_eq_reasons);
            }
            reasons.extend(index_eq_reasons);

            // Preserve the unprocessed tail before returning so one emitted
            // lemma does not silently drop later queued ROW1 work.
            retained.extend(iter);
            self.pending_row1.replace(retained);
            return self.conflict_reasons_to_lemma(reasons);
        }

        self.pending_row1.replace(retained);
        None
    }

    pub(crate) fn row2_down_clause_terms(
        &self,
        store_term: TermId,
        select_term: TermId,
    ) -> Option<(TermId, TermId, TermId)> {
        let &(array, select_idx) = self.select_cache.get(&select_term)?;
        // #8596: Accept both syntactic identity and EUF-equivalence between
        // the select's array and the store term. When `(= a store(...))` is
        // asserted, `select(a, y)` has `array = a` which differs syntactically
        // from the store term. Without this, ROW2 axioms are never generated
        // for const-array + store patterns where the array variable is
        // indirectly equal to the store term via an asserted equality.
        if array != store_term && !self.known_equal(array, store_term) {
            return None;
        }

        let &(base_array, store_idx, _) = self.store_cache.get(&store_term)?;
        let base_select = self
            .get_exact_select_term(base_array, select_idx)
            // #8596: mk_select eagerly simplifies select(const-array(v), i) to v,
            // so the select term never exists in the term store. Use the const-array
            // default value directly as the base_select for ROW2.
            .or_else(|| self.terms.get_const_array(base_array))?;
        if base_select == select_term {
            return None;
        }
        Some((store_idx, select_idx, base_select))
    }

    /// Lazily generate ROW2 down axioms from the current term caches.
    ///
    /// #8141: Instead of eagerly queuing all store-select ROW2 axioms during
    /// `register_select()` / `register_store()`, we scan for relevant pairs
    /// lazily during `check()`. The key optimization is a **budget**: only
    /// generate up to `LAZY_ROW2_BUDGET` new axioms per check() call. The
    /// fingerprint mechanism (`axiom_fingerprints`) ensures axioms are never
    /// duplicated. Remaining pairs are discovered on subsequent check() calls
    /// or in final_check().
    ///
    /// For benchmarks with hundreds of stores on one array (bubble_sort22,
    /// wchains400se), this spreads the cost over multiple DPLL iterations
    /// instead of generating all O(stores * selects) axioms upfront.
    pub(crate) fn generate_lazy_row2_axioms(&mut self) {
        const LAZY_ROW2_BUDGET: usize = 64;
        let mut generated = 0usize;

        // Collect select terms to avoid borrowing issues.
        // Only process selects whose array has stores_as_result entries.
        let select_entries: Vec<(TermId, TermId)> = self
            .select_cache
            .iter()
            .filter_map(|(&sel, &(arr, _))| {
                self.array_vars
                    .get(&arr)
                    .filter(|d| !d.stores_as_result.is_empty())
                    .map(|_| (sel, arr))
            })
            .collect();

        for (select_term, array) in select_entries {
            if generated >= LAZY_ROW2_BUDGET {
                break;
            }
            let stores = match self.array_vars.get(&array) {
                Some(data) => data.stores_as_result.clone(),
                None => continue,
            };
            for store in stores {
                if generated >= LAZY_ROW2_BUDGET {
                    break;
                }
                // queue_row2_down_axiom checks fingerprints and only queues
                // truly new axioms. Count the axiom as "generated" only if it
                // wasn't already fingerprinted.
                let select_idx = match self.select_cache.get(&select_term) {
                    Some(&(_, idx)) => idx,
                    None => continue,
                };
                if !self.row2_fingerprint_seen(store, select_idx) {
                    self.queue_row2_down_axiom(store, select_term);
                    generated += 1;
                }
            }
        }
    }

    /// Generate ALL remaining lazy ROW2 axioms (no budget).
    ///
    /// Called from `final_check()` to ensure completeness. Unlike
    /// `generate_lazy_row2_axioms()`, this has no per-call limit.
    pub(crate) fn generate_all_lazy_row2_axioms(&mut self) {
        let select_entries: Vec<(TermId, TermId)> = self
            .select_cache
            .iter()
            .filter_map(|(&sel, &(arr, _))| {
                self.array_vars
                    .get(&arr)
                    .filter(|d| !d.stores_as_result.is_empty())
                    .map(|_| (sel, arr))
            })
            .collect();

        for (select_term, array) in select_entries {
            // #8615: Check interrupt periodically to avoid indefinite axiom
            // generation on large formulas (no budget limit in this path).
            if self.is_interrupted() {
                return;
            }
            let stores = match self.array_vars.get(&array) {
                Some(data) => data.stores_as_result.clone(),
                None => continue,
            };
            for store in stores {
                // M1 weak-equivalence invariant: the (select array, store)
                // pair lies on a length-1 weak path (array ≈ store —[i]— base).
                #[cfg(debug_assertions)]
                self.debug_assert_row2_pair_on_length1_weak_path(array, store);
                self.queue_row2_down_axiom(store, select_term);
            }
        }
    }

    /// Check read-over-write axiom 2 (different index):
    /// If i ≠ j, then select(store(a, i, v), j) = select(a, j).
    ///
    /// The array solver cannot create fresh equality terms directly, so this
    /// pass has two stages:
    /// 1. if both equality atoms already exist, emit the permanent ROW2 clause
    /// 2. otherwise, request the missing equality atoms via NeedModelEqualities
    ///
    /// Applied ROW2 clauses are remembered so later check() calls do not
    /// regenerate them after split-loop rebuilds (#6546 Packet 3).
    pub(crate) fn check_row2(&mut self) -> Option<TheoryResult> {
        let mut lemmas = Vec::new();
        let mut seen_lemmas = HashSet::default();
        let mut requests = Vec::new();
        let mut seen_requests = HashSet::default();

        // (#6820) Move blocked axioms back to pending only when new terms have
        // been created.
        if self.populated_terms > self.blocked_axiom_term_gen {
            self.pending_axioms.append(&mut self.blocked_axioms);
            self.blocked_axiom_term_gen = self.populated_terms;
        }

        // Drain completed axioms: swap out pending_axioms, process them, and
        // put back only those that still need work.
        let axioms = std::mem::take(&mut self.pending_axioms);
        let mut remaining = Vec::with_capacity(axioms.len());

        for axiom in axioms {
            match axiom {
                PendingAxiom::Row2Down { store, select } => {
                    let Some(&(select_array, select_idx)) = self.select_cache.get(&select) else {
                        remaining.push(PendingAxiom::Row2Down { store, select });
                        continue;
                    };
                    let Some(&(store_base, store_idx, store_val)) = self.store_cache.get(&store)
                    else {
                        remaining.push(PendingAxiom::Row2Down { store, select });
                        continue;
                    };

                    // ROW2 only applies to the distinct-index branch.
                    // When the current equality graph already makes the
                    // indices equal, ROW1 handles the case. Forget the exact
                    // ROW2 fingerprint so lazy generation may re-queue this
                    // structural pair later if backtracking makes the indices
                    // non-equal again.
                    if store_idx == select_idx || self.known_equal(store_idx, select_idx) {
                        self.forget_row2_down_fingerprint(store, select_idx);
                        continue;
                    }

                    let Some((store_idx, select_idx, base_select)) =
                        self.row2_down_clause_terms(store, select)
                    else {
                        // Terms not in cache yet — keep for later.
                        remaining.push(PendingAxiom::Row2Down { store, select });
                        continue;
                    };
                    let Some(alias_reasons) = (if select_array == store {
                        Some(Vec::new())
                    } else {
                        self.explain_equal_if_provable(select_array, store)
                    }) else {
                        remaining.push(PendingAxiom::Row2Down { store, select });
                        continue;
                    };

                    let idx_eq = self.get_eq_term(store_idx, select_idx);
                    let select_eq = self.get_eq_term(select, base_select);
                    if let (Some(idx_eq), Some(select_eq)) = (idx_eq, select_eq) {
                        // If either disjunct is already true under the current
                        // assignment the clause is satisfied — skip emission.
                        let idx_sat = self.assigns.get(&idx_eq) == Some(&true);
                        let sel_sat = self.assigns.get(&select_eq) == Some(&true);
                        if idx_sat || sel_sat {
                            remaining.push(PendingAxiom::Row2Down { store, select });
                            continue;
                        }

                        // Both atoms exist — build and emit the clause, then
                        // drain this axiom (don't push to remaining).
                        let mut clause: Vec<_> = alias_reasons
                            .iter()
                            .copied()
                            .map(|lit| TheoryLit::new(lit.term, !lit.value))
                            .collect();
                        clause.extend([
                            TheoryLit::new(idx_eq, true),
                            TheoryLit::new(select_eq, true),
                        ]);
                        clause.sort_by_key(|lit| (lit.term.0, lit.value));
                        clause.dedup_by_key(|lit| (lit.term, lit.value));
                        if !clause.is_empty() && seen_lemmas.insert(clause.clone()) {
                            // #lemma-must-prune / #refine-theory-memory: skip no-op lemmas.
                            if self.lemma_is_unproductive(&clause) {
                                continue;
                            }
                            lemmas.push(TheoryLemma::new(clause));
                        }
                        // Axiom completed — drained (not pushed to remaining).
                        continue;
                    }

                    // If the index disequality is already explainable but the
                    // equality atom `(= store_idx select_idx)` does not exist
                    // yet, emit the guarded ROW2 implication directly:
                    //   reasons(index != j) => select = base_select
                    //
                    // This is the inline replay case for AUFLIA: LIA can
                    // provide a SAT-visible disequality reason after ROW2-down
                    // has already blocked on the missing index equality atom.
                    if let Some(select_eq) = select_eq {
                        let sel_sat = self.assigns.get(&select_eq) == Some(&true);
                        if !sel_sat {
                            if let Some(idx_diseq_reasons) =
                                self.explain_distinct_if_provable(store_idx, select_idx)
                            {
                                let reasoned_index_diseq = !idx_diseq_reasons.is_empty();
                                let mut clause: Vec<_> = alias_reasons
                                    .iter()
                                    .copied()
                                    .map(|lit| TheoryLit::new(lit.term, !lit.value))
                                    .collect();
                                clause.extend(
                                    idx_diseq_reasons
                                        .iter()
                                        .copied()
                                        .map(|lit| TheoryLit::new(lit.term, !lit.value)),
                                );
                                clause.push(TheoryLit::new(select_eq, true));
                                clause.sort_by_key(|lit| (lit.term.0, lit.value));
                                clause.dedup_by_key(|lit| (lit.term, lit.value));
                                if !clause.is_empty() && seen_lemmas.insert(clause.clone()) {
                                    // #lemma-must-prune / #refine-theory-memory: skip no-op lemmas.
                                    if self.lemma_is_unproductive(&clause) {
                                        continue;
                                    }
                                    lemmas.push(TheoryLemma::new(clause));
                                }
                                if reasoned_index_diseq {
                                    self.forget_row2_down_fingerprint(store, select_idx);
                                }
                                continue;
                            }
                        }
                    }

                    if let (Some(mut idx_diseq_reasons), Some(mut val_diseq_reasons)) = (
                        self.explain_distinct_if_provable(store_idx, select_idx),
                        self.explain_distinct_if_provable(select, base_select),
                    ) {
                        let mut reasons = alias_reasons;
                        reasons.append(&mut idx_diseq_reasons);
                        reasons.append(&mut val_diseq_reasons);
                        reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                        reasons.dedup_by_key(|lit| (lit.term, lit.value));

                        if let Some(TheoryResult::NeedLemmas(conflict_lemmas)) =
                            self.conflict_reasons_to_lemma(reasons)
                        {
                            for lemma in conflict_lemmas {
                                if seen_lemmas.insert(lemma.clause.clone()) {
                                    lemmas.push(lemma);
                                }
                            }
                        }
                        self.forget_row2_down_fingerprint(store, select_idx);
                        continue;
                    }

                    // At least one equality atom missing — request it and move
                    // to blocked_axioms.
                    for (lhs, rhs) in [(store_idx, select_idx), (select, base_select)] {
                        if self.get_eq_term(lhs, rhs).is_some() {
                            continue;
                        }
                        let kind = if lhs == store_idx && rhs == select_idx {
                            ExactSelectModelEqKind::DownIndex
                        } else {
                            ExactSelectModelEqKind::DownSelect
                        };
                        let request_key = Self::ordered_pair(lhs, rhs);
                        if !seen_requests.insert(request_key) {
                            continue;
                        }
                        if self.model_equality_already_requested(lhs, rhs) {
                            continue;
                        }
                        let obligation = ExactSelectModelEqObligation {
                            kind,
                            request: request_key,
                            store,
                            store_base,
                            store_index: store_idx,
                            store_value: store_val,
                            select,
                            select_array,
                            select_index: select_idx,
                            value: Some(base_select),
                            reasons: alias_reasons.clone(),
                        };
                        if let Some(request) =
                            self.exact_select_model_eq_request(obligation, lhs, rhs, Vec::new())
                        {
                            requests.push(request);
                        }
                    }
                    self.blocked_axioms
                        .push(PendingAxiom::Row2Down { store, select });
                }
            }
        }

        self.pending_axioms = remaining;

        if !lemmas.is_empty() {
            return Some(TheoryResult::NeedLemmas(lemmas));
        }
        match requests.len() {
            0 => None,
            1 => Some(TheoryResult::NeedModelEquality(
                requests.pop().expect("invariant: len checked above"),
            )),
            _ => Some(TheoryResult::NeedModelEqualities(requests)),
        }
    }

    /// Axiom 2b: Upward ROW2 conflict detection through store chains.
    ///
    /// Standard ROW2 (check_row2) checks *downward*: given select(store(A,i,v), j),
    /// it derives select(store(A,i,v), j) = select(A, j) when i != j.
    ///
    /// Upward ROW2 checks the reverse direction: given select(A, j) where A is
    /// the *base* array of some store(A, i, v) = B, it derives:
    ///   i != j → select(A, j) = select(B, j)
    ///
    /// Reference: Z3 `instantiate_axiom2b`, `set_prop_upward`, `add_parent_store`.
    #[cfg(test)]
    pub(crate) fn check_row2_upward(&self) -> Option<TheoryResult> {
        let mut selects: Vec<_> = self.select_cache.iter().collect();
        selects.sort_by_key(|(&term, _)| term.0);

        for (&select_on_base, &(base_array, select_idx)) in &selects {
            let Some(data) = self.array_vars.get(&base_array) else {
                continue;
            };
            if !data.prop_upward || data.parent_stores.is_empty() {
                continue;
            }

            for &store_term in &data.parent_stores {
                let Some(&(store_base, store_idx, _)) = self.store_cache.get(&store_term) else {
                    continue;
                };
                let Some(base_reasons) = self.explain_equal_if_provable(base_array, store_base)
                else {
                    continue;
                };
                let Some(idx_diseq_reasons) =
                    self.explain_distinct_if_provable(select_idx, store_idx)
                else {
                    continue;
                };

                if let Some((select_on_store, mut select_alias_reasons)) =
                    self.get_exact_select_term_on_provable_array_alias(store_term, select_idx)
                {
                    if let Some(val_diseq_reasons) =
                        self.explain_distinct_if_provable(select_on_base, select_on_store)
                    {
                        let mut reasons = base_reasons;
                        reasons.append(&mut select_alias_reasons);
                        reasons.extend(idx_diseq_reasons);
                        reasons.extend(val_diseq_reasons);
                        reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                        reasons.dedup_by_key(|lit| (lit.term, lit.value));

                        if reasons.is_empty() {
                            return None;
                        }
                        return Some(TheoryResult::Unsat(reasons));
                    }
                }
            }
        }

        None
    }

    /// Check ROW2 upward and emit `NeedModelEquality` for undecided index pairs.
    pub(crate) fn check_row2_upward_with_guidance(&mut self) -> Option<TheoryResult> {
        self.check_row2_upward_with_guidance_impl(false)
    }

    /// Final-check ROW2-upward guidance limited to conflict-ready shapes.
    pub(crate) fn check_row2_upward_conflict_ready_guidance(&mut self) -> Option<TheoryResult> {
        self.check_row2_upward_with_guidance_impl(true)
    }

    fn check_row2_upward_with_guidance_impl(
        &mut self,
        require_value_diseq: bool,
    ) -> Option<TheoryResult> {
        let pairs = self.pending_row2_upward.take();
        let mut pending_requests = Vec::new();

        for (select_on_base, store_term) in pairs {
            let Some(&(select_array, select_idx)) = self.select_cache.get(&select_on_base) else {
                continue;
            };
            let Some(&(store_base, store_idx, store_val)) = self.store_cache.get(&store_term)
            else {
                continue;
            };
            let Some(base_reasons) = self.explain_equal_if_provable(select_array, store_base)
            else {
                continue;
            };
            if select_idx == store_idx {
                continue;
            }

            if self.known_equal(select_idx, store_idx) {
                continue; // ROW1 handles this
            }

            if let Some(idx_diseq_reasons) =
                self.explain_distinct_if_provable(select_idx, store_idx)
            {
                if let Some((select_on_store, mut select_alias_reasons)) =
                    self.get_exact_select_term_on_provable_array_alias(store_term, select_idx)
                {
                    if let Some(val_diseq_reasons) =
                        self.explain_distinct_if_provable(select_on_base, select_on_store)
                    {
                        let mut reasons = base_reasons;
                        reasons.append(&mut select_alias_reasons);
                        reasons.extend(idx_diseq_reasons);
                        reasons.extend(val_diseq_reasons);
                        reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                        reasons.dedup_by_key(|lit| (lit.term, lit.value));
                        if reasons.is_empty() {
                            return None;
                        }
                        return self.conflict_reasons_to_lemma(reasons);
                    }
                }
            } else {
                let store_select =
                    self.get_exact_select_term_on_provable_array_alias(store_term, select_idx);
                if require_value_diseq && store_select.is_none() {
                    continue;
                }
                let mut reason = base_reasons.clone();
                let mut value = self.get_exact_select_term(store_term, select_idx);
                if let Some((select_on_store, mut select_alias_reasons)) = store_select {
                    if require_value_diseq {
                        let Some(val_diseq_reasons) =
                            self.explain_distinct_if_provable(select_on_base, select_on_store)
                        else {
                            continue;
                        };
                        reason.extend(val_diseq_reasons);
                    }
                    reason.append(&mut select_alias_reasons);
                    value = Some(select_on_store);
                }
                let key = if store_idx.0 <= select_idx.0 {
                    (store_idx, select_idx)
                } else {
                    (select_idx, store_idx)
                };
                if self.requested_model_eqs.contains(&key) {
                    continue;
                }
                reason.sort_by_key(|lit| (lit.term.0, lit.value));
                reason.dedup_by_key(|lit| (lit.term, lit.value));
                let obligation = ExactSelectModelEqObligation {
                    kind: ExactSelectModelEqKind::UpwardIndex,
                    request: key,
                    store: store_term,
                    store_base,
                    store_index: store_idx,
                    store_value: store_val,
                    select: select_on_base,
                    select_array,
                    select_index: select_idx,
                    value,
                    reasons: reason.clone(),
                };
                if let Some(request) =
                    self.exact_select_model_eq_request(obligation, store_idx, select_idx, reason)
                {
                    pending_requests.push(request);
                }
            }
        }

        match pending_requests.len() {
            0 => None,
            1 => Some(TheoryResult::NeedModelEquality(
                pending_requests
                    .pop()
                    .expect("invariant: len checked above"),
            )),
            _ => Some(TheoryResult::NeedModelEqualities(pending_requests)),
        }
    }

    /// Check ROW2 conflicts via store chain following.
    pub(crate) fn check_row2_extended(&self) -> Option<TheoryResult> {
        let lemmas = self.row2_extended_conflict_lemmas();
        if lemmas.is_empty() {
            None
        } else {
            Some(TheoryResult::NeedLemmas(lemmas))
        }
    }

    fn row2_extended_conflict_lemmas(&self) -> Vec<TheoryLemma> {
        struct Row2ExtendedSelectState {
            select_term: TermId,
            index: TermId,
            resolution: SelectResolution,
            reasons: Vec<TheoryLit>,
        }

        let candidate_pairs = self.select_conflict_candidate_pairs();
        let mut lemmas = Vec::new();
        let mut seen_clauses = HashSet::default();

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
            .filter_map(|&select_term| {
                let &(array, index) = self.select_cache.get(&select_term)?;
                let (resolution, reasons) =
                    self.resolve_select_base_for_propagation_with_reasons(array, index);
                Some((
                    select_term,
                    Row2ExtendedSelectState {
                        select_term,
                        index,
                        resolution,
                        reasons,
                    },
                ))
            })
            .collect();

        for &(sel1_term, sel2_term) in candidate_pairs.iter() {
            let Some(sel1) = select_terms.get(&sel1_term) else {
                continue;
            };
            let Some(sel2) = select_terms.get(&sel2_term) else {
                continue;
            };

            if !self.known_equal(sel1.index, sel2.index) {
                continue;
            }

            let Some(sel_diseq_reasons) =
                self.explain_distinct_if_provable(sel1.select_term, sel2.select_term)
            else {
                continue;
            };

            let mut reasons = sel_diseq_reasons;
            reasons.extend(sel1.reasons.iter().copied());
            reasons.extend(sel2.reasons.iter().copied());
            if sel1.index != sel2.index {
                let Some(eq_reasons) = self.explain_equal_if_provable(sel1.index, sel2.index)
                else {
                    continue;
                };
                reasons.extend(eq_reasons);
            }

            match (sel1.resolution, sel2.resolution) {
                (SelectResolution::Base(base1), SelectResolution::Base(base2)) => {
                    let Some(base_reasons) = self.explain_equal_if_provable(base1, base2) else {
                        continue;
                    };
                    reasons.extend(base_reasons);
                }
                (SelectResolution::Value(value1), SelectResolution::Value(value2)) => {
                    let Some(value_reasons) = self.explain_equal_if_provable(value1, value2) else {
                        continue;
                    };
                    reasons.extend(value_reasons);
                }
                _ => continue,
            }

            reasons.sort_by_key(|lit| (lit.term.0, lit.value));
            reasons.dedup_by_key(|lit| (lit.term, lit.value));

            if reasons.is_empty() {
                continue;
            }
            let mut clause: Vec<TheoryLit> = reasons
                .into_iter()
                .map(|lit| TheoryLit::new(lit.term, !lit.value))
                .collect();
            clause.sort_by_key(|lit| (lit.term.0, lit.value));
            clause.dedup_by_key(|lit| (lit.term, lit.value));
            if clause.is_empty() || !seen_clauses.insert(clause.clone()) {
                continue;
            }
            // #lemma-must-prune / #refine-theory-memory: skip no-op lemmas.
            if self.lemma_is_unproductive(&clause) {
                continue;
            }
            lemmas.push(TheoryLemma::new(clause));
        }
        lemmas
    }
}
